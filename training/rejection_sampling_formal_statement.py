import argparse
import json
import math
import os
import subprocess

import requests
from transformers import AutoTokenizer

from utils.prompt_utils import extract_math_final_answer, last_boxed_only_string


def load_subgoal_proof(subgoal_dir):
    subgoal_proof = {}
    for file in os.listdir(subgoal_dir):
        with open(os.path.join(subgoal_dir, file), encoding="utf-8") as f:
            json_obj = json.loads(f.read().strip())
            subgoal_proof[json_obj["id"]] = json_obj
    return subgoal_proof

class InformalToFormalMinif2fPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert isinstance(self.num_samples, int)
        self.model_index = kwargs.get("model_index", None)
        assert isinstance(self.model_index, int)
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.batch_size = 8
        self.max_sequence_len = 8192
        self.max_response_len = max_response_len
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")
        self.filename_extension = "jsonl"

        subgoal_dir = kwargs.get("subgoal_dir", None)
        current_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(current_dir)
        self.dataset = self.load_data(subgoal_dir=subgoal_dir, repo_root=repo_root)
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx

    def load_data(self, subgoal_dir, repo_root):
        subgoal_proof_dict = load_subgoal_proof(subgoal_dir)

        math_path = f"{repo_root}/datasets/compose/math_aime_imo_threshold0_1.jsonl"

        dataset = []
        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                if json_obj["source"] == "math":
                    final_answer = extract_math_final_answer(json_obj["answer"])
                    informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                    string_to_replace = last_boxed_only_string(json_obj["answer"])
                    if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                        informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                    else:
                        informal_proof = json_obj["answer"]
                else:
                    informal_statement = json_obj['question']
                    informal_proof = json_obj["answer"]
                pid = json_obj["id"]
                if ("[asy]" in informal_statement and "[/asy]" in informal_statement) or ("[asy]" in informal_proof and "[/asy]" in informal_proof):
                    continue
                assert pid in subgoal_proof_dict

                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "subgoal_proof": subgoal_proof_dict[pid]["subgoal_proof"],
                    "id": pid,
                })
        return dataset

    def num_tokens_from_string(self, string: str) -> int:
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<|end_of_text|>']
    
    def get_prompt(self, idx):
        data_idx = idx // self.num_samples
        informal_statement = self.dataset[data_idx]["informal_statement"]
        prompt = f"Translate the informal statement into a formal statement by defining variables and assumptions explicitly, and then stating the main claim clearly using precise mathematical notation.\n\n### Informal Statement\n{informal_statement}\n\n### Formal Statement"
        return prompt

    def get_num_prompts(self):
        return len(self.dataset) * self.num_samples
    
    def get_data_idx(self, task_id): # "train-xxx-xxx" (num_samples > 1) or "train-xxx" (num_samples==1)
        assert len(task_id.split("-")) == 3 or len(task_id.split("-")) == 2
        return self.id_to_idx["-".join(task_id.split("-")[:2])]
    
    def get_sample_idx(self, task_id):
        if len(task_id.split("-")) == 3:
            return int(task_id.split("-")[2])
        elif len(task_id.split("-")) == 2:
            return 0
        else:
            raise ValueError

    def get_id_from_task_name(self, task_name):
        return "-".join(task_name.split("-")[:2])

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [file_name.split(".")[0] for file_name in file_names if file_name.endswith(self.filename_extension)]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        sorted_unfinished = sorted(unfinished, key=lambda x: (self.get_data_idx(x), self.get_sample_idx(x)))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory):
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers):
        if self.are_all_workers_finished(directory):
            return [self.get_num_prompts()]
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        if tasks_per_worker == 0:
            return [self.get_num_prompts()]
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task_id = unfinished[i]
            start_index = self.get_data_idx(task_id) * self.num_samples + self.get_sample_idx(task_id)
            start_indices.append(start_index)
        
        print(f"Number of unfinished tasks: {len(unfinished)}")
        print(f"Tasks per worker: {tasks_per_worker}")
        print(f"Actual number of workers: {len(start_indices)}")
        return start_indices

    def get_task_name(self, idx):
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"{self.dataset[data_idx]['id']}-{sample_idx}"
        else:
            return f"{self.dataset[data_idx]['id']}"
    
    def get_data_from_task_name(self, task_name):
        data_idx = self.get_data_idx(task_name)
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

def write_to_file(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "id": task_id,
            "informal_statement": informal_statement,
            "informal_proof": informal_proof,
            "subgoal_proof": subgoal_proof,
            "formal_statement": formal_statement,
        }) + "\n")

def save_results(batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement):
    for dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement in zip(
        batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement):
        write_to_file(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=10000)
    parser.add_argument("--endpoint_address", type=str, default="")
    parser.add_argument("--prompt_manager_name", type=str, default="InformalToFormalPromptManager")
    parser.add_argument("--max_response_len", type=int, default=1024)
    parser.add_argument("--dump_path", type=str, default="")
    parser.add_argument("--model_index", type=int, default=0)
    parser.add_argument("--num_samples", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=0.4)
    parser.add_argument("--subgoal_dir", type=str, required=True)
    args = parser.parse_args()

    if args.prompt_manager_name == "InformalToFormalMinif2fPromptManager":
        prompt_manager = InformalToFormalMinif2fPromptManager(max_response_len=args.max_response_len, model_index=args.model_index, num_samples=args.num_samples, temperature=args.temperature, subgoal_dir=args.subgoal_dir)
    else:
        raise ValueError


    batched_path = []
    batched_id = []
    batched_informal_statement = []
    batched_informal_proof = []
    batched_subgoal_proof = []
    batched_prompt = []
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path):
            continue
        
        task_id = prompt_manager.get_data_from_index(idx)["id"]
        informal_statement = prompt_manager.get_data_from_index(idx)["informal_statement"]
        informal_proof = prompt_manager.get_data_from_index(idx)["informal_proof"]
        subgoal_proof = prompt_manager.get_data_from_index(idx)["subgoal_proof"]

        prompt = prompt_manager.get_prompt(idx)
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                subgoal_proof=subgoal_proof,
                formal_statement=None,
            )
            continue
        
        batched_path.append(dump_file_path)
        batched_id.append(task_id)
        batched_informal_statement.append(informal_statement)
        batched_informal_proof.append(informal_proof)
        batched_subgoal_proof.append(subgoal_proof)
        batched_prompt.append(prompt)
        if len(batched_prompt) == prompt_manager.batch_size:
            max_batch_length = max([prompt_manager.num_tokens_from_string(p) for p in batched_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_prompt,
                "do_sample": True,
                'temperature': prompt_manager.temperature,
                "max_tokens": min(prompt_manager.max_response_len, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_formal_statement = responses.json()["choices"][0]["text"]
            save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement)

            batched_path = []
            batched_id = []
            batched_informal_statement = []
            batched_informal_proof = []
            batched_subgoal_proof = []
            batched_prompt = []
    if len(batched_prompt) > 0:
        max_batch_length = max([prompt_manager.num_tokens_from_string(p) for p in batched_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_prompt,
            "do_sample": True,
            'temperature': prompt_manager.temperature,
            "max_tokens": min(prompt_manager.max_response_len, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_formal_statement = responses.json()["choices"][0]["text"]
        save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement)
