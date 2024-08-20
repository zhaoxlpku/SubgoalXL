import argparse
import glob
import json
import math
import os
import re
from collections import defaultdict

import requests
from transformers import AutoTokenizer


def count_jsonl_files(directory):
    """
    Counts the number of files ending with '.jsonl' in the specified directory.
    Only returns the base filenames.

    :param directory: Path to the directory to search for '.jsonl' files.
    :return: Number of '.jsonl' files in the directory and a list of their base filenames.
    """
    if not os.path.isdir(directory):
        raise ValueError(f"The path {directory} is not a valid directory.")
    
    jsonl_files = glob.glob(os.path.join(directory, '*.jsonl'))
    base_filenames = [os.path.basename(file) for file in jsonl_files]
    return len(base_filenames), base_filenames

def construct_nested_list(directory):
    files = os.listdir(directory)
    pattern_with_yyy = re.compile(r'compose-(\d+)-(\d+)\.jsonl')
    pattern_without_yyy = re.compile(r'compose-(\d+)\.jsonl')

    # Create a dictionary to store filenames based on xxx and yyy values
    files_dict = defaultdict(lambda: defaultdict(list))
    single_files = defaultdict(list)

    for file in files:
        match_with_yyy = pattern_with_yyy.match(file)
        match_without_yyy = pattern_without_yyy.match(file)
        
        if match_with_yyy:
            xxx, yyy = match_with_yyy.groups()
            files_dict[int(xxx)][int(yyy)].append(file)
        elif match_without_yyy:
            xxx = match_without_yyy.group(1)
            single_files[int(xxx)].append(file)

    # Construct the list based on the sorted xxx and yyy values
    result = []
    for xxx in sorted(set(files_dict.keys()).union(single_files.keys())):
        if xxx in files_dict:
            sublist = []
            for yyy in sorted(files_dict[xxx].keys()):
                sublist.extend(files_dict[xxx][yyy])
            result.append(sublist)
        elif xxx in single_files:
            result.append(single_files[xxx])

    return result

class InformalToFormalMinif2fPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.model_index = kwargs.get("model_index", None)
        assert isinstance(self.model_index, int)
        self.num_models = kwargs.get("num_models", None)
        assert self.num_models in [4]

        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.data_dir = kwargs.get("data_dir", None)
        assert isinstance(self.data_dir, str)

        self.batch_size = 8
        self.max_sequence_len = 8192 
        self.max_response_len = max_response_len 
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")
        self.filename_extension = "jsonl" 

        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx
        
    def load_data(self):
        nested_list = construct_nested_list(self.data_dir)

        dataset = []
        for sublist in nested_list:
            pid = None
            informal_statement = None
            informal_proof = None
            subgoal_proof = None
            formal_statement = []
            for i, file in enumerate(sublist):
                if i % self.num_models != self.model_index:
                    continue

                with open(os.path.join(self.data_dir, file), encoding="utf-8") as f:
                    json_obj = json.loads(f.read().strip())
                    if pid is None:
                        pid = json_obj["id"]
                        informal_statement = json_obj["informal_statement"]
                        informal_proof = json_obj["informal_proof"]
                        subgoal_proof = json_obj["subgoal_proof"]
                    else:
                        assert pid == json_obj["id"]
                        assert informal_statement == json_obj["informal_statement"]
                        assert informal_proof == json_obj["informal_proof"]
                        assert subgoal_proof == json_obj["subgoal_proof"]
                    formal_statement.append(json_obj["formal_statement"])

            dataset.append({
                "informal_statement": informal_statement,
                "informal_proof": informal_proof,
                "subgoal_proof": subgoal_proof,
                "formal_statement": formal_statement,
                "id": pid,
            })
        return dataset

    def num_tokens_from_string(self, string: str) -> int: 
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<|end_of_text|>']
    
    def get_prompt(self, idx): 
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        data_idx = idx // num_samples_total
        sample_idx = idx % num_samples_total

        formal_statement = self.dataset[data_idx]["formal_statement"][sample_idx // self.num_models]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        subgoal_proof = self.dataset[data_idx]["subgoal_proof"]
        prompt = f"### Problem:\n{informal_statement}\n\n### Proof:\n{formal_statement}"
        prompt = f"{prompt} (*{subgoal_proof}*)\n" # TODO: check
        return prompt

    def get_num_prompts(self): 
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        return len(self.dataset) *  num_samples_total
    
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
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        if num_samples_total > 1:
            return [f"{data['id']}-{i * self.num_models + self.model_index}" for data in self.dataset for i in range(len(data["formal_statement"]))]
        else:
            return [data['id'] for data in self.dataset]

    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [file_name.split(".")[0] for file_name in file_names if file_name.endswith(self.filename_extension)]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        sorted_unfinished = sorted(unfinished, key=lambda x: (self.get_data_idx(x), self.get_sample_idx(x)))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): 
        _, file_names = count_jsonl_files(directory)
        task_names = [file_name.split(".")[0] for file_name in file_names if file_name.endswith(self.filename_extension)]

        num_samples = len(self.dataset[0]["formal_statement"])
        sample_indices = [i for i in range(self.model_index, 99999, self.num_models)][:num_samples]
        task_names = [task_name for task_name in task_names if self.get_sample_idx(task_name) in sample_indices]
        if len(task_names) == len(self.dataset) * num_samples:
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
        
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task_id = unfinished[i]
            start_index = self.get_data_idx(task_id) * num_samples_total + self.get_sample_idx(task_id)
            start_indices.append(start_index)
        
        print(f"Number of unfinished tasks: {len(unfinished)}")
        print(f"Tasks per worker: {tasks_per_worker}")
        print(f"Actual number of workers: {len(start_indices)}")
        return start_indices

    def get_task_name(self, idx): 
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        data_idx = idx // num_samples_total
        sample_idx = idx % num_samples_total
        if num_samples_total > 1:
            return f"{self.dataset[data_idx]['id']}-{sample_idx}"
        else:
            return f"{self.dataset[data_idx]['id']}"
    
    def get_data_from_task_name(self, task_name):
        data_idx = self.get_data_idx(task_name)
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        data_idx = idx // num_samples_total
        return self.dataset[data_idx]
    
    def get_formal_statement_from_index(self, idx):
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        data_idx = idx // num_samples_total
        sample_idx = idx % num_samples_total
        local_sample_idx = sample_idx // self.num_models

        formal_statement = self.dataset[data_idx]["formal_statement"][local_sample_idx]
        return formal_statement
    
    def should_skip(self, idx):
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        sample_idx = idx % num_samples_total
        if sample_idx % self.num_models != self.model_index:
            return True
        else:
            return False

class InformalToFormalMinif2fTwoInstructPromptManager(InformalToFormalMinif2fPromptManager):
    def __init__(self, max_response_len, **kwargs):
        self.model_index = kwargs.get("model_index", None)
        assert isinstance(self.model_index, int)
        self.num_models = kwargs.get("num_models", None)
        assert self.num_models in [4]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.data_dir = kwargs.get("data_dir", None)
        assert isinstance(self.data_dir, str)

        self.batch_size = 8
        self.max_sequence_len = 8192 
        self.max_response_len = max_response_len 
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")
        self.filename_extension = "jsonl" 
        
        self.instructions = [
            "Develop formal proofs using Isabelle, leveraging auxiliary tools such as Sledgehammer to enhance the proving process.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n\n### Output",
            "Utilize Isabelle for the systematic verification of theorem proofs, employing Sledgehammer as a supplementary tool. Approach the problem in a step-by-step manner.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}",
        ]
        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx

    def get_prompt(self, idx): 
        num_samples_total = len(self.dataset[0]["formal_statement"]) * self.num_models
        data_idx = idx // num_samples_total
        sample_idx = idx % num_samples_total
        local_sample_idx = sample_idx // self.num_models

        formal_statement = self.dataset[data_idx]["formal_statement"][local_sample_idx]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        subgoal_proof = self.dataset[data_idx]["subgoal_proof"]
        template = self.instructions[local_sample_idx % len(self.instructions)]
        prompt = template.format(informal_statement, formal_statement)
        prompt = f"{prompt} (*{subgoal_proof}*)\n"
        return prompt


def write_to_file(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement, formal_proof):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "id": task_id,
            "informal_statement": informal_statement,
            "informal_proof": informal_proof,
            "subgoal_proof": subgoal_proof,
            "formal_statement": formal_statement,
            "formal_proof": formal_proof,
        }) + "\n")

def save_results(batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement, batched_formal_proof):
    for dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement, formal_proof in zip(
        batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement, batched_formal_proof):
        write_to_file(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof, formal_statement, formal_proof)


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=10000)
    parser.add_argument("--endpoint_address", type=str, default="")
    parser.add_argument("--prompt_manager_name", type=str, default="InformalToFormalPromptManager")
    parser.add_argument("--max_response_len", type=int, default=1024)
    parser.add_argument("--dump_path", type=str, default="")
    parser.add_argument("--num_models", type=int, default=1)
    parser.add_argument("--model_index", type=int, default=0)
    parser.add_argument("--temperature", type=float, default=0.4)
    parser.add_argument("--data_dir", type=str, default="")
    args = parser.parse_args()

    if args.prompt_manager_name == "InformalToFormalMinif2fPromptManager":
        prompt_manager = InformalToFormalMinif2fPromptManager(max_response_len=args.max_response_len, model_index=args.model_index, num_models=args.num_models, temperature=args.temperature, data_dir=args.data_dir)
    elif args.prompt_manager_name == "InformalToFormalMinif2fTwoInstructPromptManager":
        prompt_manager = InformalToFormalMinif2fTwoInstructPromptManager(max_response_len=args.max_response_len, model_index=args.model_index, num_models=args.num_models, temperature=args.temperature, data_dir=args.data_dir)
    else:
        raise ValueError


    batched_path = []
    batched_id = []
    batched_informal_statement = []
    batched_informal_proof = []
    batched_subgoal_proof = []
    batched_formal_statement = []
    batched_prompt = []
    for idx in range(args.start_idx, args.end_idx):
        if prompt_manager.should_skip(idx):
            continue

        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path):
            continue
        
        task_id = prompt_manager.get_data_from_index(idx)["id"]
        informal_statement = prompt_manager.get_data_from_index(idx)["informal_statement"]
        informal_proof = prompt_manager.get_data_from_index(idx)["informal_proof"]
        subgoal_proof = prompt_manager.get_data_from_index(idx)["subgoal_proof"]
        formal_statement = prompt_manager.get_formal_statement_from_index(idx)

        prompt = prompt_manager.get_prompt(idx)
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                subgoal_proof=subgoal_proof,
                formal_statement=formal_statement, 
                formal_proof=None
            )
            continue
        
        batched_path.append(dump_file_path)
        batched_id.append(task_id)
        batched_informal_statement.append(informal_statement)
        batched_informal_proof.append(informal_proof)
        batched_subgoal_proof.append(subgoal_proof)
        batched_formal_statement.append(formal_statement)
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
            batched_formal_proof = responses.json()["choices"][0]["text"]
            save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement, batched_formal_proof)

            batched_path = []
            batched_id = []
            batched_informal_statement = []
            batched_informal_proof = []
            batched_subgoal_proof = []
            batched_formal_statement = []
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
        batched_formal_proof = responses.json()["choices"][0]["text"]
        save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof, batched_formal_statement, batched_formal_proof)
