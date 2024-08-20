import argparse
import json
import math
import os
import random
import subprocess

import h5py
import requests
from transformers import AutoTokenizer

assistant_token = "### Assistant:"
user_token = "### User:"

def extract_task_id(file_name):
    # Split the file name by "."
    parts = file_name.split(".")

    # Extract the task ID, which is the first part before the file extension
    task_id = parts[0]

    return task_id

class FormalToInformalLlama3FewshotPromptManager:
    def __init__(self, data_path, model_name_or_path, max_response_len, num_samples, temperature):
        self.num_samples = num_samples
        assert self.num_samples in [1, 2, 4, 8]
        self.temperature = temperature
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        
        
        self.max_sequence_len = 8192 # necessary
        self.batch_size = 8
        self.max_response_len = max_response_len # necessary
        # self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B-Instruct")
        self.tokenizer = AutoTokenizer.from_pretrained(model_name_or_path)

        self.filename_extension = "jsonl" # necessary
        current_dir = os.path.dirname(os.path.abspath(__file__))
        repo_root = os.path.dirname(current_dir)
        with open(f"{repo_root}/data_preparation/demonstrations/vanilla/formal_to_informal.md", encoding="utf-8") as f:
            self.few_shot_prompt = f.read().strip()

        # self.dataset = h5py.File(f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/afp_train_154k.hdf5")
        # self.dataset = h5py.File(f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/std_train_42k.hdf5")
        self.dataset = h5py.File(data_path)
        self.groups = sorted(list(self.dataset.keys()), key=lambda x:int(x))
        assert len(self.groups) == int(self.groups[-1]) + 1
        
    def get_data(self, idx, key=None):
        grp = self.groups[idx // self.num_samples]
        # sample_idx = idx % self.num_samples
        data = {
            "id": self.dataset[grp]["id"][()].decode(),
            "formal_statement": self.dataset[grp]["formal_statement"][()].decode(),
            "formal_proof": self.dataset[grp]["formal_proof"][()].decode(),
        }
        if key is not None:
            return data[key]
        else:
            return data
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{self.dataset[grp]['id'][()].decode()}-{i}" for grp in self.groups for i in range(self.num_samples)]
        else:
            return [self.dataset[grp]['id'][()].decode() for grp in self.groups]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', user_token]

    def system_constructor(self):
        content = "Clearly state the problem, simplify and explain each step in plain language, summarize the result, and use LaTeX for mathematical expressions."
        return [{"role": "system", "content": content}]

    def suffix_constructor(self, formal_statement, formal_proof):
        content = f"{formal_statement}\n{formal_proof}"
        return [{"role": "user", "content": content}]
        # return f"Formal:\n{formal_statement}\n{formal_proof}\n\nInformal:"

    def middle_constructor(self, formal, informal):
        user = f"{formal}"
        assistant = f"{informal}"
        return [
            {"role": "user", "content": user},
            {"role": "assistant", "content": assistant},
        ]
    
    def parse_demonstrations(self, raw_demonstrations):
        demonstrations = []
        for raw_demo in raw_demonstrations:
            formal = raw_demo.split("Informal:")[0].strip().split("Formal:")[1].strip()
            informal = raw_demo.split("Informal:")[1].strip()
            informal = informal.split("(*")[1].split("*)")[0].strip()
            demonstrations.append({
                "formal": formal,
                "informal": informal,
            })
        return demonstrations

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            context = self.middle_constructor(**(demonstrations[0]))
            context_tokens = self.num_tokens_from_string(context[0]["content"]) + 4 + self.num_tokens_from_string(context[1]["content"]) + 4 # bos, eos, [INST] and [/INST]
            if context_tokens < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        assert len(demonstrations) == 11
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-32)

        used = 0
        context = []
        for demo in sorted_demonstrations:
            new_context = self.middle_constructor(**demo)
            to_add = self.num_tokens_from_string(new_context[0]["content"]) + 4 + self.num_tokens_from_string(new_context[1]["content"]) + 4
            if used + to_add > budget:
                break
            else:
                used += to_add
                context.extend(new_context)
        return context
    
    def apply_chat_template(self, prompt):
        result = ""
        for turn in prompt:
            if turn["role"] == "system":
                continue
            elif turn["role"] == "user":
                result += f"{user_token}\n{turn['content']}\n\n\n"
            elif turn["role"] == "assistant":
                result += f"{assistant_token}\n{turn['content']}\n\n\n"
        # result += f"{assistant_token}"
        # return result.strip()
        result += f"{assistant_token}\n"
        return result

    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples
        
        formal_statement = self.get_data(data_idx, "formal_statement")
        formal_proof = self.get_data(data_idx, "formal_proof")

        prompt_prefix = self.system_constructor()
        prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
        prompt_suffix = self.suffix_constructor(formal_statement, formal_proof)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
        remain_budget = self.max_sequence_len - self.max_response_len - prefix_tokens - suffix_tokens - 32
        # remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens - 32

        demonstrations = self.parse_demonstrations(self.few_shot_prompt.split("\n\n\n\n"))
        prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)

        prompt = prompt_prefix + prompt_middle + prompt_suffix
        # prompt = prompt_middle + prompt_suffix
        # prompt = self.tokenizer.apply_chat_template(prompt, tokenize=False)
        prompt = self.apply_chat_template(prompt)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.groups) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = set([extract_task_id(file_name) for file_name in file_names if file_name.endswith(self.filename_extension)])
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.groups) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"{self.get_data(data_idx, 'id')}-{sample_idx}"
        else:
            return self.get_data(data_idx, 'id')
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        
        return self.get_data(data_idx)

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.get_data(data_idx)

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_response_len, self.max_sequence_len - self.num_tokens_from_string(prompt)),
            "stop_sequences": self.stop_generation(),
        }

def write_to_file(dump_file_path, task_id, formal_statement, formal_proof, prediction, informal_statement, informal_proof):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "id": task_id,
            "formal_statement": formal_statement,
            "formal_proof": formal_proof,
            "prediction": prediction,
            "informal_statement": informal_statement,
            "informal_proof": informal_proof,
        }) + "\n")

def save_results(batched_dump_path, batched_id, batched_formal_statement, batched_formal_proof, batched_prediction, batched_informal_statement, batched_informal_proof):
    for dump_file_path, task_id, formal_statement, formal_proof, prediction, informal_statement, informal_proof in zip(
        batched_dump_path, batched_id, batched_formal_statement, batched_formal_proof, batched_prediction, batched_informal_statement, batched_informal_proof):
        write_to_file(dump_file_path, task_id, formal_statement, formal_proof, prediction, informal_statement, informal_proof)

def post_process(response):
    response = response.strip()
    if response.startswith(assistant_token):
        response = response.split(assistant_token)[1].strip()
    return response

def extract_statement_and_proof(prediction):
    if "Informal:" in prediction:
        prediction = prediction.split("Informal:")[1].strip()
    else:
        prediction = prediction.strip()

    if "### Problem" not in prediction or "### Solution" not in prediction:
        return None, None
    informal_statement = prediction.split("### Problem")[1].split("### Solution")[0].strip()
    informal_proof = prediction.split("### Solution")[1].strip()
    return informal_statement, informal_proof

def parse_prediction_result(batched_prediction):
    batched_informal_statement = []
    batched_informal_proof = []
    for prediction in batched_prediction:
        prediction = post_process(prediction.strip())
        informal_statement, informal_proof = extract_statement_and_proof(prediction)
        batched_informal_statement.append(informal_statement)
        batched_informal_proof.append(informal_proof)
    return batched_informal_statement, batched_informal_proof


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=10000)
    parser.add_argument("--data_path", type=str, default="")
    parser.add_argument("--model_name_or_path", type=str, default="")
    parser.add_argument("--endpoint_address", type=str, default="")
    parser.add_argument("--prompt_manager_name", type=str, default="FormalToInformalLlama3FewshotPromptManager")
    parser.add_argument("--dump_path", type=str, default="")
    parser.add_argument("--max_response_len", type=int, default=1024)
    parser.add_argument("--num_samples", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=0.4)
    args = parser.parse_args()

    if args.prompt_manager_name == "FormalToInformalLlama3FewshotPromptManager":
        prompt_manager = FormalToInformalLlama3FewshotPromptManager(
            data_path=args.data_path, model_name_or_path=args.model_name_or_path, max_response_len=args.max_response_len, num_samples=args.num_samples, temperature=args.temperature)
    else:
        raise ValueError

    batched_path = []
    batched_id = []
    batched_formal_statement = []
    batched_formal_proof = []
    batched_prompt = []
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path): 
            # print(f"dump_file_path {dump_file_path} exists, skip...")
            continue

        task_id = prompt_manager.get_data_from_index(idx)["id"]
        formal_statement = prompt_manager.get_data_from_index(idx)["formal_statement"]
        formal_proof = prompt_manager.get_data_from_index(idx)["formal_proof"]

        prompt = prompt_manager.get_prompt(idx)
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                formal_statement=formal_statement, 
                formal_proof=formal_proof, 
                prediction=None,
                informal_statement=None, 
                informal_proof=None
            )
            continue

        batched_path.append(dump_file_path)
        batched_id.append(task_id)
        batched_formal_statement.append(formal_statement)
        batched_formal_proof.append(formal_proof)
        batched_prompt.append(prompt)
        if len(batched_prompt) == prompt_manager.batch_size:
            max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_prompt,
                "do_sample": True,
                # 'top_p': 0.5, 
                # 'top_k': 800, 
                'temperature': prompt_manager.temperature,
                "max_tokens": min(prompt_manager.max_response_len, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_prediction = responses.json()["choices"][0]["text"]
            batched_informal_statement, batched_informal_proof = parse_prediction_result(batched_prediction)
            save_results(batched_path, batched_id, batched_formal_statement, batched_formal_proof, batched_prediction, batched_informal_statement, batched_informal_proof)

            batched_path = []
            batched_id = []
            batched_formal_statement = []
            batched_formal_proof = []
            batched_prompt = []


    if len(batched_prompt) > 0:
        max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_prompt,
            "do_sample": True,
            # 'top_p': 0.5, 
            # 'top_k': 800, 
            'temperature': prompt_manager.temperature,
            "max_tokens": min(prompt_manager.max_response_len, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_prediction = responses.json()["choices"][0]["text"]
        batched_informal_statement, batched_informal_proof = parse_prediction_result(batched_prediction)
        save_results(batched_path, batched_id, batched_formal_statement, batched_formal_proof, batched_prediction, batched_informal_statement, batched_informal_proof)
