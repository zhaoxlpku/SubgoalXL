import argparse
import json
import math
import os
import random
import subprocess

import requests
from transformers import AutoTokenizer

from utils.autoformalization_utils import is_valid_case, is_nontrivial_case, is_good_case
from utils.prompt_utils import extract_math_final_answer, last_boxed_only_string, remove_boxed

MAX_FORMAL_STATEMENT_LEN = 512 # TODO: obtain max formal statement length
MAX_FORMAL_PROOF_LEN = 1024

assistant_token = "### Assistant:"
user_token = "### User:"

class FewshotPromptManager:
    def __init__(self, num_samples, temperature, solved_problems_path=""):
        self.num_samples = num_samples
        assert isinstance(self.num_samples, int)
        self.temperature = temperature
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.solved_problems_path = solved_problems_path
        if self.solved_problems_path:
            with open(self.solved_problems_path, encoding="utf-8") as f:
                self.solved_problems = f.read().strip().split("\n")
        else:
            self.solved_problems = []
        
        self.max_sequence_len = 4096 # necessary
        self.batch_size = 1
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        current_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.dirname(current_dir)
        with open(f"{self.repo_root}/data_preparation/demonstrations/vanilla/informal_statement_to_formal_statement_demonstrations.md", encoding="utf-8") as f:
            self.formal_statement_prompt = f.read().strip()
        with open(f"{self.repo_root}/data_preparation/demonstrations/vanilla/informal_proof_to_formal_proof_demonstrations.md", encoding="utf-8") as f:
            self.formal_proof_prompt = f.read().strip()

        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx
    
    def load_data(self, ignore_geometry_problems=True):
        math_path = f"{self.repo_root}/datasets/math/train_clean_threshold0_1.0.jsonl"

        dataset = []
        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                pid = json_obj["id"]
                if ("[asy]" in informal_statement and "[/asy]" in informal_statement) or ("[asy]" in informal_proof and "[/asy]" in informal_proof):
                    continue
                if pid in self.solved_problems:
                    continue
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": pid,
                })
        return dataset
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, informal_statement, informal_proof=None, formal_statement=None, task="formal_statement"):
        if task == "formal_statement":
            return f"Informal:\n(*### Problem\n\n{informal_statement}*)\n\nFormal:"
        else:
            return f"Informal:\n(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nInformal:']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx, formal_statement=None, task="formal_statement"): # necessary
        data_idx = idx // self.num_samples # the {data_idx}-th element in self.dataset
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # formal_statement = self.dataset[data_idx]["formal_statement"]

        if task == "formal_statement":
            prompt_suffix = self.suffix_constructor(informal_statement, task="formal_statement")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix)
            remain_budget = self.max_sequence_len - MAX_FORMAL_STATEMENT_LEN - suffix_tokens
        else:
            prompt_suffix = self.suffix_constructor(informal_statement, informal_proof=informal_proof, formal_statement=formal_statement, task="formal_proof")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix)
            remain_budget = self.max_sequence_len - MAX_FORMAL_PROOF_LEN - suffix_tokens
        
        if task == "formal_statement":
            prompt_middle = self.sample_demonstrations(self.formal_statement_prompt.split("\n\n\n\n"), budget=remain_budget)
        else:
            prompt_middle = self.sample_demonstrations(self.formal_proof_prompt.split("\n\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
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

    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [file_name.split(".")[0] for file_name in file_names if file_name.endswith(self.filename_extension)]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        sorted_unfinished = sorted(unfinished, key=lambda x: (self.get_data_idx(x), self.get_sample_idx(x)))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
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
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
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

    def get_generation_config(self, prompt, task="formal_statement"): # necessary
        if task == "formal_statement":
            max_response_len = MAX_FORMAL_STATEMENT_LEN
        else:
            max_response_len = MAX_FORMAL_PROOF_LEN
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_sequence_len - self.num_tokens_from_string(prompt), max_response_len),
            "stop_sequences": self.stop_generation(),
        }
    
    def post_process(self, response):
        return response

class Llama3FewshotPromptManager(FewshotPromptManager):
    def __init__(self, num_samples, temperature, solved_problems_path=""):
        self.num_samples = num_samples
        assert isinstance(self.num_samples, int)
        self.temperature = temperature
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.solved_problems_path = solved_problems_path
        if self.solved_problems_path:
            with open(self.solved_problems_path, encoding="utf-8") as f:
                self.solved_problems = f.read().strip().split("\n")
        else:
            self.solved_problems = []
        
        self.max_sequence_len = 8192 # necessary
        self.batch_size = 8
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B-Instruct")

        self.filename_extension = "jsonl" # necessary
        current_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.dirname(current_dir)
        with open(f"{self.repo_root}/data_preparation/demonstrations/subgoal/informal_statement_to_formal_statement_demonstrations.md", encoding="utf-8") as f:
            self.formal_statement_prompt = f.read().strip()
        
        with open(f"{self.repo_root}/data_preparation/demonstrations/subgoal/informal_statement_to_formal_proof.md", encoding="utf-8") as f:
            self.formal_proof_prompt = f.read().strip()

        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx

    def load_data(self, ignore_geometry_problems=True):
        math_path = f"{self.repo_root}/datasets/compose/math_aime_imo_threshold0_1.jsonl"

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
                if pid in self.solved_problems:
                    continue
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": pid,
                })
        return dataset
    
    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']
    
    def system_constructor(self, task="formal_statement"):
        if task == "formal_statement":
            content = "Use Isabelle to formalize informal mathematical problems by defining the necessary variables and assumptions, followed by constructing the precise theorem statements."
        else:
            content = "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving."
        return [{"role": "system", "content": content}]

    def suffix_constructor(self, informal_statement, informal_proof=None, formal_statement=None, task="formal_statement"):
        if task == "formal_statement":
            content = f"text \<open>\n{informal_statement.strip()}\n\<close>"
        else:
            content = f"text \<open>\n{informal_statement.strip()}\n\<close>\n\n{formal_statement.strip()}"
        return [{"role": "user", "content": content}]

    def middle_constructor(self, informal_statement, formal_statement, informal_proof=None, formal_proof=None, task="formal_statement"):
        if task == "formal_statement":
            user = f"text \<open>\n{informal_statement.strip()}\n\<close>"
            assistant = formal_statement
        else:
            user = f"text \<open>\n{informal_statement.strip()}\n\<close>\n\n{formal_statement.strip()}"
            assistant = formal_proof
        return [
            {"role": "user", "content": user},
            {"role": "assistant", "content": assistant},
        ]

    def parse_demonstrations(self, raw_demonstrations, task="formal_statement"):
        if task == "formal_statement":
            demonstrations = []
            for raw_demo in raw_demonstrations:
                formal_statement = raw_demo.split("Formal:")[1].strip()
                informal_statement = raw_demo.split("(*### Problem")[1].strip().split("*)")[0].strip()
                demonstrations.append({
                    "informal_statement": informal_statement,
                    "formal_statement": formal_statement,
                    "task": "formal_statement",
                })
        else:
            demonstrations = []
            for raw_demo in raw_demonstrations:
                formal_proof = raw_demo.split("### Formal Proof")[1].strip()
                formal_statement = raw_demo.split("### Formal Statement")[1].strip().split("### Formal Proof")[0].strip()
                informal_statement = raw_demo.split("### Informal Statement")[1].strip().split("### Formal Statement")[0].strip()
                demonstrations.append({
                    "informal_statement": informal_statement,
                    "formal_statement": formal_statement,
                    "formal_proof": formal_proof,
                    "task": "formal_proof",
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
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-32)

        used = 0
        context = []
        for demo in sorted_demonstrations[:16]:
            new_context = self.middle_constructor(**demo)
            to_add = self.num_tokens_from_string(new_context[0]["content"]) + 4 + self.num_tokens_from_string(new_context[1]["content"]) + 4
            if used + to_add > budget:
                break
            else:
                used += to_add
                context.extend(new_context)
        return context
    
    def get_prompt(self, idx, formal_statement=None, task="formal_statement"): # necessary
        data_idx = idx // self.num_samples # the {data_idx}-th element in self.dataset
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # formal_statement = self.dataset[data_idx]["formal_statement"]

        if task == "formal_statement":
            prompt_prefix = self.system_constructor(task=task)
            prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
            prompt_suffix = self.suffix_constructor(informal_statement, task="formal_statement")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
            remain_budget = self.max_sequence_len - MAX_FORMAL_STATEMENT_LEN - prefix_tokens - suffix_tokens - 32
        else:
            prompt_prefix = self.system_constructor(task=task)
            prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
            prompt_suffix = self.suffix_constructor(informal_statement, formal_statement=formal_statement, task="formal_proof")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
            remain_budget = self.max_sequence_len - MAX_FORMAL_PROOF_LEN - prefix_tokens - suffix_tokens - 32
        
        if task == "formal_statement":
            demonstrations = self.parse_demonstrations(self.formal_statement_prompt.split("\n\n\n\n"), task=task)
            prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)
        else:
            demonstrations = self.parse_demonstrations(self.formal_proof_prompt.split("\n\n\n\n"), task=task)
            prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)
        prompt = prompt_prefix + prompt_middle + prompt_suffix
        prompt = self.tokenizer.apply_chat_template(prompt, tokenize=False)
        return prompt
    
    def get_generation_config(self, prompt, task="formal_statement"): # necessary
        if task == "formal_statement":
            max_response_len = MAX_FORMAL_STATEMENT_LEN
        else:
            max_response_len = MAX_FORMAL_PROOF_LEN
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_sequence_len - self.num_tokens_from_string(prompt), max_response_len),
            "stop_sequences": self.stop_generation(),
        }

    def post_process(self, response):
        if response.startswith("assistant"):
            response = response.split("assistant")[1].strip()
        return response

class Llama3BaseFewshotPromptManager(Llama3FewshotPromptManager):
    def __init__(self, num_samples, temperature, solved_problems_path=""):
        self.num_samples = num_samples
        assert isinstance(self.num_samples, int)
        self.temperature = temperature
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.solved_problems_path = solved_problems_path
        if self.solved_problems_path:
            with open(self.solved_problems_path, encoding="utf-8") as f:
                self.solved_problems = f.read().strip().split("\n")
        else:
            self.solved_problems = []
        
        self.max_sequence_len = 8192 # necessary
        self.batch_size = 8
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")

        self.filename_extension = "jsonl" # necessary
        current_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.dirname(current_dir)
        with open(f"{self.repo_root}/data_preparation/demonstrations/subgoal/informal_statement_to_formal_statement_demonstrations.md", encoding="utf-8") as f:
            self.formal_statement_prompt = f.read().strip()
        
        with open(f"{self.repo_root}/data_preparation/demonstrations/subgoal/informal_statement_to_formal_proof.md", encoding="utf-8") as f:
            self.formal_proof_prompt = f.read().strip()

        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx
    
    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', user_token]
    
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

    def get_prompt(self, idx, formal_statement=None, task="formal_statement"): # necessary
        data_idx = idx // self.num_samples # the {data_idx}-th element in self.dataset
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # formal_statement = self.dataset[data_idx]["formal_statement"]

        if task == "formal_statement":
            prompt_prefix = self.system_constructor(task=task)
            prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
            prompt_suffix = self.suffix_constructor(informal_statement, task="formal_statement")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
            remain_budget = self.max_sequence_len - MAX_FORMAL_STATEMENT_LEN - prefix_tokens - suffix_tokens - 32
        else:
            prompt_prefix = self.system_constructor(task=task)
            prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
            prompt_suffix = self.suffix_constructor(informal_statement, formal_statement=formal_statement, task="formal_proof")
            suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
            remain_budget = self.max_sequence_len - MAX_FORMAL_PROOF_LEN - prefix_tokens - suffix_tokens - 32
        
        if task == "formal_statement":
            demonstrations = self.parse_demonstrations(self.formal_statement_prompt.split("\n\n\n\n"), task=task)
            prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)
        else:
            demonstrations = self.parse_demonstrations(self.formal_proof_prompt.split("\n\n\n\n"), task=task)
            prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)
        prompt = prompt_prefix + prompt_middle + prompt_suffix
        prompt = self.apply_chat_template(prompt)
        return prompt
    
    def post_process(self, response):
        response = response.strip()
        if response.startswith(assistant_token):
            response = response.split(assistant_token)[1].strip()
        return response
    
class Llama3BaseSubgoalPromptManager(FewshotPromptManager):
    def __init__(self, num_samples, temperature, solved_problems_path=""):
        self.num_samples = num_samples
        assert isinstance(self.num_samples, int)
        self.temperature = temperature
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.solved_problems_path = solved_problems_path
        if self.solved_problems_path:
            with open(self.solved_problems_path, encoding="utf-8") as f:
                self.solved_problems = f.read().strip().split("\n")
        else:
            self.solved_problems = []
        
        self.max_sequence_len = 8192 # necessary
        self.batch_size = 8
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")

        self.filename_extension = "jsonl" # necessary
        current_dir = os.path.dirname(os.path.abspath(__file__))
        self.repo_root = os.path.dirname(current_dir)
        with open(f"{self.repo_root}/data_preparation/demonstrations/subgoal/informal_statement_to_informal_proof.md", encoding="utf-8") as f:
            self.subgoal_proof_prompt = f.read().strip()

        self.dataset = self.load_data()
        self.id_to_idx = {}
        for idx, data in enumerate(self.dataset):
            self.id_to_idx[data['id']] = idx

    def load_data(self, ignore_geometry_problems=True):
        math_path = f"{self.repo_root}/datasets/compose/math_aime_imo_threshold0_1.jsonl"

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
                if pid in self.solved_problems:
                    continue
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": pid,
                })
        return dataset
    
    def system_constructor(self):
        content = "To generate a subgoal-based proof from an informal statement and informal proof, systematically decompose the informal proof into smaller logical steps (subgoals), then prove each subgoal to logically build towards proving the main theorem."
        return [{"role": "system", "content": content}]

    def suffix_constructor(self, informal_statement, informal_proof):
        content = f"text \<open>\n### Informal Statement:\n{informal_statement.strip()}\n\n### Informal Proof:\n{informal_proof.strip()}\n\<close>"
        return [{"role": "user", "content": content}]

    def middle_constructor(self, informal_statement, informal_proof, subgoal_proof):
        user = f"text \<open>\n### Informal Statement:\n{informal_statement.strip()}\n\n### Informal Proof:\n{informal_proof.strip()}\n\<close>"
        assistant = subgoal_proof
        return [
            {"role": "user", "content": user},
            {"role": "assistant", "content": assistant},
        ]

    def parse_demonstrations(self, raw_demonstrations):
        demonstrations = []
        for raw_demo in raw_demonstrations:
            subgoal_proof = raw_demo.split("### Subgoal-based Proof")[1].strip()
            informal_proof = raw_demo.split("### Informal Proof")[1].strip().split("### Subgoal-based Proof")[0].strip()
            informal_statement = raw_demo.split("### Informal Statement")[1].strip().split("### Formal Statement")[0].strip()
            
            demonstrations.append({
                "informal_statement": informal_statement,
                "informal_proof": informal_proof,
                "subgoal_proof": subgoal_proof,
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
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-32)

        used = 0
        context = []
        for demo in sorted_demonstrations[:16]:
            new_context = self.middle_constructor(**demo)
            to_add = self.num_tokens_from_string(new_context[0]["content"]) + 4 + self.num_tokens_from_string(new_context[1]["content"]) + 4
            if used + to_add > budget:
                break
            else:
                used += to_add
                context.extend(new_context)
        return context
    
    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', user_token]
    
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
        data_idx = idx // self.num_samples # the {data_idx}-th element in self.dataset
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]

        prompt_prefix = self.system_constructor()
        prefix_tokens = self.num_tokens_from_string(prompt_prefix[0]["content"]) + 4 # <<SYS>> and <</SYS>>
        prompt_suffix = self.suffix_constructor(informal_statement, informal_proof)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix[0]["content"]) + 4 # [INST] and [/INST]
        remain_budget = self.max_sequence_len - MAX_FORMAL_PROOF_LEN - prefix_tokens - suffix_tokens - 32
        
        demonstrations = self.parse_demonstrations(self.subgoal_proof_prompt.split("\n\n\n\n"))
        prompt_middle = self.sample_demonstrations(demonstrations, budget=remain_budget)
        prompt = prompt_prefix + prompt_middle + prompt_suffix
        prompt = self.apply_chat_template(prompt)
        return prompt
    
    def post_process(self, response):
        response = response.strip()
        if response.startswith(assistant_token):
            response = response.split(assistant_token)[1].strip()
        return response

def write_to_file(dump_file_path, task_id, informal_statement, informal_proof, formal_statement, formal_proof):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "id": task_id,
            "informal_statement": informal_statement,
            "informal_proof": informal_proof,
            "formal_statement": formal_statement,
            "formal_proof": formal_proof,
        }) + "\n")

def write_to_file2(dump_file_path, formal_statement, result, message):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "formal_statement": formal_statement,
            "result": result,
            "message": message,
        }) + "\n")

def write_to_file3(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof):
    with open(dump_file_path, "w", encoding="utf-8") as f:
        f.write(json.dumps({
            "id": task_id,
            "informal_statement": informal_statement,
            "informal_proof": informal_proof,
            "subgoal_proof": subgoal_proof,
        }) + "\n")

def save_results(batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_formal_statement, batched_formal_proof):
    for dump_file_path, task_id, informal_statement, informal_proof, formal_statement, formal_proof in zip(
        batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_formal_statement, batched_formal_proof):
        write_to_file(dump_file_path, task_id, informal_statement, informal_proof, formal_statement, formal_proof)

def save_results2(batched_dump_path, batched_formal_statement, batched_result, batched_message):
    for dump_file_path, formal_statement, result, message in zip(batched_dump_path, batched_formal_statement, batched_result, batched_message):
        write_to_file2(dump_file_path, formal_statement, result, message)

def save_results3(batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof):
    for dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof in zip(
        batched_dump_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof):
        write_to_file3(dump_file_path, task_id, informal_statement, informal_proof, subgoal_proof)


def statement_and_proof_generation(args):
    if args.prompt_manager_name == "FewshotPromptManager":
        prompt_manager = FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3FewshotPromptManager":
        prompt_manager = Llama3FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    else:
        raise ValueError

    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path): 
            # print(f"dump_file_path {dump_file_path} exists, skip...")
            continue

        task_id = prompt_manager.get_data_from_index(idx)["id"]
        informal_statement = prompt_manager.get_data_from_index(idx)["informal_statement"]
        informal_proof = prompt_manager.get_data_from_index(idx)["informal_proof"]

        # generate formal_statement
        formal_statement_prompt = prompt_manager.get_prompt(idx, task="formal_statement")
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(formal_statement_prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                formal_statement=None, 
                formal_proof=None
            )
            continue
        
        json_obj = prompt_manager.get_generation_config(prompt=formal_statement_prompt, task="formal_statement")
        response = requests.post(f'http://{args.endpoint_address}/completions', json=json_obj)
        response = json.loads(response.text)
        formal_statement = prompt_manager.post_process(response['choices'][0]['text'].strip())

        # generate formal proof
        formal_proof_prompt = prompt_manager.get_prompt(idx, formal_statement=formal_statement, task="formal_proof")
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(formal_proof_prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                formal_statement=formal_statement, 
                formal_proof=None,
            )
            continue


        json_obj = prompt_manager.get_generation_config(prompt=formal_proof_prompt, task="formal_proof")
        response = requests.post(f'http://{args.endpoint_address}/completions', json=json_obj)
        response = json.loads(response.text)
        formal_proof = prompt_manager.post_process(response['choices'][0]['text'].strip())
        write_to_file(
            dump_file_path=dump_file_path, 
            task_id=task_id, 
            informal_statement=informal_statement, 
            informal_proof=informal_proof, 
            formal_statement=formal_statement,
            formal_proof=formal_proof,
        )



def statement_and_proof_generation_batched(args):
    if args.prompt_manager_name == "FewshotPromptManager":
        prompt_manager = FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3FewshotPromptManager":
        prompt_manager = Llama3FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3BaseFewshotPromptManager":
        prompt_manager = Llama3BaseFewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    else:
        raise ValueError

    batched_path = []
    batched_id = []
    batched_informal_statement = []
    batched_informal_proof = []
    batched_statement_prompt = []
    batched_idx = []
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path): 
            # print(f"dump_file_path {dump_file_path} exists, skip...")
            continue

        task_id = prompt_manager.get_data_from_index(idx)["id"]
        informal_statement = prompt_manager.get_data_from_index(idx)["informal_statement"]
        informal_proof = prompt_manager.get_data_from_index(idx)["informal_proof"]

        # generate formal_statement
        formal_statement_prompt = prompt_manager.get_prompt(idx, task="formal_statement")
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(formal_statement_prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                formal_statement=None, 
                formal_proof=None
            )
            continue
        
        batched_path.append(dump_file_path)
        batched_id.append(task_id)
        batched_informal_statement.append(informal_statement)
        batched_informal_proof.append(informal_proof)
        batched_statement_prompt.append(formal_statement_prompt)
        batched_idx.append(idx)
        if len(batched_statement_prompt) == prompt_manager.batch_size:
            max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_statement_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_statement_prompt,
                "do_sample": True,
                # 'top_p': 0.5, 
                # 'top_k': 800, 
                'temperature': prompt_manager.temperature,
                "max_tokens": min(MAX_FORMAL_STATEMENT_LEN, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_formal_statement = responses.json()["choices"][0]["text"]
            batched_formal_statement = [prompt_manager.post_process(formal_statement.strip()) for formal_statement in batched_formal_statement]

            batched_proof_prompt = [prompt_manager.get_prompt(idx, formal_statement=formal_statement, task="formal_proof") for idx, formal_statement in zip(batched_idx, batched_formal_statement)]
            max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_proof_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_proof_prompt,
                "do_sample": True,
                # 'top_p': 0.5, 
                # 'top_k': 800, 
                'temperature': prompt_manager.temperature,
                "max_tokens": min(MAX_FORMAL_PROOF_LEN, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_formal_proof = responses.json()["choices"][0]["text"]
            batched_formal_proof = [prompt_manager.post_process(formal_proof.strip()) for formal_proof in batched_formal_proof]
            save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_formal_statement, batched_formal_proof)

            batched_path = []
            batched_id = []
            batched_informal_statement = []
            batched_informal_proof = []
            batched_statement_prompt = []
            batched_idx = []
    
    if len(batched_statement_prompt) > 0:
        max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_statement_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_statement_prompt,
            "do_sample": True,
            # 'top_p': 0.5, 
            # 'top_k': 800, 
            'temperature': prompt_manager.temperature,
            "max_tokens": min(MAX_FORMAL_STATEMENT_LEN, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_formal_statement = responses.json()["choices"][0]["text"]
        batched_formal_statement = [prompt_manager.post_process(formal_statement.strip()) for formal_statement in batched_formal_statement]

        batched_proof_prompt = [prompt_manager.get_prompt(idx, formal_statement=formal_statement, task="formal_proof") for idx, formal_statement in zip(batched_idx, batched_formal_statement)]
        max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_proof_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_proof_prompt,
            "do_sample": True,
            # 'top_p': 0.5, 
            # 'top_k': 800, 
            'temperature': prompt_manager.temperature,
            "max_tokens": min(MAX_FORMAL_PROOF_LEN, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_formal_proof = responses.json()["choices"][0]["text"]
        batched_formal_proof = [prompt_manager.post_process(formal_proof.strip()) for formal_proof in batched_formal_proof]
        save_results(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_formal_statement, batched_formal_proof)



        
def statement_validation(args):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    with open(f"{repo_root}/data_preparation/demonstrations/statement_validation_demonstrations.md", encoding="utf-8") as f:
        demonstration = f.read().strip()
    
    if args.prompt_manager_name == "FewshotPromptManager":
        prompt_manager = FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3FewshotPromptManager":
        prompt_manager = Llama3FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    else:
        raise ValueError
    
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        
        if os.path.exists(dump_file_path): 
            continue
        else:
            # print(f"start quering problem {task_name}".format())
            if len(dump_file_path.split("/")) == 3:
                autoformalization_path = "autoformalization/" + "/".join(dump_file_path.split("/")[-2:])
            else:
                autoformalization_path = "/".join(dump_file_path.split("/")[:-3]) + "/autoformalization/" + "/".join(dump_file_path.split("/")[-2:])
            with open(autoformalization_path, encoding="utf-8") as f:
                json_obj = json.loads(f.read().strip())
            formal_statement = json_obj["formal_statement"]
            if formal_statement is None:
                result = False
                message = "An overly lengthy informal statement invalidates cases."
            elif not is_valid_case(formal_statement=formal_statement):
                result = False
                message = "Single-lined or improperly formatted statements invalidate cases."
            elif not is_nontrivial_case(formal_statement=formal_statement):
                result = False
                message = "Objective lacking variables or containing cancelable terms makes cases trivial."
            else:
                result, message = is_good_case(
                    formal_statement=formal_statement,
                    endpoint=args.endpoint_address,
                    tokenizer=prompt_manager.tokenizer,
                    demonstration=demonstration,
                    use_chat=True if "Llama3" in args.prompt_manager_name else False
                )
            
            with open(dump_file_path, "w", encoding="utf-8") as f:
                f.write(json.dumps({
                    "formal_statement": formal_statement,
                    "result": result,
                    "message": message,
                }) + "\n")

def get_validation_prompt(formal_statement, tokenizer, demonstration, use_chat=False):
    if not use_chat:
        prompt = f"{demonstration}\n\n---\n\n### Input\n{formal_statement}\n\n### Output"
    else:
        system = "Verify if the objective is a trivial consequence of the assumptions, unrelated, or leads to a contradiction, and classify the statement as either $\\boxed{good}$ or $\\boxed{bad}$."
        chat_history = [{"role": "system", "content": system}]
        demos = demonstration.split("---")
        for demo in demos:
            user = demo.split("### Output")[0].split("### Input")[1].strip()
            assistant = demo.split("### Output")[1].strip()
            chat_history.append(
                {"role": "user", "content": user},
            )
            chat_history.append(
                {"role": "assistant", "content": assistant},
            )
        chat_history.append(
            {"role": "user", "content": formal_statement}
        )
        prompt = tokenizer.apply_chat_template(chat_history, tokenize=False)
    return prompt

def parse_validation_result(batched_prediction):
    batched_result = []
    batched_message = []
    for prediction in batched_prediction:
        if prediction.startswith("assistant"):
            prediction = prediction.split("assistant")[1].strip()
        
        answer = remove_boxed(last_boxed_only_string(prediction))
        if isinstance(answer, str) and answer.strip() == "good":
            result = True
        else:
            result = False
        batched_result.append(result)
        batched_message.append(prediction)
    return batched_result, batched_message

def statement_validation_batched(args):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    with open(f"{repo_root}/data_preparation/demonstrations/statement_validation_demonstrations.md", encoding="utf-8") as f:
        demonstration = f.read().strip()
    
    if args.prompt_manager_name == "FewshotPromptManager":
        prompt_manager = FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3FewshotPromptManager":
        prompt_manager = Llama3FewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    elif args.prompt_manager_name == "Llama3BaseFewshotPromptManager":
        prompt_manager = Llama3BaseFewshotPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    else:
        raise ValueError

    use_chat = True if args.prompt_manager_name in ["Llama3FewshotPromptManager"] else False

    batched_formal_statement = []
    batched_prompt = []
    batched_dump_path = []
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        
        if os.path.exists(dump_file_path): 
            continue
        
        if len(dump_file_path.split("/")) == 3:
            autoformalization_path = "autoformalization/" + "/".join(dump_file_path.split("/")[-2:])
        else:
            autoformalization_path = "/".join(dump_file_path.split("/")[:-3]) + "/autoformalization/" + "/".join(dump_file_path.split("/")[-2:])
        with open(autoformalization_path, encoding="utf-8") as f:
            json_obj = json.loads(f.read().strip())
        formal_statement = json_obj["formal_statement"]
        
        if formal_statement is None:
            result = False
            message = "An overly lengthy informal statement invalidates cases."
            write_to_file2(dump_file_path, formal_statement, result, message)
            continue
        
        if not is_valid_case(formal_statement=formal_statement):
            result = False
            message = "Single-lined or improperly formatted statements invalidate cases."
            write_to_file2(dump_file_path, formal_statement, result, message)
            continue

        if not is_nontrivial_case(formal_statement=formal_statement):
            result = False
            message = "Objective lacking variables or containing cancelable terms makes cases trivial."
            write_to_file2(dump_file_path, formal_statement, result, message)
            continue
        
        prompt = get_validation_prompt(formal_statement, prompt_manager.tokenizer, demonstration, use_chat)
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(prompt) <= 10:
            result = False
            message = "Excessive statement length indicates flaws or ambiguities in cases."
            write_to_file2(dump_file_path, formal_statement, result, message)
            continue
        
        batched_formal_statement.append(formal_statement)
        batched_prompt.append(prompt)
        batched_dump_path.append(dump_file_path)

        if len(batched_prompt) == prompt_manager.batch_size:
            max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_prompt,
                "do_sample": False,
                # 'top_p': 0.5, 
                # 'top_k': 800, 
                # 'temperature': 0.2,
                "max_tokens": min(1024, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_prediction = responses.json()["choices"][0]["text"]
            batched_result, batched_message = parse_validation_result(batched_prediction)
            save_results2(batched_dump_path, batched_formal_statement, batched_result, batched_message)

            batched_formal_statement = []
            batched_prompt = []
            batched_dump_path = []
    if len(batched_prompt) > 0:
        max_batch_length = max([prompt_manager.num_tokens_from_string(prompt) for prompt in batched_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_prompt,
            "do_sample": False,
            # 'top_p': 0.5, 
            # 'top_k': 800, 
            # 'temperature': 0.2,
            "max_tokens": min(1024, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_prediction = responses.json()["choices"][0]["text"]
        batched_result, batched_message = parse_validation_result(batched_prediction)
        save_results2(batched_dump_path, batched_formal_statement, batched_result, batched_message)


def subgoal_generation_batched(args):
    if args.prompt_manager_name == "Llama3BaseSubgoalPromptManager":
        prompt_manager = Llama3BaseSubgoalPromptManager(num_samples=args.num_samples, temperature=args.temperature, solved_problems_path=args.solved_problems_path)
    else:
        raise ValueError

    batched_path = []
    batched_id = []
    batched_informal_statement = []
    batched_informal_proof = []
    batched_prompt = []
    for idx in range(args.start_idx, args.end_idx):
        task_name = prompt_manager.get_task_name(idx)
        dump_path = args.dump_path
        dump_file_path = os.path.join(dump_path, f"{task_name}.{prompt_manager.filename_extension}")
        if os.path.exists(dump_file_path): 
            # print(f"dump_file_path {dump_file_path} exists, skip...")
            continue

        task_id = prompt_manager.get_data_from_index(idx)["id"]
        informal_statement = prompt_manager.get_data_from_index(idx)["informal_statement"]
        informal_proof = prompt_manager.get_data_from_index(idx)["informal_proof"]

        # generate formal_statement
        prompt = prompt_manager.get_prompt(idx)
        if prompt_manager.max_sequence_len - prompt_manager.num_tokens_from_string(prompt) <= 10:
            print("too few tokens left for generation, skip this query")
            write_to_file3(
                dump_file_path=dump_file_path, 
                task_id=task_id, 
                informal_statement=informal_statement, 
                informal_proof=informal_proof, 
                subgoal_proof=None,
            )
            continue
        
        batched_path.append(dump_file_path)
        batched_id.append(task_id)
        batched_informal_statement.append(informal_statement)
        batched_informal_proof.append(informal_proof)
        batched_prompt.append(prompt)
        if len(batched_prompt) == prompt_manager.batch_size:
            max_batch_length = max([prompt_manager.num_tokens_from_string(p) for p in batched_prompt])
            responses = requests.post(f'http://{args.endpoint_address}/completions', json={
                "prompt": batched_prompt,
                "do_sample": True,
                'temperature': prompt_manager.temperature,
                "max_tokens": min(MAX_FORMAL_PROOF_LEN, prompt_manager.max_sequence_len - max_batch_length),
                "stop_sequences": prompt_manager.stop_generation(),
            })
            batched_subgoal_proof = responses.json()["choices"][0]["text"]
            batched_subgoal_proof = [prompt_manager.post_process(subgoal_proof.strip()) for subgoal_proof in batched_subgoal_proof]

            save_results3(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof)

            batched_path = []
            batched_id = []
            batched_informal_statement = []
            batched_informal_proof = []
            batched_prompt = []
    
    if len(batched_prompt) > 0:
        max_batch_length = max([prompt_manager.num_tokens_from_string(p) for p in batched_prompt])
        responses = requests.post(f'http://{args.endpoint_address}/completions', json={
            "prompt": batched_prompt,
            "do_sample": True,
            'temperature': prompt_manager.temperature,
            "max_tokens": min(MAX_FORMAL_PROOF_LEN, prompt_manager.max_sequence_len - max_batch_length),
            "stop_sequences": prompt_manager.stop_generation(),
        })
        batched_subgoal_proof = responses.json()["choices"][0]["text"]
        batched_subgoal_proof = [prompt_manager.post_process(subgoal_proof.strip()) for subgoal_proof in batched_subgoal_proof]
        save_results3(batched_path, batched_id, batched_informal_statement, batched_informal_proof, batched_subgoal_proof)

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start_idx", type=int, default=0)
    parser.add_argument("--end_idx", type=int, default=10000)
    parser.add_argument("--endpoint_address", type=str, default="")
    parser.add_argument("--prompt_manager_name", type=str, default="InformalToFormalPromptManager")
    parser.add_argument("--dump_path", type=str, default="")
    parser.add_argument("--num_samples", type=int, default=1)
    parser.add_argument("--temperature", type=float, default=0.4)
    parser.add_argument("--solved_problems_path", type=str, default="")
    parser.add_argument("--phrase", type=str, default="statement_and_proof_generation")
    args = parser.parse_args()

    if args.phrase == "statement_and_proof_generation":
        statement_and_proof_generation(args)
    elif args.phrase == "statement_and_proof_generation_batched":
        statement_and_proof_generation_batched(args)
    elif args.phrase == "statement_validation":
        statement_validation(args)
    elif args.phrase == "statement_validation_batched":
        statement_validation_batched(args)
    elif args.phrase == "subgoal_generation_batched":
        subgoal_generation_batched(args)