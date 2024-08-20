import argparse
import importlib
import os
import subprocess
import time

import psutil


def import_class(class_name, module_name):
    module = importlib.import_module(module_name)
    class_obj = getattr(module, class_name)
    return class_obj

def get_pef(model_name_or_path):
    if model_name_or_path == "/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base":
        return "/import/snvm-sc-scratch2/xueliangz/Data/pef_data/deepseek_math/inference_ts_1socket/generative_hook_216471_17_41_38.pef"
    elif model_name_or_path == "/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B-Instruct":
        return "/import/snvm-sc-podscratch4/xueliangz/pef/llama3_8b_pef"
    elif model_name_or_path == "/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B":
        return "/import/snvm-sc-podscratch4/xueliangz/pef/llama3_8b_pef"
    else:
        raise ValueError

def get_virtual_env(model_name_or_path):
    if model_name_or_path == "/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base":
        return "/import/snvm-sc-scratch2/xueliangz/software/sambaflow/apps/nlp/transformers_on_rdu/llama_venv/venv/"
    elif model_name_or_path == "/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B-Instruct":
        return "/import/snvm-sc-podscratch4/xueliangz/batched_inference/software/sambaflow/apps/modelzoo/tests/venv/"
    elif model_name_or_path == "/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B":
        return "/import/snvm-sc-podscratch4/xueliangz/batched_inference/software/sambaflow/apps/modelzoo/tests/venv/"
    else:
        raise ValueError



def run(exp_name, num_workers, endpoint_manager_name, model_name_or_path, prompt_manager_name, num_samples, temperature, solved_problems_path=""):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dump_path = f"{repo_root}/outputs/autoformalization/{exp_name}"
    os.makedirs(dump_path, exist_ok=True)
    
    prompt_manager_class = import_class(prompt_manager_name, "data_preparation.autoformalization_generation")
    prompt_manager = prompt_manager_class(num_samples=num_samples, temperature=temperature, solved_problems_path=solved_problems_path)
    start_indices = prompt_manager.distribute_tasks_to_workers(directory=dump_path, num_workers=num_workers)
    true_num_endpoints = len(start_indices)
    
    endpoint_manager_class = import_class(endpoint_manager_name, "endpoint_utils")
    endpoint_manager = endpoint_manager_class(
        model_name_or_path=model_name_or_path,
        pef=get_pef(model_name_or_path),
        cache_dir="/import/snvm-sc-scratch2/xueliangz/cache",
        num_endpoints=true_num_endpoints,
        virtual_env=get_virtual_env(model_name_or_path),
    )
    
    all_endpoints = endpoint_manager.start_endpoints()
    if type(all_endpoints) == dict:
        all_endpoints = list(all_endpoints.items())
    
    assert len(all_endpoints) == len(start_indices)
    jobs = []
    for i, start_index in enumerate(start_indices):
        end_index = start_indices[i+1] if i + 1 < len(start_indices) else prompt_manager.get_num_prompts()
        endpoint_address, endpoint_job = all_endpoints[i]
        cmd = [
            "python", "autoformalization_generation.py",
            "--start_idx", str(start_index), 
            "--end_idx", str(end_index),
            "--endpoint_address", endpoint_address,
            "--prompt_manager_name", prompt_manager_name, 
            "--dump_path", dump_path, 
            "--num_samples", str(num_samples),
            "--temperature", str(temperature),
            "--phrase", "statement_and_proof_generation_batched" if "Batched" in endpoint_manager_name else "statement_and_proof_generation" 
        ]
        if solved_problems_path:
            cmd += ["--solved_problems_path", solved_problems_path]
        sub = subprocess.Popen(cmd).pid
        print("start process #{}...".format(sub))
        jobs.append(sub)

    try:
        print("dump_path: {}".format(dump_path))
        time.sleep(300)
        while True:
            if prompt_manager.are_all_workers_finished(directory=dump_path):
                break
            else:
                time.sleep(300)
    except KeyboardInterrupt:
        for job in jobs:
            try:
                parent = psutil.Process(job)
                children = parent.children(recursive=True)
                for process in children:
                    process.kill()
                parent.kill()
            except psutil.NoSuchProcess:
                pass
    endpoint_manager.stop_endpoints()
    print("dump_path: {}".format(dump_path))

def run_statement_validation(exp_name, num_workers, endpoint_manager_name, model_name_or_path, prompt_manager_name, num_samples, temperature, solved_problems_path=""):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dump_path = f"{repo_root}/outputs/statement_validation/{exp_name}"
    os.makedirs(dump_path, exist_ok=True)
    
    prompt_manager_class = import_class(prompt_manager_name, "data_preparation.autoformalization_generation")
    prompt_manager = prompt_manager_class(num_samples=num_samples, temperature=temperature, solved_problems_path=solved_problems_path)
    start_indices = prompt_manager.distribute_tasks_to_workers(directory=dump_path, num_workers=num_workers)
    true_num_endpoints = len(start_indices)
    
    endpoint_manager_class = import_class(endpoint_manager_name, "endpoint_utils")
    endpoint_manager = endpoint_manager_class(
        model_name_or_path=model_name_or_path,
        pef=get_pef(model_name_or_path),
        cache_dir="/import/snvm-sc-scratch2/xueliangz/cache",
        num_endpoints=true_num_endpoints,
        virtual_env=get_virtual_env(model_name_or_path),
    )
    
    all_endpoints = endpoint_manager.start_endpoints()
    if type(all_endpoints) == dict:
        all_endpoints = list(all_endpoints.items())
    
    assert len(all_endpoints) == len(start_indices)
    jobs = []
    for i, start_index in enumerate(start_indices):
        end_index = start_indices[i+1] if i + 1 < len(start_indices) else prompt_manager.get_num_prompts()
        endpoint_address, endpoint_job = all_endpoints[i]
        cmd = [
            "python", "autoformalization_generation.py",
            "--start_idx", str(start_index), 
            "--end_idx", str(end_index),
            "--endpoint_address", endpoint_address,
            "--prompt_manager_name", prompt_manager_name, 
            "--dump_path", dump_path, 
            "--num_samples", str(num_samples),
            "--temperature", str(temperature),
            "--phrase", "statement_validation_batched" if "Batched" in endpoint_manager_name else "statement_validation" 
        ]
        if solved_problems_path:
            cmd += ["--solved_problems_path", solved_problems_path]
        sub = subprocess.Popen(cmd).pid
        print("start process #{}...".format(sub))
        jobs.append(sub)

    try:
        print("dump_path: {}".format(dump_path))
        time.sleep(300)
        while True:
            if prompt_manager.are_all_workers_finished(directory=dump_path):
                break
            else:
                time.sleep(300)
    except KeyboardInterrupt:
        for job in jobs:
            try:
                parent = psutil.Process(job)
                children = parent.children(recursive=True)
                for process in children:
                    process.kill()
                parent.kill()
            except psutil.NoSuchProcess:
                pass
    endpoint_manager.stop_endpoints()
    print("dump_path: {}".format(dump_path))

def run_subgoal_proof_generation(exp_name, num_workers, endpoint_manager_name, model_name_or_path, prompt_manager_name, num_samples, temperature, solved_problems_path=""):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dump_path = f"{repo_root}/outputs/subgoal_proof/{exp_name}"
    os.makedirs(dump_path, exist_ok=True)
    
    prompt_manager_class = import_class(prompt_manager_name, "data_preparation.autoformalization_generation")
    prompt_manager = prompt_manager_class(num_samples=num_samples, temperature=temperature, solved_problems_path=solved_problems_path)
    start_indices = prompt_manager.distribute_tasks_to_workers(directory=dump_path, num_workers=num_workers)
    true_num_endpoints = len(start_indices)
    
    endpoint_manager_class = import_class(endpoint_manager_name, "endpoint_utils")
    endpoint_manager = endpoint_manager_class(
        model_name_or_path=model_name_or_path,
        pef=get_pef(model_name_or_path),
        cache_dir="/import/snvm-sc-scratch2/xueliangz/cache",
        num_endpoints=true_num_endpoints,
        virtual_env=get_virtual_env(model_name_or_path),
    )
    
    all_endpoints = endpoint_manager.start_endpoints()
    if type(all_endpoints) == dict:
        all_endpoints = list(all_endpoints.items())
    
    assert len(all_endpoints) == len(start_indices)
    jobs = []
    for i, start_index in enumerate(start_indices):
        end_index = start_indices[i+1] if i + 1 < len(start_indices) else prompt_manager.get_num_prompts()
        endpoint_address, endpoint_job = all_endpoints[i]
        cmd = [
            "python", "autoformalization_generation.py",
            "--start_idx", str(start_index), 
            "--end_idx", str(end_index),
            "--endpoint_address", endpoint_address,
            "--prompt_manager_name", prompt_manager_name, 
            "--dump_path", dump_path, 
            "--num_samples", str(num_samples),
            "--temperature", str(temperature),
            "--phrase", "subgoal_generation_batched"
        ]
        if solved_problems_path:
            cmd += ["--solved_problems_path", solved_problems_path]
        sub = subprocess.Popen(cmd).pid
        print("start process #{}...".format(sub))
        jobs.append(sub)

    try:
        print("dump_path: {}".format(dump_path))
        time.sleep(300)
        while True:
            if prompt_manager.are_all_workers_finished(directory=dump_path):
                break
            else:
                time.sleep(300)
    except KeyboardInterrupt:
        for job in jobs:
            try:
                parent = psutil.Process(job)
                children = parent.children(recursive=True)
                for process in children:
                    process.kill()
                parent.kill()
            except psutil.NoSuchProcess:
                pass
    endpoint_manager.stop_endpoints()
    print("dump_path: {}".format(dump_path))

def main():
    parser = argparse.ArgumentParser(description="Run a specific task")
    parser.add_argument('--task', type=str, required=True, choices=['autoformalization', 'statement_validation', 'subgoal'], help="Task to perform: 'autoformalization', 'statement_validation', or 'subgoal'")
    parser.add_argument('--exp_name', type=str, required=True, help="Experiment name")
    parser.add_argument('--num_workers', type=int, default=4, help="Number of workers")
    parser.add_argument('--endpoint_manager_name', type=str, default="BatchedEndpointManager", help="Endpoint manager name")
    parser.add_argument('--model_name_or_path', type=str, required=True, help="Path to the model")
    parser.add_argument('--prompt_manager_name', type=str, required=True, help="Prompt manager name")
    parser.add_argument('--num_samples', type=int, default=64, help="Number of samples")
    parser.add_argument('--temperature', type=float, default=0.6, help="Temperature for sampling")
    parser.add_argument('--solved_problems_path', type=str, default="", help="Path to the solved problems file")

    args = parser.parse_args()

    if args.task == 'autoformalization':
        run(
            exp_name=args.exp_name,
            num_workers=args.num_workers,
            endpoint_manager_name=args.endpoint_manager_name,
            model_name_or_path=args.model_name_or_path,
            prompt_manager_name=args.prompt_manager_name,
            num_samples=args.num_samples,
            temperature=args.temperature,
            solved_problems_path=args.solved_problems_path
        )

    elif args.task == 'statement_validation':
        run_statement_validation(
            exp_name=args.exp_name,
            num_workers=args.num_workers,
            endpoint_manager_name=args.endpoint_manager_name,
            model_name_or_path=args.model_name_or_path,
            prompt_manager_name=args.prompt_manager_name,
            num_samples=args.num_samples,
            temperature=args.temperature,
            solved_problems_path=args.solved_problems_path
        )

    elif args.task == 'subgoal':
        run_subgoal_proof_generation(
            exp_name=args.exp_name,
            num_workers=args.num_workers,
            endpoint_manager_name=args.endpoint_manager_name,
            model_name_or_path=args.model_name_or_path,
            prompt_manager_name=args.prompt_manager_name,
            num_samples=args.num_samples,
            temperature=args.temperature,
            solved_problems_path=args.solved_problems_path
        )

if __name__ == "__main__":
    main()
