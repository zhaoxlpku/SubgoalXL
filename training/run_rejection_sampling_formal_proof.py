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

def parse_arguments():
    parser = argparse.ArgumentParser(description="Schedule proof checker tasks.")
    parser.add_argument("--exp_name", type=str, required=True)
    parser.add_argument("--num_workers", type=int, required=True)
    parser.add_argument("--endpoint_manager_name", type=str, required=True)
    parser.add_argument("--model_name_or_path", type=str, required=True)
    parser.add_argument("--prompt_manager_name", type=str, required=True)
    parser.add_argument("--max_response_len", type=int, default=1024)
    parser.add_argument("--num_models", type=int, required=True)
    parser.add_argument("--model_index", type=int, required=True)
    parser.add_argument("--temperature", type=float, required=True)
    parser.add_argument("--data_dir", type=str, required=True)
    return parser.parse_args()

def run(exp_name, num_workers, endpoint_manager_name, model_name_or_path, prompt_manager_name, max_response_len, **kwargs):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dump_path = f"{repo_root}/outputs/rejection_sampling/{exp_name}"
    os.makedirs(dump_path, exist_ok=True)
    
    prompt_manager_class = import_class(prompt_manager_name, "training.rejection_sampling_formal_proof")
    prompt_manager = prompt_manager_class(max_response_len=max_response_len, **kwargs)    
    start_indices = prompt_manager.distribute_tasks_to_workers(directory=dump_path, num_workers=num_workers)
    true_num_endpoints = len(start_indices)
    
    endpoint_manager_class = import_class(endpoint_manager_name, "utils.endpoint_utils")
    endpoint_manager = endpoint_manager_class(
        model_name_or_path=model_name_or_path,
        pef="/import/snvm-sc-podscratch4/xueliangz/pef/llama3_8b_pef",
        cache_dir="/import/snvm-sc-scratch2/xueliangz/cache",
        num_endpoints=true_num_endpoints,
        virtual_env="/import/snvm-sc-podscratch4/xueliangz/batched_inference/software/sambaflow/apps/modelzoo/tests/venv/",
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
            "python", "rejection_sampling_formal_proof.py",
            "--start_idx", str(start_index), 
            "--end_idx", str(end_index),
            "--endpoint_address", endpoint_address, 
            "--prompt_manager_name", prompt_manager_name, 
            "--max_response_len", str(max_response_len), 
            "--dump_path", dump_path, 
            "--num_models", str(kwargs.get("num_models", 4)), 
            "--model_index", str(kwargs.get("model_index", 0)), 
            "--temperature", str(kwargs.get("temperature", 0.6)), 
            "--data_dir", str(kwargs.get("data_dir", "")), 
        ]
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

if __name__ == "__main__":
    args = parse_arguments()
    run(
        exp_name=args.exp_name, 
        num_workers=args.num_workers, 
        endpoint_manager_name=args.endpoint_manager_name, 
        model_name_or_path=args.model_name_or_path, 
        prompt_manager_name=args.prompt_manager_name, 
        max_response_len=args.max_response_len,
        num_models=args.num_models,
        model_index=args.model_index,
        temperature=args.temperature,
        data_dir=args.data_dir,
    )