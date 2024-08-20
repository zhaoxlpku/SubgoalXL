
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

def run(exp_name, num_workers, endpoint_manager_name, model_name_or_path, prompt_manager_name, data_path, max_response_len, num_samples, temperature):
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dump_path = f"{repo_root}/outputs/formal_to_informal/{exp_name}"
    os.makedirs(dump_path, exist_ok=True)
    
    prompt_manager_class = import_class(prompt_manager_name, "data_preparation.auto_formal_to_informal")
    prompt_manager = prompt_manager_class(data_path=data_path, model_name_or_path=model_name_or_path, max_response_len=max_response_len, num_samples=num_samples, temperature=temperature)
    start_indices = prompt_manager.distribute_tasks_to_workers(directory=dump_path, num_workers=num_workers)
    true_num_endpoints = len(start_indices)
    
    endpoint_manager_class = import_class(endpoint_manager_name, "utils.endpoint_utils")
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
            "python", "auto_formal_to_informal.py",
            "--start_idx", str(start_index), 
            "--end_idx", str(end_index),
            "--data_path", data_path,
            "--model_name_or_path", model_name_or_path,
            "--endpoint_address", endpoint_address,
            "--prompt_manager_name", prompt_manager_name, 
            "--dump_path", dump_path, 
            "--max_response_len", str(max_response_len),
            "--num_samples", str(num_samples),
            "--temperature", str(temperature),
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

def main():
    parser = argparse.ArgumentParser(description="Run formal to informal conversion")
    parser.add_argument('--exp_name', type=str, help="Experiment name")
    parser.add_argument('--num_workers', type=int, default=2, help="Number of workers")
    parser.add_argument('--endpoint_manager_name', type=str, default="BatchedEndpointManager", help="Endpoint manager name")
    parser.add_argument('--model_name_or_path', type=str, required=True, help="Path to the model")
    parser.add_argument('--prompt_manager_name', type=str, default="FormalToInformalLlama3FewshotPromptManager", help="Prompt manager name")
    parser.add_argument('--data_path', type=str, required=True, help="Path to the data file")
    parser.add_argument('--max_response_len', type=int, default=1024, help="Maximum response length")
    parser.add_argument('--num_samples', type=int, default=1, help="Number of samples")
    parser.add_argument('--temperature', type=float, default=0.2, help="Temperature for sampling")

    args = parser.parse_args()

    run(exp_name=args.exp_name, num_workers=args.num_workers, endpoint_manager_name=args.endpoint_manager_name, model_name_or_path=args.model_name_or_path, prompt_manager_name=args.prompt_manager_name, data_path=args.data_path, max_response_len=args.max_response_len, num_samples=args.num_samples, temperature=args.temperature)

if __name__ == "__main__":
    main()