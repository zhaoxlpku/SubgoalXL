import argparse
import json
import os

import numpy as np
from tqdm import tqdm
from transformers import AutoTokenizer


# https://arxiv.org/abs/2309.06657
def conduct_rejection_sampling(response_candidates, response_rewards, num_samples=1, beta=0.5):
    candidates = {c: r for c, r in zip(response_candidates, response_rewards)}
    accepted = []
    while len(accepted) < num_samples:
        max_reward = max(candidates.values())
        to_remove = []
        for c, r in candidates.items():
            u = np.random.uniform()
            if u >= np.exp((r - max_reward) / beta):
                continue
            accepted.append(c)
            to_remove.append(c)
            if len(accepted) == num_samples:
                break
        for c in to_remove:
            candidates.pop(c)
    return accepted

def process_files(data_dir, score_dir, output_dir, task, num_samples, beta):
    os.makedirs(output_dir, exist_ok=True)
    
    tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B")

    def num_tokens_from_string(string: str) -> int:
        return len(tokenizer.encode(string))

    id_to_data = {}
    for file in tqdm(os.listdir(score_dir)):
        with open(os.path.join(score_dir, file), encoding="utf-8") as f:
            data = json.loads(f.read().strip())
            filename = data["filename"].split(".")[0]
            task_id = "-".join(filename.split("-")[:2])
            normalized_score = data["log_prob"] / num_tokens_from_string(data["completion"])
            if task_id not in id_to_data:
                id_to_data[task_id] = {
                    "candidates": [],
                    "rewards": [],
                }
            id_to_data[task_id]["candidates"].append(filename)
            id_to_data[task_id]["rewards"].append(normalized_score)
    
    for task_id in tqdm(id_to_data.keys()):
        accepted = conduct_rejection_sampling(
            response_candidates=id_to_data[task_id]["candidates"],
            response_rewards=id_to_data[task_id]["rewards"],
            num_samples=num_samples,
            beta=beta,
        )
        for filename in accepted:
            with open(os.path.join(data_dir, f"{filename}.jsonl"), encoding="utf-8") as f:
                data_to_save = json.loads(f.read().strip())
            if task == "formal_statement":
                data_to_save["formal_proof"] = "sorry"
            
            with open(os.path.join(output_dir, f"{filename}.jsonl"), "w", encoding="utf-8") as f:
                f.write(json.dumps(data_to_save) + "\n")
            
if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--data_dir', type=str, required=True)
    parser.add_argument('--score_dir', type=str, required=True)
    parser.add_argument('--output_dir', type=str, required=True)
    parser.add_argument('--task', type=str, required=True)
    parser.add_argument('--num_samples', type=int, default=1)
    parser.add_argument('--beta', type=float, default=0.5)

    args = parser.parse_args()

    process_files(args.data_dir, args.score_dir, args.output_dir, args.task, args.num_samples, args.beta)
