import json

from tqdm import tqdm


def is_correct(eval_obj):
    success = eval_obj["success"]
    if any(["sorry" in step["step"] or "oops" in step["step"] for step in eval_obj["step_results"][1:]]):
        success = False
    num_steps = len([step["step"] for step in eval_obj["step_results"][1:]])
    if num_steps < 2:
        success = False
    return success

if __name__ == "__main__":
    # split = "validation"
    split = "test"
    rounds = [0, 1, 2, 3]
    exp_types = ["without_informal", "with_informal"]
    model_types = ["v1", "v2", "v3", "v4"]

    correct_ids = set()
    all_ids = set()
    for round_idx in tqdm(rounds):
        for exp_type in tqdm(exp_types):
            for model_type in tqdm(model_types):
                with open(f"results/{split}_round_{round_idx}_{exp_type}_model_{model_type}.jsonl", encoding="utf-8") as f:
                    for line in f.readlines():
                        json_obj = json.loads(line)
                        if (json_obj["isa2021"] is not None and is_correct(json_obj["isa2021"])) or (json_obj["isa2022"] is not None and is_correct(json_obj["isa2022"])):
                            correct_ids.add(json_obj["id"])
                        all_ids.add(json_obj["id"])
    print(correct_ids)
    print(len(correct_ids) / len(all_ids), f"({len(correct_ids)} / {len(all_ids)})")
