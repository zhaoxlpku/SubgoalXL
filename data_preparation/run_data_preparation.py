import argparse
import json
import os
import random
import re
from collections import Counter

import h5py
from tqdm import tqdm


class Prompter_Llama3_v1:
    def __init__(self):
        self.max_sequence_len = 8192

    def get_prompt(self, informal_statement, formal_statement, data_type=None):
        prompt = f"### Problem:\n{informal_statement}\n\n### Proof:\n{formal_statement}"
        return prompt

class Prompter_Llama3_v2:
    def __init__(self):
        self.instructions = [
            "Develop formal proofs using Isabelle, leveraging auxiliary tools such as Sledgehammer to enhance the proving process.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n\n### Output",
            "Utilize Isabelle for the systematic verification of theorem proofs, employing Sledgehammer as a supplementary tool. Approach the problem in a step-by-step manner.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}",
        ]
        self.max_sequence_len = 8192

    def get_prompt(self, informal_statement, formal_statement, data_type="afp"):
        if data_type == "std" or data_type == "afp":
            template = self.instructions[0]
        elif data_type == "other":
            template = self.instructions[1]
        else:
            raise ValueError
        prompt = template.format(informal_statement, formal_statement)
        return prompt

def drop_sample(p):
    """Return 1 with probability p and 0 with probability 1-p."""
    return 1 if random.random() < p else 0

def extract_statement_and_proof(prediction):
    if "Informal:" in prediction:
        prediction = prediction.split("Informal:")[1].strip()
    else:
        prediction = prediction.strip()

    if (not prediction.startswith("(*")) or (not prediction.endswith("*)")):
        return None, None
    prediction = prediction.split("(*")[1].split("*)")[0].strip()
    if "### Problem" not in prediction or "### Solution" not in prediction:
        return None, None
    informal_statement = prediction.split("### Problem")[1].split("### Solution")[0].strip()
    informal_proof = prediction.split("### Solution")[1].strip()
    return informal_statement, informal_proof

def delete_comments(formal_proof):
    lines = [line.strip() for line in formal_proof.split("\n")]
    lines_to_delete = []
    to_delete = False
    for i, line in enumerate(lines):
        if line.startswith("(*"):
            to_delete = True
        if to_delete:
            lines_to_delete.append(i)
        if line.endswith("*)"):
            to_delete = False
    lines = [line for i, line in enumerate(lines) if i not in lines_to_delete]
    return "\n".join(lines)

def tokenize(string):
    return set(delete_comments(string).split())

def filter_strings(strings, threshold=0.75):
    def word_overlap(s1, s2):
        return len(s1.intersection(s2)) / float(len(s1.union(s2)))

    tokenized_strings = [tokenize(s["formal_proof"] if isinstance(s, dict) else s) for s in strings]  # s["formal_proof"]
    filtered_indices = set(range(len(strings)))
    for i in range(len(strings)):
        for j in range(i + 1, len(strings)):
            if i in filtered_indices and j in filtered_indices:
                overlap = word_overlap(tokenized_strings[i], tokenized_strings[j])
                if overlap > threshold:
                    filtered_indices.remove(j)
    return [strings[i] for i in filtered_indices]

def is_successful_case(evaluation_data):
    is_success = evaluation_data["success"]
    if any(["sorry" in step["step"] or "oops" in step["step"] for step in evaluation_data["step_results"][1:]]):
        is_success = False
    num_steps = len([step["step"] for step in evaluation_data["step_results"][1:]])
    if num_steps < 2:
        is_success = False
    return is_success

def is_valid_case(validation_data):
    # if validation_data["result"] or (not validation_data["result"] and  validation_data["message"] == "Single-lined or improperly formatted statements invalidate cases.")
    return True if validation_data["result"] else False

def get_num_steps(evaluation_data):
    num_steps = len([step["step"] for step in evaluation_data["step_results"][1:]])
    return num_steps

def load_synthesized_data(autoformalization_dir):
    validation_dir = autoformalization_dir.split("/")[:-2] + ["statement_validation"] + autoformalization_dir.split("/")[-1:]
    evaluation_dir = autoformalization_dir.split("/")[:-2] + ["evaluation"] + autoformalization_dir.split("/")[-1:]

    data = {}  # id -> []
    for file in tqdm(os.listdir(autoformalization_dir)):
        autoformalization_path = os.path.join(autoformalization_dir, file)
        validation_path = os.path.join(validation_dir, file)
        evaluation_path = os.path.join(evaluation_dir, file)

        with open(autoformalization_path, encoding="utf-8") as f:
            autoformalization_data = json.loads(f.read().strip())
            task_id = autoformalization_data["id"]
            informal_statement = autoformalization_data["informal_statement"]
            informal_proof = autoformalization_data["informal_proof"]
            formal_statement = autoformalization_data["formal_statement"]
            formal_proof = autoformalization_data["formal_proof"]

        if not os.path.exists(validation_path): continue
        with open(validation_path, encoding="utf-8") as f:
            try:
                validation_data = json.loads(f.read().strip())
            except json.decoder.JSONDecodeError:
                print(evaluation_path)
                continue

        if not os.path.exists(evaluation_path): continue
        with open(evaluation_path, encoding="utf-8") as f:
            try:
                evaluation_data = json.loads(f.read().strip())
            except json.decoder.JSONDecodeError:
                print(evaluation_path)
                continue

        is_successful = is_successful_case(evaluation_data)
        is_valid = is_valid_case(validation_data)
        num_steps = get_num_steps(evaluation_data)

        if task_id not in data:
            data[task_id] = []

        if formal_statement is not None and formal_proof is not None and formal_statement.strip() != "" and formal_proof.strip() != "":
            data[task_id].append({
                "informal_statement": informal_statement,
                "informal_proof": informal_proof,
                "formal_statement": formal_statement,
                "formal_proof": formal_proof,
                "is_successful": is_successful,
                "is_valid": is_valid,
                "num_steps": num_steps,
            })
    return data

def merge_dict(dict1, dict2):
    merged_dict = {}
    all_keys = dict1.keys() | dict2.keys()
    for key in all_keys:
        merged_dict[key] = dict1.get(key, []) + dict2.get(key, [])
    return merged_dict

def load_afp_data(afp_prediction_dir, length_filtering=False, filtering_config=[(2, 0.8), (3, 0.6), (4, 0.4)]):  # afp_ratio: percentage of afp data that should be kept
    current_dir = os.path.dirname(os.path.abspath(__file__))
    repo_root = os.path.dirname(current_dir)
    dataset = h5py.File(f"{repo_root}/datasets/afp/afp_train_154k.hdf5")
    groups = sorted(list(dataset.keys()), key=lambda x: int(x))
    assert len(groups) == int(groups[-1]) + 1

    data = {}
    for i in tqdm(len(groups)):
        task_name = f"afp-{i}"
        grp = groups[i]
        meta_data = {
            "id": dataset[grp]["id"][()].decode(),
            "formal_statement": dataset[grp]["formal_statement"][()].decode(),
            "formal_proof": dataset[grp]["formal_proof"][()].decode(),
        }
        formal_statement = meta_data["formal_statement"]
        formal_proof = meta_data["formal_proof"]
        with open(f"{afp_prediction_dir}/{task_name}.jsonl", encoding="utf-8") as f:
            prediction = json.loads(f.read().strip())["prediction"]
        informal_statement, informal_proof = extract_statement_and_proof(prediction)
        original_name = task_name
        if original_name not in data:
            data[original_name] = []
        if informal_statement is not None and informal_proof is not None:
            data[original_name].append({
                "informal_statement": informal_statement,
                "informal_proof": informal_proof,
                "formal_statement": formal_statement,
                "formal_proof": formal_proof,
            })
    dataset = []
    for task_name in tqdm(data, total=len(data)):
        tuples = data[task_name]
        if len(tuples) == 0:
            continue
        assert len(tuples) == 1
        if not length_filtering:
            dataset.append(tuples[0])
        else:
            formal_proof = tuples[0]["formal_proof"]
            num_steps = len(formal_proof.strip().split("\n"))
            is_skip = False
            for min_step, drop_rate in filtering_config:
                if num_steps < min_step:
                    if drop_sample(drop_rate):
                        is_skip = True
                        break
            if is_skip:
                continue
            dataset.append(tuples[0])
    print(f"Loaded {len(dataset)} examples from AFP.")
    return dataset

def load_std_data(std_prediction_dir, length_filtering=False, filtering_config=[(2, 0.8), (3, 0.6), (4, 0.4)]):
    data = {}
    for file in os.listdir(std_prediction_dir):
        with open(os.path.join(std_prediction_dir, file), encoding="utf-8") as f:
            json_obj = json.loads(f.read().strip())
            if json_obj["informal_statement"] is None or json_obj["informal_proof"] is None:
                continue
            data[json_obj["id"]] = {
                "informal_statement": json_obj["informal_statement"],
                "predictions": [json_obj["informal_proof"]],
                "formal_statement": json_obj["formal_statement"],
                "formal_proof": json_obj["formal_proof"],
                "id": json_obj["id"],
            }

    dataset = []
    for task_id, json_obj in data.items():
        predictions = json_obj["predictions"]
        if len(predictions) > 1:
            predictions = filter_strings(predictions)
        for informal_proof in predictions:
            if not length_filtering:
                dataset.append({
                    "informal_statement": json_obj["informal_statement"],
                    "informal_proof": informal_proof,
                    "formal_statement": json_obj["formal_statement"],
                    "formal_proof": json_obj["formal_proof"],
                })
            else:
                formal_proof = json_obj["formal_proof"]
                num_steps = len(formal_proof.strip().split("\n"))
                is_skip = False
                for min_step, drop_rate in filtering_config:
                    if num_steps < min_step:
                        if drop_sample(drop_rate):
                            is_skip = True
                            break
                if is_skip:
                    continue
                dataset.append({
                    "informal_statement": json_obj["informal_statement"],
                    "informal_proof": informal_proof,
                    "formal_statement": json_obj["formal_statement"],
                    "formal_proof": json_obj["formal_proof"],
                })
    print(f"Loaded {len(dataset)} examples from HOL-STD.")
    return dataset

def load_solved_problems(prediction_dirs):
    total_data = {}
    for prediction_dir in prediction_dirs:
        data = load_synthesized_data(prediction_dir)
        total_data = merge_dict(total_data, data)

    solved = {}
    for task_id in tqdm(total_data, total=len(total_data)):
        tuples = [tp for tp in total_data[task_id] if tp["is_successful"] and tp["is_valid"]]
        solved[task_id] = {
            "id": task_id,
            "informal_statement": total_data[task_id][0]["informal_statement"],
            "informal_proof": total_data[task_id][0]["informal_proof"],
            "verified_proofs": [
                {
                    "formal_statement": tp["formal_statement"],
                    "formal_proof": tp["formal_proof"],
                } for tp in tuples
            ]
        }
    return solved

def load_math_data(prediction_dirs, subgoal_proof=False):
    solved = load_solved_problems(prediction_dirs=prediction_dirs)

    dataset = []
    for task_id in solved:
        json_obj = solved[task_id]
        verified_proofs = json_obj["verified_proofs"]
        if len(verified_proofs) > 1:
            verified_proofs = filter_strings(verified_proofs)
        for proof in verified_proofs:
            dataset.append({
                "informal_statement": json_obj["informal_statement"],
                "informal_proof": extract_comments(proof["formal_proof"]) if subgoal_proof else json_obj["informal_proof"],
                "formal_statement": proof["formal_statement"],
                "formal_proof": proof["formal_proof"],
            })

    print(f"Loaded {len(dataset)} examples from Math Competitions.")
    return dataset


def load_competition_data(prediction_dirs, subgoal_proof=False):
    solved = load_solved_problems(prediction_dirs=prediction_dirs)

    dataset = []
    for task_id in solved:
        json_obj = solved[task_id]
        verified_proofs = json_obj["verified_proofs"]
        if len(verified_proofs) > 1:
            verified_proofs = filter_strings(verified_proofs)
        dataset.extend([{
            "informal_statement": json_obj["informal_statement"],
            "informal_proof": extract_comments(proof["formal_proof"]) if subgoal_proof else json_obj["informal_proof"],
            "formal_statement": proof["formal_statement"],
            "formal_proof": proof["formal_proof"],
        } for proof in verified_proofs])
    print(f"Loaded {len(dataset)} examples from Math Competitions.")
    return dataset

def extract_comments(formal_proof):
    """Extract comments from the formal proof enclosed by '(*' and '*)'."""
    comments = re.findall(r'\(\*.*?\*\)', formal_proof, re.DOTALL)
    # Remove the comment delimiters "(*" and "*)"
    comments = [comment[2:-2].strip() for comment in comments]
    return comments

def compare_proofs(informal_proof, formal_proof, data_type="afp"):
    """Compare informal proof with comments in formal proof and return the appropriate proof."""

    def word_overlap(informal_proof, comments):
        """Calculate the overlap percentage of words between informal proof and comments."""
        informal_words = informal_proof.split()
        informal_count = Counter(informal_words)

        comments_words = ' '.join(comments).split()
        comments_count = Counter(comments_words)

        overlap = sum((informal_count & comments_count).values())
        total_words = sum(informal_count.values())

        overlap_percentage = (overlap / total_words) * 100 if total_words else 0
        return overlap_percentage

    comments = extract_comments(formal_proof)
    overlap_percentage = word_overlap(informal_proof, comments)

    if (data_type == "other" and overlap_percentage > 85) or (data_type != "other"):
        return f"(*{informal_proof}*)\n{formal_proof}"
    else:
        return formal_proof

def process_files(afp_prediction_dir, std_prediction_dir, math_prediction_dirs, aime_prediction_dirs, output_path, task):
    if task == "formal_proof_v1:orig":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=False)
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=False)
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v1()
    elif task == "formal_proof_v1:filter":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=True)
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=True)
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v1()
    elif task == "formal_proof_v1:filter2":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=True, filtering_config=[(2, 0.9), (3, 0.8), (4, 0.7), (5, 0.6), (6, 0.5), (7, 0.4), (8, 0.3), (9, 0.2), (10, 0.1)])
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=True, filtering_config=[(2, 0.9), (3, 0.8), (4, 0.7), (5, 0.6), (6, 0.5), (7, 0.4), (8, 0.3), (9, 0.2), (10, 0.1)])
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v1()
    elif task == "formal_proof_v2:orig":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=False)
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=False)
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v2()
    elif task == "formal_proof_v2:filter":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=True)
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir,  length_filtering=True)
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v2()
    elif task == "formal_proof_v2:filter2":
        afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=True, filtering_config=[(2, 0.9), (3, 0.8), (4, 0.7), (5, 0.6), (6, 0.5), (7, 0.4), (8, 0.3), (9, 0.2), (10, 0.1)])
        std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=True, filtering_config=[(2, 0.9), (3, 0.8), (4, 0.7), (5, 0.6), (6, 0.5), (7, 0.4), (8, 0.3), (9, 0.2), (10, 0.1)])
        math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
        aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs)
        prompter = Prompter_Llama3_v2()
    else:
        raise ValueError

    writer = open(output_path, "w", encoding="utf-8")
    count = 0
    for json_obj in tqdm(afp_dataset):
        completion = compare_proofs(json_obj["informal_proof"].strip(), json_obj["formal_proof"].strip(), "afp")
        prompt = prompter.get_prompt(json_obj["informal_statement"].strip(), json_obj["formal_statement"].strip(), data_type="afp")
        if count < 3:
            print(f"# {count}:")
            print(prompt)
            print("-----------------")
            print(completion)
            print("=================")
        writer.write(json.dumps({
            "prompt": prompt,
            "completion": completion,
        }) + "\n")
        count += 1

    count = 0
    for json_obj in tqdm(std_dataset):
        completion = compare_proofs(json_obj["informal_proof"].strip(), json_obj["formal_proof"].strip(), "std")
        prompt = prompter.get_prompt(json_obj["informal_statement"].strip(), json_obj["formal_statement"].strip(), data_type="std")
        if count < 3:
            print(f"# {count}:")
            print(prompt)
            print("-----------------")
            print(completion)
            print("=================")
        writer.write(json.dumps({
            "prompt": prompt,
            "completion": completion,
        }) + "\n")
        count += 1

    count = 0
    for json_obj in tqdm(math_dataset):
        completion = compare_proofs(json_obj["informal_proof"].strip(), json_obj["formal_proof"].strip(), "other")
        prompt = prompter.get_prompt(json_obj["informal_statement"].strip(), json_obj["formal_statement"].strip(), data_type="other")
        if count < 3:
            print(f"# {count}:")
            print(prompt)
            print("-----------------")
            print(completion)
            print("=================")
        writer.write(json.dumps({
            "prompt": prompt,
            "completion": completion,
        }) + "\n")
        count += 1

    count = 0
    for json_obj in tqdm(aime_dataset):
        completion = compare_proofs(json_obj["informal_proof"].strip(), json_obj["formal_proof"].strip(), "other")
        prompt = prompter.get_prompt(json_obj["informal_statement"].strip(), json_obj["formal_statement"].strip(), data_type="other")
        if count < 3:
            print(f"# {count}:")
            print(prompt)
            print("-----------------")
            print(completion)
            print("=================")
        writer.write(json.dumps({
            "prompt": prompt,
            "completion": completion,
        }) + "\n")
        count += 1

    writer.close()

def process_files_other(afp_prediction_dir, std_prediction_dir, math_prediction_dirs, aime_prediction_dirs, output_path, task):
    afp_dataset = load_afp_data(afp_prediction_dir=afp_prediction_dir, length_filtering=True)
    std_dataset = load_std_data(std_prediction_dir=std_prediction_dir, length_filtering=True)
    math_dataset = load_math_data(prediction_dirs=math_prediction_dirs)
    aime_dataset = load_competition_data(prediction_dirs=aime_prediction_dirs, subgoal_proof=True)
    dataset = afp_dataset + std_dataset + math_dataset + aime_dataset

    if task == "formal_statement":
        writer = open(output_path, "w", encoding="utf-8")
        count = 0
        for json_obj in tqdm(dataset):
            prompt = f"Translate the informal statement into a formal statement by defining variables and assumptions explicitly, and then stating the main claim clearly using precise mathematical notation.\n\n### Informal Statement\n{json_obj['informal_statement']}\n\n### Formal Statement"
            completion = json_obj['formal_statement']
            if count < 3:
                print(f"# {count}:")
                print(prompt)
                print("-----------------")
                print(completion)
                print("=================")
            writer.write(json.dumps({
                "prompt": prompt,
                "completion": completion,
            }) + "\n")
            count += 1
        writer.close()

    elif task == "informal_proof":
        writer = open(output_path, "w", encoding="utf-8")
        count = 0
        for json_obj in tqdm(dataset):
            prompt = f"Generate a subgoal-based proof by identifying and breaking down the critical steps needed to achieve the overall proof, explaining each subgoal with clear mathematical reasoning and ensuring logical progression from one subgoal to the next until the final proof is achieved.\n\n### Informal Statement\n{json_obj['informal_statement']}\n\n### Formal Statement\n{json_obj['formal_statement']}\n\n### Subogal-based Proof"
            completion = json_obj["subgoal_proof"] if "subgoal_proof" in json_obj else json_obj["informal_proof"]

            if count < 3:
                print(f"# {count}:")
                print(prompt)
                print("-----------------")
                print(completion)
                print("=================")
            writer.write(json.dumps({
                "prompt": prompt,
                "completion": completion,
            }) + "\n")
            count += 1
        writer.close()

    elif task == "posterior_informal_proof":
        writer = open(output_path, "w", encoding="utf-8")
        count = 0
        for json_obj in tqdm(dataset):
            formal_proof = delete_comments(json_obj["formal_proof"])
            prompt = f"Generate a subgoal-based proof by breaking down the formal proof into critical steps, providing clear mathematical reasoning for each subgoal, and ensuring logical progression from one subgoal to the next until the final proof is achieved.\n\n### Informal Statement\n{json_obj['informal_statement']}\n\n### Formal Statement\n{json_obj['formal_statement']}\n\n### Formal Proof\n{formal_proof}\n\n### Subogal-based Proof"
            completion = json_obj["subgoal_proof"] if "subgoal_proof" in json_obj else json_obj["informal_proof"]

            if count < 3:
                print(f"# {count}:")
                print(prompt)
                print("-----------------")
                print(completion)
                print("=================")
            writer.write(json.dumps({
                "prompt": prompt,
                "completion": completion,
            }) + "\n")
            count += 1
        writer.close()

    else:
        raise ValueError

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument('--afp_prediction_dir', type=str, required=True)
    parser.add_argument('--std_prediction_dir', type=str, required=True)
    parser.add_argument('--math_prediction_dirs', type=str, nargs='+', required=True)
    parser.add_argument('--aime_prediction_dirs', type=str, nargs='+', required=True)
    parser.add_argument('--output_path', type=str, required=True)
    parser.add_argument('--task', type=str, required=True)

    args = parser.parse_args()
    os.makedirs(os.path.dirname(args.output_path), exist_ok=True)

    if args.task in ["formal_proof_v1:orig", "formal_proof_v1:filter", "formal_proof_v1:filter2", "formal_proof_v2:orig", "formal_proof_v2:filter", "formal_proof_v2:filter2"]:
        process_files(
            afp_prediction_dir=args.afp_prediction_dir,
            std_prediction_dir=args.std_prediction_dir,
            math_prediction_dirs=args.math_prediction_dirs,
            aime_prediction_dirs=args.aime_prediction_dirs,
            output_path=args.output_path,
            task=args.task
        )
    elif args.task in ["formal_statement", "informal_proof", "posterior_informal_proof"]:
        process_files_other(
            afp_prediction_dir=args.afp_prediction_dir,
            std_prediction_dir=args.std_prediction_dir,
            math_prediction_dirs=args.math_prediction_dirs,
            aime_prediction_dirs=args.aime_prediction_dirs,
            output_path=args.output_path,
            task=args.task
        )
    else:
        raise ValueError