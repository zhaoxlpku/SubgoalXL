import argparse
import json
import os

import torch
from torch.nn.utils.rnn import pad_sequence
from tqdm import tqdm
from transformers import AutoModelForCausalLM, AutoTokenizer


def add_space_separator(completion, prompt):
    if prompt:
        prompt = prompt.rstrip(' ')
    if completion:
        completion = ' ' + completion.lstrip(' ')
    return completion, prompt

def calculate_log_probabilities(model, tokenizer, prompts, completions, device):
    # Tokenize the prompts and completions
    prompt_ids = [tokenizer(prompt, return_tensors='pt').input_ids.squeeze(0).to(device) for prompt in prompts]
    completion_ids = [tokenizer(completion, return_tensors='pt').input_ids.squeeze(0).to(device) for completion in completions]

    # Concatenate prompt and completion ids
    input_ids = [torch.cat([p_ids, c_ids], dim=-1) for p_ids, c_ids in zip(prompt_ids, completion_ids)]
    
    # If the tokenizer doesn't have a pad_token, use eos_token for padding
    if tokenizer.pad_token is None:
        pad_token_id = tokenizer.eos_token_id
        tokenizer.pad_token = tokenizer.eos_token
    else:
        pad_token_id = tokenizer.pad_token_id

    input_ids = pad_sequence(input_ids, batch_first=True, padding_value=pad_token_id).to(device)
    attention_mask = (input_ids != pad_token_id).to(device)

    # Get the model's outputs
    with torch.no_grad():
        outputs = model(input_ids, attention_mask=attention_mask, labels=input_ids, return_dict=True)

    # Calculate log probabilities
    log_probs = outputs.logits.log_softmax(dim=-1)

    completion_log_probs = []
    for i in range(len(prompts)):
        prompt_length = prompt_ids[i].size(0)
        completion_length = completion_ids[i].size(0)
        completion_log_probs.append(log_probs[i, prompt_length:prompt_length + completion_length].gather(1, completion_ids[i].unsqueeze(1)).squeeze(-1).sum().item())
    
    return completion_log_probs

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

def get_subgoal_prompt(informal_statement, informal_proof, formal_statement):
    prompt = f"Generate a subgoal-based proof by identifying and breaking down the critical steps needed to achieve the overall proof, explaining each subgoal with clear mathematical reasoning and ensuring logical progression from one subgoal to the next until the final proof is achieved.\n\n### Informal Statement\n{informal_statement}\n\n### Formal Statement\n{formal_statement}\n\n### Subogal-based Proof"
    completion = informal_proof
    return prompt, completion

def get_post_subgoal_prompt(informal_statement, informal_proof, formal_statement, formal_proof): 
    formal_proof = delete_comments(formal_proof)
    prompt = f"Generate a subgoal-based proof by breaking down the formal proof into critical steps, providing clear mathematical reasoning for each subgoal, and ensuring logical progression from one subgoal to the next until the final proof is achieved.\n\n### Informal Statement\n{informal_statement}\n\n### Formal Statement\n{formal_statement}\n\n### Formal Proof\n{formal_proof}\n\n### Subogal-based Proof"
    completion = informal_proof
    return prompt, completion

def get_formal_proof_prompt(informal_statement, informal_proof, formal_statement, formal_proof):
    prompt = f"### Problem:\n{informal_statement}\n\n### Proof:\n{formal_statement}"
    prompt = f"{prompt} (*{informal_proof}*)\n"
    completion = formal_proof
    return prompt, completion


def construct_prompt_and_completion(data, task):
    if task == "formal_statement":
        informal_statement = data["informal_statement"]
        formal_statement = data["formal_statement"]
        subgoal_proof = data["subgoal_proof"]
        if formal_statement is None:
            return None, None
        return get_subgoal_prompt(informal_statement, subgoal_proof, formal_statement)
        
    elif task == "formal_proof": 
        informal_statement = data["informal_statement"]
        formal_statement = data["formal_statement"]
        subgoal_proof = data["subgoal_proof"]
        formal_proof = data["formal_proof"]
        if formal_proof is None:
            return None, None
        return get_post_subgoal_prompt(informal_statement, subgoal_proof, formal_statement, formal_proof)
    elif task == "informal_proof":
        informal_statement = data["informal_statement"]
        formal_statement = data["formal_statement"]
        subgoal_proof = data["subgoal_proof"]
        formal_proof = data["formal_proof"]
        if subgoal_proof is None:
            return None, None
        return get_formal_proof_prompt(informal_statement, subgoal_proof, formal_statement, formal_proof)
    else:
        raise ValueError

def process_files(input_dir, output_dir, model_name_or_path, task, batch_size=8, start_idx=0, end_idx=None):
    os.makedirs(output_dir, exist_ok=True)

    # Check if GPU is available
    if torch.cuda.is_available():
        device = torch.device("cuda")
        print(f"GPU is available. Using GPU: {torch.cuda.get_device_name(device)}")
    else:
        device = torch.device("cpu")
        print("GPU is not available, using CPU instead.")

    # Initialize the model and tokenizer
    tokenizer = AutoTokenizer.from_pretrained(model_name_or_path)
    model = AutoModelForCausalLM.from_pretrained(model_name_or_path).to(device)

    # Verify the model is on the correct device
    print(f"Model is on device: {next(model.parameters()).device}")

    # Gather all JSONL files
    file_list = [filename for filename in os.listdir(input_dir) if filename.endswith(".jsonl")]

    if end_idx is None or end_idx > len(file_list):
        end_idx = len(file_list)

    batch_prompts = []
    batch_completions = []
    batch_filenames = []

    for idx in tqdm(range(start_idx, end_idx), desc="Processing files"):
        filename = file_list[idx]
        input_file_path = os.path.join(input_dir, filename)
        output_file_path = os.path.join(output_dir, filename)

        if os.path.exists(output_file_path):
            tqdm.write(f"Skipping {filename} as it already exists in the output directory.")
            continue

        with open(input_file_path, 'r', encoding="utf-8") as file:
            data = json.loads(file.readline())
        
        prompt, completion = construct_prompt_and_completion(data, task)
        if prompt is None or completion is None:
            continue

        completion, prompt = add_space_separator(completion=completion, prompt=prompt)

        batch_prompts.append(prompt)
        batch_completions.append(completion)
        batch_filenames.append(filename)

        if len(batch_prompts) == batch_size:
            log_probs = calculate_log_probabilities(model, tokenizer, batch_prompts, batch_completions, device)
            for j in range(len(batch_prompts)):
                result = {
                    'filename': batch_filenames[j],
                    'prompt': batch_prompts[j],
                    'completion': batch_completions[j],
                    'log_prob': log_probs[j]
                }
                output_file_path = os.path.join(output_dir, batch_filenames[j])
                with open(output_file_path, 'w', encoding="utf-8") as output_file:
                    output_file.write(json.dumps(result) + '\n')

            batch_prompts = []
            batch_completions = []
            batch_filenames = []

    # Process any remaining examples that did not form a full batch
    if batch_prompts:
        log_probs = calculate_log_probabilities(model, tokenizer, batch_prompts, batch_completions, device)
        for j in range(len(batch_prompts)):
            result = {
                'filename': batch_filenames[j],
                'prompt': batch_prompts[j],
                'completion': batch_completions[j],
                'log_prob': log_probs[j]
            }
            output_file_path = os.path.join(output_dir, batch_filenames[j])
            with open(output_file_path, 'w', encoding="utf-8") as output_file:
                output_file.write(json.dumps(result) + '\n')

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Calculate log probabilities of completions given prompts.")
    parser.add_argument('--input_dir', type=str, required=True, help="Path to the input directory containing JSONL files.")
    parser.add_argument('--output_dir', type=str, required=True, help="Path to the output directory where results will be saved.")
    parser.add_argument('--model_name_or_path', type=str, required=True, help="Name or path of the Hugging Face model to use.")
    parser.add_argument('--batch_size', type=int, default=8, help="Batch size for processing.")
    parser.add_argument('--start_idx', type=int, default=0, help="Start index for processing files.")
    parser.add_argument('--end_idx', type=int, default=None, help="End index for processing files.")
    parser.add_argument('--task', type=str, required=True)

    args = parser.parse_args()

    process_files(args.input_dir, args.output_dir, args.model_name_or_path, args.task, args.batch_size, args.start_idx, args.end_idx)
