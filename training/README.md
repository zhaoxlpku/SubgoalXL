# Expert Iteration

This repository contains the code necessary to perform one iteration of expert learning. This process includes sampling from optimal distributions for formal statements, formal proofs, and subgoal-based proofs, as well as gathering the generated data during the data preparation stage.

## Expert Learning Process

Before initiating expert learning, it is essential to construct subgoal proofs for problems in the informal dataset. Use the following command:

```bash
python run_autoformalization_generation.py --task subgoal --exp_name exp_name --num_workers 4 --model_name_or_path /path/to/llama3 --prompt_manager_name Llama3BaseSubgoalPromptManager --num_samples 1 --temperature 0.2
```

The sampling process is divided into the following steps:

1. **Candidate Generation**: Generate a set of candidate formal statements, formal proofs, or subgoals.
2. **Scoring**: Score the candidates using the appropriate reward models.
3. **Optimal Sampling**: Select samples to ensure they represent sampling from optimal distributions.
4. **Verification**: (Applicable only for formal statements and proofs) Use Isabelle to filter out invalid samples.

### Step 1: Candidate Generation
To generate candidates, run the following scripts:

```bash
python run_rejection_sampling_formal_statement.py --exp_name formal_statement_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/formal_statement_generator_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fPromptManager --model_index 0 --num_samples 8 --temperature 0.6 --subgoal_dir /path/to/repo/outputs/subgoal_proof/subgaol_dir
python run_rejection_sampling_informal_proof.py --exp_name subgoal_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/subgoal_generator_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fPromptManager --model_index 0 --num_samples 8 --temperature 0.6
python run_rejection_sampling_formal_proof.py --exp_name formal_proof_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/formal_proof_generator_v1_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fPromptManager --num_models 4 --model_index 0 --temperature 0.6 --data_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k}
python run_rejection_sampling_formal_proof.py --exp_name formal_proof_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/formal_proof_generator_v2_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fPromptManager --num_models 4 --model_index 1 --temperature 0.6 --data_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k}
python run_rejection_sampling_formal_proof.py --exp_name formal_proof_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/formal_proof_generator_v3_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager --num_models 4 --model_index 2 --temperature 0.6 --data_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k}
python run_rejection_sampling_formal_proof.py --exp_name formal_proof_iter${k} --num_workers 4 --endpoint_manager_name BatchedDynamicEndpointManager --model_name_or_path /path/to/formal_proof_generator_v4_iter$((k-1)) --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager --num_models 4 --model_index 3 --temperature 0.6 --data_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k}
```

### Step 2: Scoring
To score the generated candidates, use the following scripts:

```bash
python run_sequence_scoring.py --input_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k} --output_dir /path/to/repo/outputs/scoring/formal_statement_iter${k} --model_name_or_path /path/to/subgoal_generator_iter$((k-1)) --task formal_statement --batch_size 2 --start_idx 0
python run_sequence_scoring.py --input_dir /path/to/repo/outputs/rejection_sampling/subgoal_iter${k} --output_dir /path/to/repo/outputs/scoring/subgoal_iter${k}  --model_name_or_path /path/to/formal_proof_generator_v1_iter$((k-1)) --task informal_proof --batch_size 2 --start_idx 0
python run_sequence_scoring.py --input_dir /path/to/repo/outputs/rejection_sampling/formal_proof_iter${k} --output_dir /path/to/repo/outputs/scoring/formal_proof_iter${k}  --model_name_or_path /path/to/posterior_subgoal_generator --task formal_proof --batch_size 2 --start_idx 0
```

### Step 3: Optimal Sampling
To sample the data, use the following scripts:

```bash
python run_data_sampling.py --data_dir /path/to/repo/outputs/rejection_sampling/formal_statement_iter${k} --score_dir /path/to/repo/outputs/scoring/formal_statement_iter${k} --output_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --task formal_statement --num_samples 2
python run_data_sampling.py --data_dir /path/to/repo/outputs/rejection_sampling/subgoal_iter${k} --score_dir /path/to/repo/outputs/scoring/subgoal_iter${k} --output_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --task informal_proof --num_samples 2
python run_data_sampling.py --data_dir /path/to/repo/outputs/rejection_sampling/formal_proof_iter${k} --score_dir /path/to/repo/outputs/scoring/formal_proof_iter${k} --output_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --task formal_proof --num_samples 2
```

### Step 4: Verification
To verify the formal statements and proofs, use the following scripts:

```bash
python ../verification/schedule_proofs.py --input_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --output_dir /path/to/repo/outputs/evaluation/formal_statement_iter${k} --script_path /path/to/repo/verification/single_proof_checker2.sh --port_base 8000 --port_count 1024
python ../verification/schedule_proofs.py --input_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_dir /path/to/repo/outputs/evaluation/formal_proof_iter${k} --script_path /path/to/repo/verification/single_proof_checker2.sh --port_base 8000 --port_count 1024
```

### Data Collection for Subsequent Iterations

After verification, gather the necessary data for training components in the next iteration using the following scripts:

```bash
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/formal_proof_v1_iter${k}.jsonl --task formal_proof_v1:orig --afp_ratio 0.5 --math_ratio 0.5
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/formal_proof_v2_iter${k}.jsonl --task formal_proof_v1:filter --afp_ratio 0.5 --math_ratio 0.5
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/formal_proof_v3_iter${k}.jsonl --task formal_proof_v2:orig --afp_ratio 0.5 --math_ratio 0.5
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/formal_proof_v4_iter${k}.jsonl --task formal_proof_v2:filter --afp_ratio 0.5 --math_ratio 0.5
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/formal_statement_iter${k}.jsonl --task formal_statement --afp_ratio 0.5 --math_ratio 0.5
python run_data_merging.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --informal_proof_dir /path/to/repo/outputs/sampling/subgoal_iter${k} --formal_statement_dir /path/to/repo/outputs/sampling/formal_statement_iter${k} --formal_proof_dir /path/to/repo/outputs/sampling/formal_proof_iter${k} --output_path /path/to/repo/outputs/merging/subgoal_iter${k}.jsonl --task informal_proof --afp_ratio 0.5 --math_ratio 0.5
```