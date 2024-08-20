# Inference

This repository contains the code necessary for conducting inference using formal proof generators trained during the expert learning processes.

## Proof Generation

To generate proofs for each problem in the miniF2F test set using formal proof generators from the *3rd* iteration, run the following scripts. Note that similar commands can be applied to the checkpoints from previous iterations by simply replacing the model paths and experiment names accordingly.

### Without Human-Written Informal Proof

```bash
python run_informal_to_formal.py \
  --exp_name test_round_3_without_informal_model_v1 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v1_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fPromptManager \
  --max_response_len 2048 \
  --phase without_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_without_informal_model_v2 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v2_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fPromptManager \
  --max_response_len 2048 \
  --phase without_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_without_informal_model_v3 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v3_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager \
  --max_response_len 2048 \
  --phase without_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_without_informal_model_v4 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v4_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager \
  --max_response_len 2048 \
  --phase without_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8
```

### With Human-Written Informal Proof

```bash
python run_informal_to_formal.py \
  --exp_name test_round_3_with_informal_model_v1 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v1_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fPromptManager \
  --max_response_len 2048 \
  --phase with_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_with_informal_model_v2 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v2_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fPromptManager \
  --max_response_len 2048 \
  --phase with_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_with_informal_model_v3 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v3_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager \
  --max_response_len 2048 \
  --phase with_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8

python run_informal_to_formal.py \
  --exp_name test_round_3_with_informal_model_v4 \
  --num_workers 1 \
  --endpoint_manager_name BatchedDynamicEndpointManager \
  --model_name_or_path /path/to/formal_proof_generator_v4_iter${k} \
  --prompt_manager_name InformalToFormalMinif2fTwoInstructPromptManager \
  --max_response_len 2048 \
  --phase with_informal_proof \
  --num_samples 512 \
  --split test \
  --temperature 0.8
```

## Proof Verification

### Using Isabelle 2021

To verify the proofs using Isabelle 2021, run the following scripts:

#### Without Human-Written Informal Proof

```bash
python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v1 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v1 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v2 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v2 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v3 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v3 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v4 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v4 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024
```

#### With Human-Written Informal Proof

```bash
python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v1 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v1 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v2 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v2 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v3 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v3 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v4 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v4 \
  --script_path /path/to/repo/verification/single_proof_checker2.sh \
  --port_base 8000 \
  --port_count 1024
```

### Using Isabelle 2022

To verify the proofs using Isabelle 2022, run the following scripts:

#### Without Human-Written Informal Proof

```bash
python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v1 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v1 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v2 \
  --output_dir /path/to/repo/

outputs/evaluation/test_round_3_without_informal_model_v2 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v3 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v3 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v4 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_without_informal_model_v4 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024
```

#### With Human-Written Informal Proof

```bash
python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v1 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v1 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v2 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v2 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v3 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v3 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024

python ../verification/schedule_proofs.py \
  --input_dir /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v4 \
  --output_dir /path/to/repo/outputs/evaluation/test_round_3_with_informal_model_v4 \
  --script_path /path/to/repo/verification/single_proof_checker2022_2.sh \
  --port_base 8000 \
  --port_count 1024
```

## Saving Results

After generating and verifying proofs, save the results using the following script:

```bash
python save_results.py \
  --dirs /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v1 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v2 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v3 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_without_informal_model_v4 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v1 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v2 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v3 \
         /path/to/repo/outputs/informal_to_formal/test_round_3_with_informal_model_v4 \
  --result_path /path/to/repo/results
```

## Calculating Accuracy

Finally, calculate the accuracy using the following script:

```bash
python calculate_accuracy.py
```
