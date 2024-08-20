# Data Preparation

This repository contains code for constructing datasets essential for initializing components in the subsequent expert learning phase. The process involves two main steps: data generation and data collection.

## Data Generation

The data generation process involves two different workflows depending on the type of input dataset:

### 1. For Informal Datasets (e.g., AMC, AIME, IMO)

For informal datasets, we perform the following steps:

1. **Autoformalization**: Converts informal statements to formal statements and proofs.
2. **Statement Validation**: Heuristically filters out illegal statements.
3. **Verification**: Uses Isabelle to filter out illegal formal statements and proofs.

To process informal datasets, run the following scripts in order:

```bash
# Autoformalization
python run_autoformalization_generation.py --task autoformalization --exp_name exp_name --num_workers 4 --model_name_or_path /path/to/llama3 --prompt_manager_name Llama3BaseFewshotPromptManager --num_samples 64 --temperature 0.6 

# Statement Validation
python run_autoformalization_generation.py --task statement_validation --exp_name exp_name --num_workers 4 --model_name_or_path /path/to/llama3-instruct --prompt_manager_name Llama3FewshotPromptManager --num_samples 64 --temperature 0.6

# Verification
python ../verification/schedule_proofs.py --input_dir /path/to/repo/outputs/autoformalization/exp_name --output_dir /path/to/repo/outputs/evaluation/exp_name --script_path /path/to/repo/verification/single_proof_checker2.sh --port_base 8000 --port_count 1024
```

### 2. For Formal Datasets (e.g., AFP and HOL-std)

For formal datasets, we perform the following step:

1. **Auto-informalization**: Converts formal statements and proofs to informal ones.

To process formal datasets, run the following script:

```bash
python run_auto_formal_to_informal.py --exp_name exp_name --num_workers 2 --model_name_or_path /path/to/llama3 --data_path /path/to/repo/datasets/std/afp_train_154k.hdf5
```

or

```bash
python run_auto_formal_to_informal.py --exp_name exp_name --num_workers 2 --model_name_or_path /path/to/llama3 --data_path /path/to/repo/datasets/std/std_train_42k.hdf5
```

## Data Collection

The data collection process involves gathering and preparing the generated data for initializing four different components used in the expert learning phase. This step is crucial for organizing and structuring the data in a format suitable for each component.

### For Component Initialization

We collect and prepare data for the following components:

1. **Formal Statement Generator**
   ```bash
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task formal_statement
   ```

2. **Formal Proof Generator**
   ```bash
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task formal_proof_v1:orig
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task formal_proof_v1:filter
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task formal_proof_v2:orig
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task formal_proof_v2:filter
   ```

3. **Subgoal Generator**
   ```bash
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task informal_proof
   ```

4. **Posterior Subgoal Generator**
   ```bash
   python run_data_preparation.py --afp_prediction_dir /path/to/repo/outputs/formal_to_informal/afp_dir --std_prediction_dir /path/to/repo/outputs/formal_to_informal/std_dir --math_prediction_dirs /path/to/repo/outputs/autoformalization/math_dir --aime_prediction_dirs /path/to/repo/outputs/autoformalization/aime_dir --output_path /path/to/output --task posterior_informal_proof
   ```

