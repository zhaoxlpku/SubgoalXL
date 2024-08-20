import argparse
import json
import os


def get_repo_root():
    # Get the absolute path of the current script (located in the "inference" folder)
    script_dir = os.path.dirname(os.path.abspath(__file__))
    # Assume the repo root is the parent directory of the "inference" folder
    repo_root = os.path.dirname(script_dir)
    return repo_root


def process_directory(directory, result_path):
    repo_root = get_repo_root()
    base_name = os.path.basename(directory)
    result_file = os.path.join(result_path, f"{base_name}.jsonl")

    with open(result_file, 'w', encoding='utf-8') as result_fp:
        # Iterate over the files in the directory
        for filename in os.listdir(directory):
            if filename.endswith(".jsonl"):
                # Extract id and sample_idx from filename by splitting at the last hyphen
                id_part = "-".join(filename.split('-')[:-1])
                sample_idx = filename.split('-')[-1].replace(".jsonl", "")

                # Read the input file content
                input_file = os.path.join(directory, filename)
                with open(input_file, 'r', encoding='utf-8') as input_fp:
                    data = [json.loads(line) for line in input_fp.readlines()]

                # Assuming the first json line contains the required fields
                json_obj = {
                    "id": id_part,
                    "informal_statement": data[0].get("informal_statement"),
                    "informal_proof": data[0].get("informal_proof"),
                    "formal_statement": data[0].get("formal_statement"),
                    "formal_proof": data[0].get("formal_proof"),
                }

                # Check isa2021 path
                isa2021_path = os.path.join(repo_root, f"outputs/evaluation/{base_name}/{filename}")
                if os.path.exists(isa2021_path):
                    with open(isa2021_path, 'r', encoding='utf-8') as isa2021_fp:
                        isa2021_data = json.loads(isa2021_fp.readline().strip())
                        json_obj['isa2021'] = isa2021_data

                # Check isa2022 path
                isa2022_path = os.path.join(repo_root, f"outputs/evaluation/{base_name}_2022/{filename}")
                if os.path.exists(isa2022_path):
                    with open(isa2022_path, 'r', encoding='utf-8') as isa2022_fp:
                        isa2022_data = json.loads(isa2022_fp.readline().strip())
                        json_obj['isa2022'] = isa2022_data

                # Write the result as a single line in result_file
                result_fp.write(json.dumps(json_obj, ensure_ascii=False) + '\n')


def main():
    parser = argparse.ArgumentParser(description="Process directories and generate JSONL results")
    parser.add_argument('--dirs', type=str, nargs='+', required=True, help="List of directories to process")
    parser.add_argument('--result_path', type=str, required=True, help="Path to save the result JSONL files")

    args = parser.parse_args()

    # Process each directory
    for directory in args.dirs:
        process_directory(directory, args.result_path)


if __name__ == "__main__":
    main()
