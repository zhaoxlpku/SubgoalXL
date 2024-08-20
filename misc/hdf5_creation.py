from tqdm import tqdm
import h5py
import os
import json

def build_formal_to_informal_dataset():
    data_path = "datasets/afp"
    split = "train"
    afp_path = "/home/xueliang/isabelle_server_resources/afp-2021-10-22"

    problem_names_split = json.load(open(f"{data_path}/problem_names_split.json", encoding="utf-8"))
    problem_names = problem_names_split[split]
    pisa_path = f"{data_path}/{split}.jsonl"

    dataset = []
    with open(pisa_path, encoding="utf-8") as f:
        for i, line in enumerate(f.readlines()):
            json_obj = json.loads(line)
            if len(json_obj) == 0: continue
            problem_name = problem_names[i]
            theory_file = problem_name[0].replace("/home/qj213/afp-2021-10-22", afp_path)

            working_dir = os.path.dirname(theory_file)
            interactive_file = os.path.join(working_dir, "Interactive.thy")

            if not os.path.exists(theory_file): continue
            lemma = problem_name[1]
            formal_statement = json_obj[0]["extra context"]
            formal_proof = "\n".join([step["action"] for step in json_obj])
            assert lemma.strip() == formal_statement.strip()
            dataset.append({
                "formal_statement": formal_statement,
                "formal_proof": formal_proof,
                "id": f"afp-{len(dataset)}",
                "working_dir": working_dir,
                "theory_file": theory_file,
                "interactive_file": interactive_file,
            })
    return dataset


def build_formal_to_informal_dataset_HOL():
    data_path = "/import/snvm-sc-scratch2/xueliangz/Data/HOL"
    split = "train"

    problem_names_split = json.load(open(f"{data_path}/problem_names_split.json", encoding="utf-8"))
    problem_names = problem_names_split[split]
    pisa_path = f"{data_path}/{split}.jsonl"

    dataset = []
    with open(pisa_path, encoding="utf-8") as f:
        for i, line in enumerate(f.readlines()):
            json_obj = json.loads(line)
            if len(json_obj) == 0: continue
            problem_name = problem_names[i]
            theory_file = problem_name[0]

            working_dir = os.path.dirname(theory_file)
            interactive_file = os.path.join(working_dir, "Interactive.thy")

            if not os.path.exists(theory_file):
                print(f"{theory_file} no found")
                continue
            lemma = problem_name[1]
            formal_statement = json_obj[0]["extra context"]
            formal_proof = "\n".join([step["action"] for step in json_obj])
            assert lemma.strip() == formal_statement.strip()
            dataset.append({
                "formal_statement": formal_statement,
                "formal_proof": formal_proof,
                "id": f"std-{len(dataset)}",
                "working_dir": working_dir,
                "theory_file": theory_file,
                "interactive_file": interactive_file,
            })
    return dataset


if __name__ == "__main__":

    dataset = build_formal_to_informal_dataset()
    h5_path = f"datasets/afp/afp_train_{int(len(dataset) // 1000)}k.hdf5"

    # dataset = build_formal_to_informal_dataset_HOL()
    # h5_path = f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/std_train_{int(len(dataset) // 1000)}k.hdf5"

    f_h5 = h5py.File(h5_path, 'w')
    for idx, data in tqdm(enumerate(dataset), total=len(dataset)):
        grp = f_h5.create_group(str(idx))
        for key in data:
            grp.create_dataset(key, data=data[key])
    f_h5.close()