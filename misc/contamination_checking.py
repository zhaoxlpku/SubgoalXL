from tqdm import tqdm
import nltk
from nltk.util import ngrams
import json
import os


def load_data(data_path="datasets/gsm8k/train.jsonl"):
    examples = []
    with open(data_path, encoding="utf-8") as f:
        for line in f.readlines():
            examples.append(json.loads(line))
    return examples

def load_aime_data(data_path="amc_and_aime_problems"):
    # source_dir = "amc_and_aime_problems"
    # count = 0
    examples = []
    for contest in os.listdir(data_path):
        for sub_contest in os.listdir(os.path.join(data_path, contest)):
            for file in os.listdir(os.path.join(data_path, contest, sub_contest)):
                problem_path = os.path.join(data_path, contest, sub_contest, file)
                with open(problem_path, encoding="utf-8") as f:
                    data = json.load(f)
                    problem = data["problem"]
                    solutions = data["solutions"]
                    if problem.strip() and "[asy]" not in problem and len([solution for solution in solutions if solution.strip()]) > 0:
                        examples.append({
                            "question": problem,
                            "answer": [solution for solution in solutions if solution.strip()][0],
                        })
    return examples

def load_imo_data(data_path="imo_problems"):
    # source_dir = "amc_and_aime_problems"
    # count = 0
    examples = []
    for contest in os.listdir(data_path):
        for file in os.listdir(os.path.join(data_path, contest)):
            problem_path = os.path.join(data_path, contest, file)
            with open(problem_path, encoding="utf-8") as f:
                data = json.load(f)
                problem = data["problem"]
                solutions = data["solutions"]
                if problem.strip() and "[asy]" not in problem and len([solution for solution in solutions if solution.strip()]) > 0:
                    # print(problem)
                    # print(solutions)
                    # input(">>>")
                    examples.append({
                        "question": problem,
                        "answer": [solution for solution in solutions if solution.strip()][0],
                    })
    return examples

def compute_ngram_overlap(sentence1, sentence2, n):
    """
    Computes the n-gram overlap between two sentences.
    
    Args:
        sentence1 (str): The first sentence.
        sentence2 (str): The second sentence.
        n (int): The value of n for n-grams.
        
    Returns:
        float: The n-gram overlap between the two sentences.
    """
    # Tokenize the sentences
    tokens1 = nltk.word_tokenize(sentence1.lower())
    tokens2 = nltk.word_tokenize(sentence2.lower())
    
    # Compute n-grams
    ngrams1 = set(ngrams(tokens1, n))
    ngrams2 = set(ngrams(tokens2, n))
    
    # Compute the overlap
    overlap = ngrams1.intersection(ngrams2)
    overlap_count = len(overlap)
    total_count = len(ngrams1) + len(ngrams2)
    
    if total_count == 0:
        return 0.0
    else:
        return overlap_count / total_count

def check_corpus_contamination(corpus_a, corpus_b, threshold=0.5, n=3):
    """
    Checks for contamination between two corpora and removes sentences in corpus_a that appear in corpus_b.
    
    Args:
        corpus_a (list): A list of sentences in corpus A.
        corpus_b (list): A list of sentences in corpus B.
        threshold (float): The threshold for n-gram overlap above which sentences are considered contaminated.
        n (int): The value of n for n-grams.
        
    Returns:
        list: A list of sentences in corpus A that are not contaminated by corpus B.
    """
    clean_corpus_a = []
    
    for item_a in tqdm(corpus_a):
        sentence_a = item_a["question"] + "\n" + item_a["answer"]
        sentence_a = sentence_a.lower()
        contaminated = False
        for item_b in corpus_b:
            if "informal_statement" in item_b:
                sentence_b = item_b["informal_statement"] + "\n" + item_b["informal_proof"]
            else:
                sentence_b = item_b["question"] + "\n" + item_b["answer"]
            sentence_b = sentence_b.lower()
            overlap = compute_ngram_overlap(sentence_a, sentence_b, n)
            if overlap >= threshold:
                contaminated = True
                # print("item_a: ", f"{item_a['question']}\n{item_a['answer']}")
                # print("------------------")
                # print("item_b: ", f"{item_b['informal_statement']}\n{item_b['informal_proof']}")
                # print("==================")
                # input(">>>")
                break
        if not contaminated:
            clean_corpus_a.append(item_a)
    
    return clean_corpus_a

def main():
    # data_name = "MATH"
    data_name = "AIME"
    # data_name = "IMO"
    if data_name == "MATH":
        math_problems = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl")
        miniF2F_valid = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/validation.jsonl")
        miniF2F_test = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/test.jsonl")

        for threshold in [0.1, 0.2, 0.3, 0.4]:
            print(f"threshold = {threshold}")
            clean_math_problems = check_corpus_contamination(math_problems, miniF2F_valid, threshold=threshold)
            clean_math_problems2 = check_corpus_contamination(clean_math_problems, miniF2F_test, threshold=threshold)
            print("remain examples: ", len(clean_math_problems2))
            with open(f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train_clean_threshold0_{threshold * 10}.jsonl", "w", encoding="utf-8") as f:
                for item in clean_math_problems2:
                    f.write(json.dumps(item) + "\n")
    elif data_name == "AIME":
        # start_idx, end_idx = 0, 1000
        # start_idx, end_idx = 1000, 2000
        # start_idx, end_idx = 2000, 3000
        # start_idx, end_idx = 3000, 4000
        # start_idx, end_idx = 4000, 5000
        start_idx, end_idx = 5000, 5381

        if False:
            aime_problems = load_aime_data()[start_idx:end_idx] # 5381
            # print(len(aime_problems))

            math_problems = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl")
            miniF2F_valid = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/validation.jsonl")
            miniF2F_test = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/test.jsonl")

            threshold = 0.1
            # print(f"threshold = {threshold}")
            clean_math_problems = check_corpus_contamination(aime_problems, math_problems + miniF2F_valid + miniF2F_test, threshold=threshold)
            print("remain examples: ", len(clean_math_problems))
            with open(f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/aime/train_clean_threshold0_{int(threshold * 10)}_{start_idx}_{end_idx}.jsonl", "w", encoding="utf-8") as f:
                for item in clean_math_problems:
                    f.write(json.dumps(item) + "\n")
        files = [
            "train_clean_threshold0_1_0_1000.jsonl",
            "train_clean_threshold0_1_1000_2000.jsonl",
            "train_clean_threshold0_1_2000_3000.jsonl",
            "train_clean_threshold0_1_3000_4000.jsonl",
            "train_clean_threshold0_1_4000_5000.jsonl",
            "train_clean_threshold0_1_5000_5381.jsonl"
        ]
        base_dir = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/aime/"
        writer = open(os.path.join(base_dir, "train_clean_threshold0_1.jsonl"), "w", encoding="utf-8")
        for file in files:
            with open(os.path.join(base_dir, file), encoding="utf-8") as f:
                for line in f.readlines():
                    writer.write(line.strip() + "\n")
        writer.close()
    
    elif data_name == "IMO":
        imo_problems = load_imo_data() # 342
        print(len(imo_problems))

        math_problems = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl")
        miniF2F_valid = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/validation.jsonl")
        miniF2F_test = load_data("/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/test.jsonl")

        threshold = 0.1
        # print(f"threshold = {threshold}")
        clean_math_problems = check_corpus_contamination(imo_problems, math_problems + miniF2F_valid + miniF2F_test, threshold=threshold)
        print("remain examples: ", len(clean_math_problems))
        with open(f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/imo/train_clean_threshold0_{int(threshold * 10)}.jsonl", "w", encoding="utf-8") as f:
            for item in clean_math_problems:
                f.write(json.dumps(item) + "\n")
    else:
        raise ValueError
    

if __name__ == "__main__":
    main()