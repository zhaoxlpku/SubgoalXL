import json
import math
import os
import random
import subprocess

import h5py
from transformers import AutoTokenizer


def remove_boxed(s):
    left = "\\boxed{"
    try:
        assert s[:len(left)] == left
        assert s[-1] == "}"
        return s[len(left):-1]
    except:
        return None

def last_boxed_only_string(string):
    idx = string.rfind("\\boxed")
    if idx < 0:
        idx = string.rfind("\\fbox")
        if idx < 0:
            return None

    i = idx
    right_brace_idx = None
    num_left_braces_open = 0
    while i < len(string):
        if string[i] == "{":
            num_left_braces_open += 1
        if string[i] == "}":
            num_left_braces_open -= 1
            if num_left_braces_open == 0:
                right_brace_idx = i
                break
        i += 1

    if right_brace_idx == None:
        retval = None
    else:
        retval = string[idx:right_brace_idx + 1]

    return retval

def _fix_fracs(string):
    substrs = string.split("\\frac")
    new_str = substrs[0]
    if len(substrs) > 1:
        substrs = substrs[1:]
        for substr in substrs:
            new_str += "\\frac"
            if substr[0] == "{":
                new_str += substr
            else:
                try:
                    assert len(substr) >= 2
                except:
                    return string
                a = substr[0]
                b = substr[1]
                if b != "{":
                    if len(substr) > 2:
                        post_substr = substr[2:]
                        new_str += "{" + a + "}{" + b + "}" + post_substr
                    else:
                        new_str += "{" + a + "}{" + b + "}"
                else:
                    if len(substr) > 2:
                        post_substr = substr[2:]
                        new_str += "{" + a + "}" + b + post_substr
                    else:
                        new_str += "{" + a + "}" + b
    string = new_str
    return string

def _fix_a_slash_b(string):
    if len(string.split("/")) != 2:
        return string
    a = string.split("/")[0]
    b = string.split("/")[1]
    try:
        a = int(a)
        b = int(b)
        assert string == "{}/{}".format(a, b)
        new_string = "\\frac{" + str(a) + "}{" + str(b) + "}"
        return new_string
    except:
        return string

def _remove_right_units(string):
    # "\\text{ " only ever occurs (at least in the val set) when describing units
    if "\\text{ " in string:
        splits = string.split("\\text{ ")
        assert len(splits) == 2
        return splits[0]
    else:
        return string

def _fix_sqrt(string):
    if "\\sqrt" not in string:
        return string
    splits = string.split("\\sqrt")
    new_string = splits[0]
    for split in splits[1:]:
        if split[0] != "{":
            a = split[0]
            new_substr = "\\sqrt{" + a + "}" + split[1:]
        else:
            new_substr = "\\sqrt" + split
        new_string += new_substr
    return new_string

def _strip_string(string):
    # linebreaks
    string = string.replace("\n", "")
    # print(string)

    # remove inverse spaces
    string = string.replace("\\!", "")
    # print(string)

    # replace \\ with \
    string = string.replace("\\\\", "\\")
    # print(string)

    # replace tfrac and dfrac with frac
    string = string.replace("tfrac", "frac")
    string = string.replace("dfrac", "frac")
    # print(string)

    # remove \left and \right
    string = string.replace("\\left", "")
    string = string.replace("\\right", "")
    # print(string)

    # Remove circ (degrees)
    string = string.replace("^{\\circ}", "")
    string = string.replace("^\\circ", "")

    # remove dollar signs
    string = string.replace("\\$", "")

    # remove units (on the right)
    string = _remove_right_units(string)

    # remove percentage
    string = string.replace("\\%", "")
    string = string.replace("\%", "")

    # " 0." equivalent to " ." and "{0." equivalent to "{." Alternatively, add "0" if "." is the start of the string
    string = string.replace(" .", " 0.")
    string = string.replace("{.", "{0.")
    # if empty, return empty string
    if len(string) == 0:
        return string
    if string[0] == ".":
        string = "0" + string

    # to consider: get rid of e.g. "k = " or "q = " at beginning
    if len(string.split("=")) == 2:
        if len(string.split("=")[0]) <= 2:
            string = string.split("=")[1]

    # fix sqrt3 --> sqrt{3}
    string = _fix_sqrt(string)

    # remove spaces
    string = string.replace(" ", "")

    # \frac1b or \frac12 --> \frac{1}{b} and \frac{1}{2}, etc. Even works with \frac1{72} (but not \frac{72}1). Also does a/b --> \\frac{a}{b}
    string = _fix_fracs(string)

    # manually change 0.5 --> \frac{1}{2}
    if string == "0.5":
        string = "\\frac{1}{2}"

    # NOTE: X/Y changed to \frac{X}{Y} in dataset, but in simple cases fix in case the model output is X/Y
    string = _fix_a_slash_b(string)

    return string

def extract_gsm8k_final_answer(answer_text):
    return answer_text.split("####")[-1].strip()

def extract_math_final_answer(answer_text):
    return remove_boxed(last_boxed_only_string(answer_text))

# todo: define a hdf5 helper to keep the api consistent

def extract_task_id(file_name):
    # Split the file name by "."
    parts = file_name.split(".")

    # Extract the task ID, which is the first part before the file extension
    task_id = parts[0]

    return task_id

def smallest_power_of_10(given_number):
    # Calculate the smallest n such that 10^n > given_number
    n = math.ceil(math.log10(given_number))
    return n

class InformalToFormalPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = 1
        self.dataset = self.load_data()
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        self.few_shot_prompt = """Informal:
(*### Problem

Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. Show that it is 12.

### Solution

Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.
It is trivial to see that $y > 0$. 
Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$.
This can be done by the sum of squares method.*)

Formal:
theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \\<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
proof -
  (* Let $y = x \\sin x$. *)
  define y where "y=x * sin x"
  (* It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}. *)
  have "12 \\<le> (9 * y^2 + 4) / y"
  proof -
    (* It is trivial to see that $y > 0$. *)
    have c0: "y > 0"
      sledgehammer
    (* Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$. *)
    have "(9 * y^2 + 4) \\<ge> 12 * y" 
      sledgehammer
    then show ?thesis
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Find the greatest common factor of 180 and 168. Show that it is 12.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_188:
  "gcd 180 168 = (12::nat)"
  sledgehammer



Informal:
(*### Problem

Show that for positive integer n, 2 divides $4^n$.

### Solution

Since n is positive, we can find a natural number m where $m+1=n$.
Then we can show that 2 divides $4^{m+1}$. The conclusion thus follows.*)

Formal:
theorem numbertheory_2dvd4expn:
  fixes n :: nat
  assumes h0 : "n \\<noteq> 0"
  shows "(2::nat) dvd 4^n"
proof -
  obtain m::nat where c0: "m+1=n"
    sledgehammer
  have "(2::nat) dvd 4^(m+1)" sledgehammer
  then show ?thesis unfolding c0 sledgehammer
qed



Informal:
(*### Problem

What is the remainder when $1 + 2 + 3 + 4 + \\dots + 9 + 10$ is divided by 9? Show that it is 1.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_466:
  "(\\<Sum> k< 11. k) mod 9 = (1::nat)"
  sledgehammer



Informal:
(*### Problem

If $321_{b}$ is equal to the base 10 integer 57, find $b$ given that $b>0$. Show that it is 4.

### Solution

Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
\\\\ 3b^2+2b+1&=57
\\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
\\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
\\end{align*}This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. We know that $b>0$, so $b=4$.*)

Formal:
theorem mathd_numbertheory_48:
  fixes b :: real
  assumes h0 : "0<b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"
proof -
  (* Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
  \\\\ 3b^2+2b+1&=57
  \\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
  \\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
  \\end{align*} *)
  have "0 = 3 * b^2 + 2 * b -56" using h1 sledgehammer
  also have "... = (3*b+14)*(b-4)" sledgehammer
  finally have "0 = (3*b+14)*(b-4)" sledgehammer
  (* This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. *)
  then have "b = -14/3 ∨ b=4" sledgehammer
  (* We know that $b>0$, so $b=4$. *)
  then show ?thesis using h0 sledgehammer
qed



Informal:
(*### Problem

When Rachel divides her favorite number by 7, she gets a remainder of 5. What will the remainder be if she multiplies her favorite number by 5 and then divides by 7? Show that it is 4.

### Solution

Let $n$ be Rachel's favorite number. 
Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$.
*)

Formal:
theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  (* Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$. *)
  have c0:"(5 * n) mod 7 = (5 * 5) mod 7" using h0
    sledgehammer
  then have "\\<dots> = 4" sledgehammer
  then have "(5 * n) mod 7 = 4" using c0 sledgehammer
  then show ?thesis sledgehammer
qed



Informal:
(*### Problem

What positive two-digit integer is exactly twice the sum of its digits? Show that it is 18.

### Solution

We simplify $10a + b = 2(a+b)$ to get $8a = b$.
Since $a$ is at least 1, $b$ is at least 8.
We know $b$ is 8 since $8a = b$ and $a$ is a natural number.
Hence $a$ is 1.
The two-digit integer is hence $18$.
*)

Formal:
theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\\<le>a \\<and> a \\<le>9 \\<and> b \\<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
proof -
  (* We simplify $10a + b = 2(a+b)$ to get $8a = b$. *)
  have c0: "8 * a = b" using h1 sledgehammer
  (* Since $a$ is at least 1, $b$ is at least 8. *)
  hence "b \\<ge> 8" using h0 sledgehammer
  (* We know $b$ is 8 since $8a = b$ and $a$ is a natural number. *)
  hence c1:"b = 8" using h0 c0
    sledgehammer
  (* Hence $a$ is 1. *)
  hence "a = 1" using c0 sledgehammer
  (* The two-digit integer is hence $18$. *)
  then show ?thesis using c1 sledgehammer
qed



Informal:
(*### Problem

Show that for any four complex numbers a, b, c, and d, $(a-d)(a-c)(a-b) = -(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$.

### Solution

We first see that $a^2 = a * a$ trivially.
Unfolding this, the main equation holds true when terms are rearranged.*)

Formal:
theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"
proof -
  (* We first see that $a^2 = a * a$ trivially. *)
  have t0: "a^2 = a * a"
    using power2_eq_square
      sledgehammer
  (* Unfolding this, the main equation holds true when terms are rearranged. *)
  show ?thesis unfolding t0
    sledgehammer
qed



Informal:
(*### Problem

For how many positive integers $n$ is $n^2 - 3n + 2$ a [[prime]] number?

$\\mathrm{(A)}\\ \\text{none}
\\qquad\\mathrm{(B)}\\ \\text{one}
\\qquad\\mathrm{(C)}\\ \\text{two}
\\qquad\\mathrm{(D)}\\ \\text{more\\ than\\ two,\\ but\\ finitely\\ many}
\\qquad\\mathrm{(E)}\\ \\text{infinitely\\ many}$ Show that it is \\mathrm{(B)}\\ \\text{one}.

### Solution

Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. 
Either $n-1$ or $n-2$ is odd, and the other is even.  
Their product must yield an even number.  
The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)

Formal:
theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
proof -
  have "n>2" 
  proof (rule ccontr)
    assume "\\<not> 2 < n"
    then have "n=1 \\<or> n=2" using \\<open>n>0\\<close> sledgehammer
    then show False using prime[THEN prime_gt_1_nat]
      sledgehammer
  qed
  (* Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. *)
  then have "n^2+2-3*n  = (n-1) * (n-2)"
    unfolding power2_eq_square
    sledgehammer
  (* Either $n-1$ or $n-2$ is odd, and the other is even.  
  Their product must yield an even number.  
  The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
  Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)
  then have "prime ((n-1) * (n-2))"
    using prime sledgehammer
  then have "n-1=1 \\<or> n-2 = 1"
    using prime_product sledgehammer
  with \\<open>n>2\\<close>
  show "n=3" sledgehammer
qed



Informal:
(*### Problem

For a positive real number a, show that $10a\\leq 28a^2+1$.

### Solution

It suffices to show $0\\leq 28a^2 - 10a + 1$.
First, consider completing the square for $28a^2 - 10a$ and observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$.
Since $0\\leq (a - \\frac{5}{28})^2$, we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$.
Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$.
Since $25/28 < 1$, the result follows.*)

Formal:
theorem algebra_binomnegdiscrineq_10alt28asqp1:
  fixes a :: real
  shows "10 * a \\<le> 28 * a^2 + 1"
proof -
(* it suffices to show $0\\leq 28a^2 - 10a + 1$ *)
  have c0: "0 \\<le> 28*a^2 - 10*a + 1"
  proof -
    (* observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    have c1: "(a - (5/28))^2 = a^2 - 10/28*a + (5/28)^2"
      sledgehammer
    (* we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    then have c2: "0 \\<le> a^2 - 10/28*a + (5/28)^2" using c1
      sledgehammer
    (* Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$ *)
    then have c3: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)^2)" using c2
      sledgehammer
    then have c4: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)*(5/28))" using c3
      sledgehammer
    then have c5: "0 \\<le> 28*a^2 - 10*a + (25/28)" using c4
      sledgehammer
    (* Since $25/28 < 1$, the result follows. *)
    then show ?thesis using c5
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.

### Solution

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.*)

Formal:
theorem algebra_2rootsintpoly_am10tap11eqasqpam110:
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
proof -
  (* We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$. *)
  have "(a-10) * (a+11) = a^2 - 10*a + 11*a - 10 *11"
    sledgehammer
  (* This equals $a^2 + a - 10*11 = a^2 + a - 110$. *)
  also have "\\<dots> = a^2 + a - 10 * 11"
    sledgehammer
  also have "\\<dots> = a^2 + a - 110"
    sledgehammer
  finally show ?thesis
    sledgehammer
qed
""".strip()

    
    def load_data(self):
        gsm8k_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/gsm8k/train.jsonl"
        math_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl"

        dataset = []
        with open(gsm8k_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_gsm8k_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                informal_proof = json_obj["answer"].split("####")[0].strip()
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })

        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })
        return dataset

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, informal_statement, informal_proof):
        return f"(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nInformal:']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]

        prompt_suffix = self.suffix_constructor(informal_statement, informal_proof)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix)
        remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens

        prompt_middle = self.sample_demonstrations(self.few_shot_prompt.split("\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"gsm8k_math-{data_idx}-{sample_idx}"
        else:
            return f"gsm8k_math-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": False,
            "n": 1, # no used
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }


class InformalToFormalMinif2fPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        # assert self.num_samples in [1, 10, 20, 50, 80, 100, 200, 300, 400, 500, 600, 700, 800, 900, 1000]
        assert isinstance(self.num_samples, int)
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation", "test_hard"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")
        self.filename_extension = "jsonl" # necessary
        self.dataset = self.load_data()
        
    def load_data(self):
        data_path = f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/{self.split}.jsonl"
        dataset = []
        with open(data_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                json_obj.update({"id": f"minif2f-{len(dataset)}"})
                dataset.append(json_obj)
        return dataset

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        formal_statement = self.dataset[data_idx]["formal_statement"]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # prompt = f"(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}\n"
        prompt = f"(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}"
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"minif2f-{data_idx}-{sample_idx}"
        else:
            return f"minif2f-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }
        
class InformalToFormalMinif2fFewshotPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 10, 20, 50, 100]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        self.few_shot_prompt = """Informal:
(*### Problem

Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. Show that it is 12.

### Solution

Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.
It is trivial to see that $y > 0$. 
Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$.
This can be done by the sum of squares method.*)

Formal:
theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \\<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
proof -
  (* Let $y = x \\sin x$. *)
  define y where "y=x * sin x"
  (* It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}. *)
  have "12 \\<le> (9 * y^2 + 4) / y"
  proof -
    (* It is trivial to see that $y > 0$. *)
    have c0: "y > 0"
      sledgehammer
    (* Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$. *)
    have "(9 * y^2 + 4) \\<ge> 12 * y" 
      sledgehammer
    then show ?thesis
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Find the greatest common factor of 180 and 168. Show that it is 12.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_188:
  "gcd 180 168 = (12::nat)"
  sledgehammer



Informal:
(*### Problem

Show that for positive integer n, 2 divides $4^n$.

### Solution

Since n is positive, we can find a natural number m where $m+1=n$.
Then we can show that 2 divides $4^{m+1}$. The conclusion thus follows.*)

Formal:
theorem numbertheory_2dvd4expn:
  fixes n :: nat
  assumes h0 : "n \\<noteq> 0"
  shows "(2::nat) dvd 4^n"
proof -
  obtain m::nat where c0: "m+1=n"
    sledgehammer
  have "(2::nat) dvd 4^(m+1)" sledgehammer
  then show ?thesis unfolding c0 sledgehammer
qed



Informal:
(*### Problem

What is the remainder when $1 + 2 + 3 + 4 + \\dots + 9 + 10$ is divided by 9? Show that it is 1.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_466:
  "(\\<Sum> k< 11. k) mod 9 = (1::nat)"
  sledgehammer



Informal:
(*### Problem

If $321_{b}$ is equal to the base 10 integer 57, find $b$ given that $b>0$. Show that it is 4.

### Solution

Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
\\\\ 3b^2+2b+1&=57
\\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
\\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
\\end{align*}This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. We know that $b>0$, so $b=4$.*)

Formal:
theorem mathd_numbertheory_48:
  fixes b :: real
  assumes h0 : "0<b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"
proof -
  (* Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
  \\\\ 3b^2+2b+1&=57
  \\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
  \\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
  \\end{align*} *)
  have "0 = 3 * b^2 + 2 * b -56" using h1 sledgehammer
  also have "... = (3*b+14)*(b-4)" sledgehammer
  finally have "0 = (3*b+14)*(b-4)" sledgehammer
  (* This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. *)
  then have "b = -14/3 ∨ b=4" sledgehammer
  (* We know that $b>0$, so $b=4$. *)
  then show ?thesis using h0 sledgehammer
qed



Informal:
(*### Problem

When Rachel divides her favorite number by 7, she gets a remainder of 5. What will the remainder be if she multiplies her favorite number by 5 and then divides by 7? Show that it is 4.

### Solution

Let $n$ be Rachel's favorite number. 
Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$.
*)

Formal:
theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  (* Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$. *)
  have c0:"(5 * n) mod 7 = (5 * 5) mod 7" using h0
    sledgehammer
  then have "\\<dots> = 4" sledgehammer
  then have "(5 * n) mod 7 = 4" using c0 sledgehammer
  then show ?thesis sledgehammer
qed



Informal:
(*### Problem

What positive two-digit integer is exactly twice the sum of its digits? Show that it is 18.

### Solution

We simplify $10a + b = 2(a+b)$ to get $8a = b$.
Since $a$ is at least 1, $b$ is at least 8.
We know $b$ is 8 since $8a = b$ and $a$ is a natural number.
Hence $a$ is 1.
The two-digit integer is hence $18$.
*)

Formal:
theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\\<le>a \\<and> a \\<le>9 \\<and> b \\<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
proof -
  (* We simplify $10a + b = 2(a+b)$ to get $8a = b$. *)
  have c0: "8 * a = b" using h1 sledgehammer
  (* Since $a$ is at least 1, $b$ is at least 8. *)
  hence "b \\<ge> 8" using h0 sledgehammer
  (* We know $b$ is 8 since $8a = b$ and $a$ is a natural number. *)
  hence c1:"b = 8" using h0 c0
    sledgehammer
  (* Hence $a$ is 1. *)
  hence "a = 1" using c0 sledgehammer
  (* The two-digit integer is hence $18$. *)
  then show ?thesis using c1 sledgehammer
qed



Informal:
(*### Problem

Show that for any four complex numbers a, b, c, and d, $(a-d)(a-c)(a-b) = -(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$.

### Solution

We first see that $a^2 = a * a$ trivially.
Unfolding this, the main equation holds true when terms are rearranged.*)

Formal:
theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"
proof -
  (* We first see that $a^2 = a * a$ trivially. *)
  have t0: "a^2 = a * a"
    using power2_eq_square
      sledgehammer
  (* Unfolding this, the main equation holds true when terms are rearranged. *)
  show ?thesis unfolding t0
    sledgehammer
qed



Informal:
(*### Problem

For how many positive integers $n$ is $n^2 - 3n + 2$ a [[prime]] number?

$\\mathrm{(A)}\\ \\text{none}
\\qquad\\mathrm{(B)}\\ \\text{one}
\\qquad\\mathrm{(C)}\\ \\text{two}
\\qquad\\mathrm{(D)}\\ \\text{more\\ than\\ two,\\ but\\ finitely\\ many}
\\qquad\\mathrm{(E)}\\ \\text{infinitely\\ many}$ Show that it is \\mathrm{(B)}\\ \\text{one}.

### Solution

Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. 
Either $n-1$ or $n-2$ is odd, and the other is even.  
Their product must yield an even number.  
The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)

Formal:
theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
proof -
  have "n>2" 
  proof (rule ccontr)
    assume "\\<not> 2 < n"
    then have "n=1 \\<or> n=2" using \\<open>n>0\\<close> sledgehammer
    then show False using prime[THEN prime_gt_1_nat]
      sledgehammer
  qed
  (* Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. *)
  then have "n^2+2-3*n  = (n-1) * (n-2)"
    unfolding power2_eq_square
    sledgehammer
  (* Either $n-1$ or $n-2$ is odd, and the other is even.  
  Their product must yield an even number.  
  The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
  Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)
  then have "prime ((n-1) * (n-2))"
    using prime sledgehammer
  then have "n-1=1 \\<or> n-2 = 1"
    using prime_product sledgehammer
  with \\<open>n>2\\<close>
  show "n=3" sledgehammer
qed



Informal:
(*### Problem

For a positive real number a, show that $10a\\leq 28a^2+1$.

### Solution

It suffices to show $0\\leq 28a^2 - 10a + 1$.
First, consider completing the square for $28a^2 - 10a$ and observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$.
Since $0\\leq (a - \\frac{5}{28})^2$, we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$.
Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$.
Since $25/28 < 1$, the result follows.*)

Formal:
theorem algebra_binomnegdiscrineq_10alt28asqp1:
  fixes a :: real
  shows "10 * a \\<le> 28 * a^2 + 1"
proof -
(* it suffices to show $0\\leq 28a^2 - 10a + 1$ *)
  have c0: "0 \\<le> 28*a^2 - 10*a + 1"
  proof -
    (* observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    have c1: "(a - (5/28))^2 = a^2 - 10/28*a + (5/28)^2"
      sledgehammer
    (* we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    then have c2: "0 \\<le> a^2 - 10/28*a + (5/28)^2" using c1
      sledgehammer
    (* Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$ *)
    then have c3: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)^2)" using c2
      sledgehammer
    then have c4: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)*(5/28))" using c3
      sledgehammer
    then have c5: "0 \\<le> 28*a^2 - 10*a + (25/28)" using c4
      sledgehammer
    (* Since $25/28 < 1$, the result follows. *)
    then show ?thesis using c5
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.

### Solution

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.*)

Formal:
theorem algebra_2rootsintpoly_am10tap11eqasqpam110:
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
proof -
  (* We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$. *)
  have "(a-10) * (a+11) = a^2 - 10*a + 11*a - 10 *11"
    sledgehammer
  (* This equals $a^2 + a - 10*11 = a^2 + a - 110$. *)
  also have "\\<dots> = a^2 + a - 10 * 11"
    sledgehammer
  also have "\\<dots> = a^2 + a - 110"
    sledgehammer
  finally show ?thesis
    sledgehammer
qed
""".strip()

        self.dataset = self.load_data()
    
    def load_data(self):
        data_path = f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/{self.split}.jsonl"
        dataset = []
        with open(data_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                json_obj.update({"id": f"minif2f-{len(dataset)}"})
                dataset.append(json_obj)
        return dataset
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, informal_statement, informal_proof, formal_statement):
        return f"Informal:\n(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nInformal:', '(*### Problem']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        formal_statement = self.dataset[data_idx]["formal_statement"]

        prompt_suffix = self.suffix_constructor(informal_statement, informal_proof, formal_statement)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix)
        remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens

        prompt_middle = self.sample_demonstrations(self.few_shot_prompt.split("\n\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"minif2f-{data_idx}-{sample_idx}"
        else:
            return f"minif2f-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_response_len, self.max_sequence_len - self.num_tokens_from_string(prompt)),
            "stop_sequences": self.stop_generation(),
        }

class AutoformalizationFewshotPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 4, 8, 16, 32, 64]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        self.few_shot_prompt = """Informal:
(*### Problem

Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. Show that it is 12.*)

Formal:
theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \\<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"



Informal:
(*### Problem

Find the greatest common factor of 180 and 168. Show that it is 12.*)

Formal:
theorem mathd_numbertheory_188:
  "gcd 180 168 = (12::nat)"



Informal:
(*### Problem

Show that for positive integer n, 2 divides $4^n$.*)

Formal:
theorem numbertheory_2dvd4expn:
  fixes n :: nat
  assumes h0 : "n \\<noteq> 0"
  shows "(2::nat) dvd 4^n"



Informal:
(*### Problem

What is the remainder when $1 + 2 + 3 + 4 + \\dots + 9 + 10$ is divided by 9? Show that it is 1.*)

Formal:
theorem mathd_numbertheory_466:
  "(\\<Sum> k< 11. k) mod 9 = (1::nat)"



Informal:
(*### Problem

If $321_{b}$ is equal to the base 10 integer 57, find $b$ given that $b>0$. Show that it is 4.*)

Formal:
theorem mathd_numbertheory_48:
  fixes b :: real
  assumes h0 : "0<b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"



Informal:
(*### Problem

When Rachel divides her favorite number by 7, she gets a remainder of 5. What will the remainder be if she multiplies her favorite number by 5 and then divides by 7? Show that it is 4.*)

Formal:
theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"



Informal:
(*### Problem

What positive two-digit integer is exactly twice the sum of its digits? Show that it is 18.*)

Formal:
theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\\<le>a \\<and> a \\<le>9 \\<and> b \\<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"



Informal:
(*### Problem

Show that for any four complex numbers a, b, c, and d, $(a-d)(a-c)(a-b) = -(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$.*)

Formal:
theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"



Informal:
(*### Problem

For how many positive integers $n$ is $n^2 - 3n + 2$ a [[prime]] number?

$\\mathrm{(A)}\\ \\text{none}
\\qquad\\mathrm{(B)}\\ \\text{one}
\\qquad\\mathrm{(C)}\\ \\text{two}
\\qquad\\mathrm{(D)}\\ \\text{more\\ than\\ two,\\ but\\ finitely\\ many}
\\qquad\\mathrm{(E)}\\ \\text{infinitely\\ many}$ Show that it is \\mathrm{(B)}\\ \\text{one}.*)

Formal:
theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"



Informal:
(*### Problem

For a positive real number a, show that $10a\\leq 28a^2+1$.*)

Formal:
theorem algebra_binomnegdiscrineq_10alt28asqp1:
  fixes a :: real
  shows "10 * a \\<le> 28 * a^2 + 1"



Informal:
(*### Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.*)

Formal:
theorem algebra_2rootsintpoly_am10tap11eqasqpam110:
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
""".strip()

        self.dataset = self.load_data()
    
    def load_data(self):
        gsm8k_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/gsm8k/train.jsonl"
        math_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl"

        dataset = []
        with open(gsm8k_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_gsm8k_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                informal_proof = json_obj["answer"].split("####")[0].strip()
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })

        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })
        return dataset
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, informal_statement):
        return f"Informal:\n(*### Problem\n\n{informal_statement}*)\n\nFormal:"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nInformal:']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        # informal_proof = self.dataset[data_idx]["informal_proof"]
        # formal_statement = self.dataset[data_idx]["formal_statement"]

        prompt_suffix = self.suffix_constructor(informal_statement)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix)
        remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens

        prompt_middle = self.sample_demonstrations(self.few_shot_prompt.split("\n\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"gsm8k_math-{data_idx}-{sample_idx}"
        else:
            return f"gsm8k_math-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }


class AutoformalizationInstructPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 4, 8, 16, 32, 64]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        
        self.dataset = self.load_data()
    
    def load_data(self):
        gsm8k_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/gsm8k/train.jsonl"
        math_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl"

        dataset = []
        with open(gsm8k_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_gsm8k_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                informal_proof = json_obj["answer"].split("####")[0].strip()
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })

        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                dataset.append({
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                    "id": f"gsm8k_math-{len(dataset)}"
                })
        return dataset
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']

    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        informal_statement = self.dataset[data_idx]["informal_statement"]
        # informal_proof = self.dataset[data_idx]["informal_proof"]
        # formal_statement = self.dataset[data_idx]["formal_statement"]

        prompt = "Use Isabelle to formalize informal math problems into precise theorem statements. Begin by defining the required variables and assumptions, then formulate the problem as a precise theorem statement.\n\n### Input\n(*Informal Statement:\n{}*)\n\n### Output".format(informal_statement)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"gsm8k_math-{data_idx}-{sample_idx}"
        else:
            return f"gsm8k_math-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }



class InformalToFormalFewshotPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 2, 4, 8]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.autoformalization_directory = kwargs.get("autoformalization_directory", "")
        assert self.autoformalization_directory != ""
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        self.few_shot_prompt = """Informal:
(*### Problem

Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. Show that it is 12.

### Solution

Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.
It is trivial to see that $y > 0$. 
Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$.
This can be done by the sum of squares method.*)

Formal:
theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \\<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
proof -
  (* Let $y = x \\sin x$. *)
  define y where "y=x * sin x"
  (* It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}. *)
  have "12 \\<le> (9 * y^2 + 4) / y"
  proof -
    (* It is trivial to see that $y > 0$. *)
    have c0: "y > 0"
      sledgehammer
    (* Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$. *)
    have "(9 * y^2 + 4) \\<ge> 12 * y" 
      sledgehammer
    then show ?thesis
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Find the greatest common factor of 180 and 168. Show that it is 12.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_188:
  "gcd 180 168 = (12::nat)"
  sledgehammer



Informal:
(*### Problem

Show that for positive integer n, 2 divides $4^n$.

### Solution

Since n is positive, we can find a natural number m where $m+1=n$.
Then we can show that 2 divides $4^{m+1}$. The conclusion thus follows.*)

Formal:
theorem numbertheory_2dvd4expn:
  fixes n :: nat
  assumes h0 : "n \\<noteq> 0"
  shows "(2::nat) dvd 4^n"
proof -
  obtain m::nat where c0: "m+1=n"
    sledgehammer
  have "(2::nat) dvd 4^(m+1)" sledgehammer
  then show ?thesis unfolding c0 sledgehammer
qed



Informal:
(*### Problem

What is the remainder when $1 + 2 + 3 + 4 + \\dots + 9 + 10$ is divided by 9? Show that it is 1.

### Solution

This is true by simple evaluation.*)

Formal:
theorem mathd_numbertheory_466:
  "(\\<Sum> k< 11. k) mod 9 = (1::nat)"
  sledgehammer



Informal:
(*### Problem

If $321_{b}$ is equal to the base 10 integer 57, find $b$ given that $b>0$. Show that it is 4.

### Solution

Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
\\\\ 3b^2+2b+1&=57
\\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
\\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
\\end{align*}This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. We know that $b>0$, so $b=4$.*)

Formal:
theorem mathd_numbertheory_48:
  fixes b :: real
  assumes h0 : "0<b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"
proof -
  (* Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
  \\\\ 3b^2+2b+1&=57
  \\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
  \\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
  \\end{align*} *)
  have "0 = 3 * b^2 + 2 * b -56" using h1 sledgehammer
  also have "... = (3*b+14)*(b-4)" sledgehammer
  finally have "0 = (3*b+14)*(b-4)" sledgehammer
  (* This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. *)
  then have "b = -14/3 ∨ b=4" sledgehammer
  (* We know that $b>0$, so $b=4$. *)
  then show ?thesis using h0 sledgehammer
qed



Informal:
(*### Problem

When Rachel divides her favorite number by 7, she gets a remainder of 5. What will the remainder be if she multiplies her favorite number by 5 and then divides by 7? Show that it is 4.

### Solution

Let $n$ be Rachel's favorite number. 
Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$.
*)

Formal:
theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  (* Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$. *)
  have c0:"(5 * n) mod 7 = (5 * 5) mod 7" using h0
    sledgehammer
  then have "\\<dots> = 4" sledgehammer
  then have "(5 * n) mod 7 = 4" using c0 sledgehammer
  then show ?thesis sledgehammer
qed



Informal:
(*### Problem

What positive two-digit integer is exactly twice the sum of its digits? Show that it is 18.

### Solution

We simplify $10a + b = 2(a+b)$ to get $8a = b$.
Since $a$ is at least 1, $b$ is at least 8.
We know $b$ is 8 since $8a = b$ and $a$ is a natural number.
Hence $a$ is 1.
The two-digit integer is hence $18$.
*)

Formal:
theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\\<le>a \\<and> a \\<le>9 \\<and> b \\<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
proof -
  (* We simplify $10a + b = 2(a+b)$ to get $8a = b$. *)
  have c0: "8 * a = b" using h1 sledgehammer
  (* Since $a$ is at least 1, $b$ is at least 8. *)
  hence "b \\<ge> 8" using h0 sledgehammer
  (* We know $b$ is 8 since $8a = b$ and $a$ is a natural number. *)
  hence c1:"b = 8" using h0 c0
    sledgehammer
  (* Hence $a$ is 1. *)
  hence "a = 1" using c0 sledgehammer
  (* The two-digit integer is hence $18$. *)
  then show ?thesis using c1 sledgehammer
qed



Informal:
(*### Problem

Show that for any four complex numbers a, b, c, and d, $(a-d)(a-c)(a-b) = -(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$.

### Solution

We first see that $a^2 = a * a$ trivially.
Unfolding this, the main equation holds true when terms are rearranged.*)

Formal:
theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"
proof -
  (* We first see that $a^2 = a * a$ trivially. *)
  have t0: "a^2 = a * a"
    using power2_eq_square
      sledgehammer
  (* Unfolding this, the main equation holds true when terms are rearranged. *)
  show ?thesis unfolding t0
    sledgehammer
qed



Informal:
(*### Problem

For how many positive integers $n$ is $n^2 - 3n + 2$ a [[prime]] number?

$\\mathrm{(A)}\\ \\text{none}
\\qquad\\mathrm{(B)}\\ \\text{one}
\\qquad\\mathrm{(C)}\\ \\text{two}
\\qquad\\mathrm{(D)}\\ \\text{more\\ than\\ two,\\ but\\ finitely\\ many}
\\qquad\\mathrm{(E)}\\ \\text{infinitely\\ many}$ Show that it is \\mathrm{(B)}\\ \\text{one}.

### Solution

Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. 
Either $n-1$ or $n-2$ is odd, and the other is even.  
Their product must yield an even number.  
The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)

Formal:
theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
proof -
  have "n>2" 
  proof (rule ccontr)
    assume "\\<not> 2 < n"
    then have "n=1 \\<or> n=2" using \\<open>n>0\\<close> sledgehammer
    then show False using prime[THEN prime_gt_1_nat]
      sledgehammer
  qed
  (* Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. *)
  then have "n^2+2-3*n  = (n-1) * (n-2)"
    unfolding power2_eq_square
    sledgehammer
  (* Either $n-1$ or $n-2$ is odd, and the other is even.  
  Their product must yield an even number.  
  The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
  Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)
  then have "prime ((n-1) * (n-2))"
    using prime sledgehammer
  then have "n-1=1 \\<or> n-2 = 1"
    using prime_product sledgehammer
  with \\<open>n>2\\<close>
  show "n=3" sledgehammer
qed



Informal:
(*### Problem

For a positive real number a, show that $10a\\leq 28a^2+1$.

### Solution

It suffices to show $0\\leq 28a^2 - 10a + 1$.
First, consider completing the square for $28a^2 - 10a$ and observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$.
Since $0\\leq (a - \\frac{5}{28})^2$, we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$.
Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$.
Since $25/28 < 1$, the result follows.*)

Formal:
theorem algebra_binomnegdiscrineq_10alt28asqp1:
  fixes a :: real
  shows "10 * a \\<le> 28 * a^2 + 1"
proof -
(* it suffices to show $0\\leq 28a^2 - 10a + 1$ *)
  have c0: "0 \\<le> 28*a^2 - 10*a + 1"
  proof -
    (* observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    have c1: "(a - (5/28))^2 = a^2 - 10/28*a + (5/28)^2"
      sledgehammer
    (* we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    then have c2: "0 \\<le> a^2 - 10/28*a + (5/28)^2" using c1
      sledgehammer
    (* Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$ *)
    then have c3: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)^2)" using c2
      sledgehammer
    then have c4: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)*(5/28))" using c3
      sledgehammer
    then have c5: "0 \\<le> 28*a^2 - 10*a + (25/28)" using c4
      sledgehammer
    (* Since $25/28 < 1$, the result follows. *)
    then show ?thesis using c5
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed



Informal:
(*### Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.

### Solution

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.*)

Formal:
theorem algebra_2rootsintpoly_am10tap11eqasqpam110:
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
proof -
  (* We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$. *)
  have "(a-10) * (a+11) = a^2 - 10*a + 11*a - 10 *11"
    sledgehammer
  (* This equals $a^2 + a - 10*11 = a^2 + a - 110$. *)
  also have "\\<dots> = a^2 + a - 10 * 11"
    sledgehammer
  also have "\\<dots> = a^2 + a - 110"
    sledgehammer
  finally show ?thesis
    sledgehammer
qed
""".strip()

        # self.dataset = self.load_data()
        self.dataset = h5py.File(f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/{os.path.basename(self.autoformalization_directory)}.hdf5")
        self.groups = sorted(list(self.dataset.keys()), key=lambda x:int(x))
        assert len(self.groups) == int(self.groups[-1]) + 1
    
    def load_data(self):
        gsm8k_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/gsm8k/train.jsonl"
        math_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl"
        
        data_dict = {}
        with open(gsm8k_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_gsm8k_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                informal_proof = json_obj["answer"].split("####")[0].strip()
                data_dict[f"gsm8k_math-{len(data_dict)}"] = {
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                }

        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                data_dict[f"gsm8k_math-{len(data_dict)}"] = {
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                }
        
        dataset = []
        files = [file.split(".")[0] for file in os.listdir(self.autoformalization_directory) if file.endswith(self.filename_extension)]
        
        if len(files[0].split("-")) == 3:
            largest_sample_number = max([int(filename.split("-")[2]) + 1 for filename in files])
            assert len(files) == largest_sample_number * len(data_dict), "This can only be invoked once the autoformalization stage is fully completed."
            get_id = lambda x: f'{x.split("-")[0]}-{int(x.split("-")[1]) * largest_sample_number + int(x.split("-")[2])}'
            print(f"The number of samples in the autoformalization stage is {largest_sample_number}.")
        else:
            assert len(files) == len(data_dict), "This can only be invoked once the autoformalization stage is fully completed."
            get_id = lambda x: f'{x.split("-")[0]}-{int(x.split("-")[1])}'
        
        sorted_files = sorted(files, key=lambda x: tuple(int(part) for part in x.rsplit('-', 2)[1:]))
        for file in sorted_files:
            with open(os.path.join(self.autoformalization_directory, f"{file}.jsonl"), encoding="utf-8") as f:
                for line in f.readlines():
                    formal_statement = json.loads(line)["prediction"].strip()
                    break
            
            base_key = "-".join(file.split("-")[:2])
            dataset.append({
                "informal_statement": data_dict[base_key]["informal_statement"],
                "informal_proof": data_dict[base_key]["informal_proof"],
                "formal_statement": formal_statement,
                "id": get_id(file)
            })
        return dataset
    
    def get_data(self, idx, key=None):
        grp = self.groups[idx]
        grp = self.groups[idx // self.num_samples]
        # sample_idx = idx % self.num_samples
        data = {
            "id": self.dataset[grp]["id"][()].decode(),
            "informal_statement": self.dataset[grp]["informal_statement"][()].decode(),
            "informal_proof": self.dataset[grp]["informal_proof"][()].decode(),
            "formal_statement": self.dataset[grp]["formal_statement"][()].decode(),
        }
        if key is not None:
            return data[key]
        else:
            return data
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{self.dataset[grp]['id'][()].decode()}-{i}" for grp in self.groups for i in range(self.num_samples)]
        else:
            return [self.dataset[grp]['id'][()].decode() for grp in self.groups]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, informal_statement, informal_proof, formal_statement):
        return f"Informal:\n(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nInformal:']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget-10:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples
        
        informal_statement = self.get_data(data_idx, "informal_statement")
        informal_proof = self.get_data(data_idx, "informal_proof")
        formal_statement = self.get_data(data_idx, "formal_statement")

        prompt_suffix = self.suffix_constructor(informal_statement, informal_proof, formal_statement)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix)
        remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens

        prompt_middle = self.sample_demonstrations(self.few_shot_prompt.split("\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.groups) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = set([extract_task_id(file_name) for file_name in file_names if file_name.endswith(self.filename_extension)])
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.groups) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"gsm8k_math-{data_idx}-{sample_idx}"
        else:
            return f"gsm8k_math-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        
        return self.get_data(data_idx)

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.get_data(data_idx)

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_response_len, self.max_sequence_len - self.num_tokens_from_string(prompt)),
            "stop_sequences": self.stop_generation(),
        }



class InformalToFormalInstructPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 2, 4, 8]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.autoformalization_directory = kwargs.get("autoformalization_directory", "")
        assert self.autoformalization_directory != ""
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        # self.dataset = self.load_data()
        self.dataset = h5py.File(f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/{os.path.basename(self.autoformalization_directory)}.hdf5")
        self.groups = sorted(list(self.dataset.keys()), key=lambda x:int(x))
        assert len(self.groups) == int(self.groups[-1]) + 1
    
    def load_data(self):
        gsm8k_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/gsm8k/train.jsonl"
        math_path = "/import/snvm-sc-scratch2/xueliangz/Data/datasets/math/train.jsonl"
        
        data_dict = {}
        with open(gsm8k_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_gsm8k_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                informal_proof = json_obj["answer"].split("####")[0].strip()
                data_dict[f"gsm8k_math-{len(data_dict)}"] = {
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                }

        with open(math_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                final_answer = extract_math_final_answer(json_obj["answer"])
                informal_statement = f"{json_obj['question'].strip()} Show that it is {final_answer}."
                string_to_replace = last_boxed_only_string(json_obj["answer"])
                if string_to_replace is not None and string_to_replace in json_obj["answer"]:
                    informal_proof = json_obj["answer"].replace(string_to_replace, final_answer)
                else:
                    informal_proof = json_obj["answer"]
                data_dict[f"gsm8k_math-{len(data_dict)}"] = {
                    "informal_statement": informal_statement,
                    "informal_proof": informal_proof,
                }
        
        dataset = []
        files = [file.split(".")[0] for file in os.listdir(self.autoformalization_directory) if file.endswith(self.filename_extension)]
        
        if len(files[0].split("-")) == 3:
            largest_sample_number = max([int(filename.split("-")[2]) + 1 for filename in files])
            assert len(files) == largest_sample_number * len(data_dict), "This can only be invoked once the autoformalization stage is fully completed."
            get_id = lambda x: f'{x.split("-")[0]}-{int(x.split("-")[1]) * largest_sample_number + int(x.split("-")[2])}'
            print(f"The number of samples in the autoformalization stage is {largest_sample_number}.")
        else:
            assert len(files) == len(data_dict), "This can only be invoked once the autoformalization stage is fully completed."
            get_id = lambda x: f'{x.split("-")[0]}-{int(x.split("-")[1])}'
        
        sorted_files = sorted(files, key=lambda x: tuple(int(part) for part in x.rsplit('-', 2)[1:]))
        for file in sorted_files:
            with open(os.path.join(self.autoformalization_directory, f"{file}.jsonl"), encoding="utf-8") as f:
                for line in f.readlines():
                    formal_statement = json.loads(line)["prediction"].strip()
                    break
            
            base_key = "-".join(file.split("-")[:2])
            dataset.append({
                "informal_statement": data_dict[base_key]["informal_statement"],
                "informal_proof": data_dict[base_key]["informal_proof"],
                "formal_statement": formal_statement,
                "id": get_id(file)
            })
        return dataset
    
    def get_data(self, idx, key=None):
        # grp = self.groups[idx]
        grp = self.groups[idx // self.num_samples]
        # sample_idx = idx % self.num_samples
        data = {
            "id": self.dataset[grp]["id"][()].decode(),
            "informal_statement": self.dataset[grp]["informal_statement"][()].decode(),
            "informal_proof": self.dataset[grp]["informal_proof"][()].decode(),
            "formal_statement": self.dataset[grp]["formal_statement"][()].decode(),
        }
        if key is not None:
            return data[key]
        else:
            return data
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{self.dataset[grp]['id'][()].decode()}-{i}" for grp in self.groups for i in range(self.num_samples)]
        else:
            return [self.dataset[grp]['id'][()].decode() for grp in self.groups]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']

    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples
        
        informal_statement = self.get_data(data_idx, "informal_statement")
        informal_proof = self.get_data(data_idx, "informal_proof")
        formal_statement = self.get_data(data_idx, "formal_statement")

        prompt = "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output".format(informal_statement, formal_statement, informal_proof)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.groups) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = set([extract_task_id(file_name) for file_name in file_names if file_name.endswith(self.filename_extension)])
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.groups) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"gsm8k_math-{data_idx}-{sample_idx}"
        else:
            return f"gsm8k_math-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        
        return self.get_data(data_idx)

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.get_data(data_idx)

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_response_len, self.max_sequence_len - self.num_tokens_from_string(prompt)),
            "stop_sequences": self.stop_generation(),
        }



class FormalToInformalFewshotPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 2, 4, 8]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")

        self.filename_extension = "jsonl" # necessary
        self.few_shot_prompt = """Formal:
theorem aime_1983_p9:
  fixes x::real
  assumes "0<x" "x<pi"
  shows "12 \\<le> ((9 * (x^2 * (sin x)^2)) + 4) / (x * sin x)"
proof -
  (* Let $y = x \\sin x$. *)
  define y where "y=x * sin x"
  (* It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}. *)
  have "12 \\<le> (9 * y^2 + 4) / y"
  proof -
    (* It is trivial to see that $y > 0$. *)
    have c0: "y > 0"
      sledgehammer
    (* Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$. *)
    have "(9 * y^2 + 4) \\<ge> 12 * y" 
      sledgehammer
    then show ?thesis
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed

Informal:
(*### Problem

Find the minimum value of $\\frac{9x^2\\sin^2 x + 4}{x\\sin x}$ for $0 < x < \\pi$. Show that it is 12.

### Solution

Let $y = x \\sin x$. It suffices to show that $12 \\leq \\frac{9y^2 + 4}{y}.
It is trivial to see that $y > 0$. 
Then one can multiply both sides by $y$ and it suffices to show $12y \\leq 9y^2 + 4$.
This can be done by the sum of squares method.*)



Formal:
theorem mathd_numbertheory_188:
  "gcd 180 168 = (12::nat)"
  sledgehammer

Informal:
(*### Problem

Find the greatest common factor of 180 and 168. Show that it is 12.

### Solution

This is true by simple evaluation.*)



Formal:
theorem numbertheory_2dvd4expn:
  fixes n :: nat
  assumes h0 : "n \\<noteq> 0"
  shows "(2::nat) dvd 4^n"
proof -
  obtain m::nat where c0: "m+1=n"
    sledgehammer
  have "(2::nat) dvd 4^(m+1)" sledgehammer
  then show ?thesis unfolding c0 sledgehammer
qed

Informal:
(*### Problem

Show that for positive integer n, 2 divides $4^n$.

### Solution

Since n is positive, we can find a natural number m where $m+1=n$.
Then we can show that 2 divides $4^{m+1}$. The conclusion thus follows.*)



Formal:
theorem mathd_numbertheory_466:
  "(\\<Sum> k< 11. k) mod 9 = (1::nat)"
  sledgehammer

Informal:
(*### Problem

What is the remainder when $1 + 2 + 3 + 4 + \\dots + 9 + 10$ is divided by 9? Show that it is 1.

### Solution

This is true by simple evaluation.*)



Formal:
theorem mathd_numbertheory_48:
  fixes b :: real
  assumes h0 : "0<b"
    and h1 : "3 * b^2 + 2 * b + 1 = 57"
  shows "b=4"
proof -
  (* Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
  \\\\ 3b^2+2b+1&=57
  \\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
  \\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
  \\end{align*} *)
  have "0 = 3 * b^2 + 2 * b -56" using h1 sledgehammer
  also have "... = (3*b+14)*(b-4)" sledgehammer
  finally have "0 = (3*b+14)*(b-4)" sledgehammer
  (* This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. *)
  then have "b = -14/3 ∨ b=4" sledgehammer
  (* We know that $b>0$, so $b=4$. *)
  then show ?thesis using h0 sledgehammer
qed

Informal:
(*### Problem

If $321_{b}$ is equal to the base 10 integer 57, find $b$ given that $b>0$. Show that it is 4.

### Solution

Converting $321_{b}$ to base 10 and setting it equal to 57, we find that  \\begin{align*} 3(b^2)+2(b^1)+1(b^0)&=57
\\\\ 3b^2+2b+1&=57
\\\\\\Rightarrow\\qquad 3b^2+2b-56&=0
\\\\\\Rightarrow\\qquad (3b+14)(b-4)&=0
\\end{align*}This tells us that $b$ is either $-\\frac{14}{3}$ or $4$. We know that $b>0$, so $b=4$.*)



Formal:
theorem mathd_numbertheory_335:
  fixes n :: nat
  assumes h0 : "n mod 7 = 5"
  shows "(5 * n) mod 7 = 4"
proof -
  (* Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$. *)
  have c0:"(5 * n) mod 7 = (5 * 5) mod 7" using h0
    sledgehammer
  then have "\\<dots> = 4" sledgehammer
  then have "(5 * n) mod 7 = 4" using c0 sledgehammer
  then show ?thesis sledgehammer
qed

Informal:
(*### Problem

When Rachel divides her favorite number by 7, she gets a remainder of 5. What will the remainder be if she multiplies her favorite number by 5 and then divides by 7? Show that it is 4.

### Solution

Let $n$ be Rachel's favorite number. 
Then $n \\equiv 5 \\pmod{7}$, so $5n \\equiv 5 \\cdot 5 \\equiv 25 \\equiv 4 \\pmod{7}$.*)



Formal:
theorem mathd_numbertheory_284:
  fixes a b :: nat
  assumes h0 : "1\\<le>a \\<and> a \\<le>9 \\<and> b \\<le>9"
    and h1 : "10 * a + b = 2 * (a+b)"
  shows "10 * a + b = 18"
proof -
  (* We simplify $10a + b = 2(a+b)$ to get $8a = b$. *)
  have c0: "8 * a = b" using h1 sledgehammer
  (* Since $a$ is at least 1, $b$ is at least 8. *)
  hence "b \\<ge> 8" using h0 sledgehammer
  (* We know $b$ is 8 since $8a = b$ and $a$ is a natural number. *)
  hence c1:"b = 8" using h0 c0
    sledgehammer
  (* Hence $a$ is 1. *)
  hence "a = 1" using c0 sledgehammer
  (* The two-digit integer is hence $18$. *)
  then show ?thesis using c1 sledgehammer
qed

Informal:
(*### Problem

What positive two-digit integer is exactly twice the sum of its digits? Show that it is 18.

### Solution

We simplify $10a + b = 2(a+b)$ to get $8a = b$.
Since $a$ is at least 1, $b$ is at least 8.
We know $b$ is 8 since $8a = b$ and $a$ is a natural number.
Hence $a$ is 1.
The two-digit integer is hence $18$.*)



Formal:
theorem algebra_3rootspoly_amdtamctambeqnasqmbpctapcbtdpasqmbpctapcbta:
  fixes a b c d :: complex
  shows "(a-d) * (a-c) * (a-b) = -(((a^2 - (b+c) * a) + c * b) * d) + (a^2 - (b+c) * a + c * b) * a"
proof -
  (* We first see that $a^2 = a * a$ trivially. *)
  have t0: "a^2 = a * a"
    using power2_eq_square
      sledgehammer
  (* Unfolding this, the main equation holds true when terms are rearranged. *)
  show ?thesis unfolding t0
    sledgehammer
qed

Informal:
(*### Problem

Show that for any four complex numbers a, b, c, and d, $(a-d)(a-c)(a-b) = -(((a^2 - a(b+c)) + bc) * d) + (a^2 - a(b+c) + bc) * a$.

### Solution

We first see that $a^2 = a * a$ trivially.
Unfolding this, the main equation holds true when terms are rearranged.*)



Formal:
theorem amc12b_2002_p3:
  fixes n ::nat
  assumes "n>0"
    and prime:"prime (n^2+2-3*n)"
  shows "n=3"
proof -
  have "n>2" 
  proof (rule ccontr)
    assume "\\<not> 2 < n"
    then have "n=1 \\<or> n=2" using \\<open>n>0\\<close> sledgehammer
    then show False using prime[THEN prime_gt_1_nat]
      sledgehammer
  qed
  (* Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. *)
  then have "n^2+2-3*n  = (n-1) * (n-2)"
    unfolding power2_eq_square
    sledgehammer
  (* Either $n-1$ or $n-2$ is odd, and the other is even.  
  Their product must yield an even number.  
  The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
  Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)
  then have "prime ((n-1) * (n-2))"
    using prime sledgehammer
  then have "n-1=1 \\<or> n-2 = 1"
    using prime_product sledgehammer
  with \\<open>n>2\\<close>
  show "n=3" sledgehammer
qed

Informal:
(*### Problem

For how many positive integers $n$ is $n^2 - 3n + 2$ a [[prime]] number?

$\\mathrm{(A)}\\ \\text{none}
\\qquad\\mathrm{(B)}\\ \\text{one}
\\qquad\\mathrm{(C)}\\ \\text{two}
\\qquad\\mathrm{(D)}\\ \\text{more\\ than\\ two,\\ but\\ finitely\\ many}
\\qquad\\mathrm{(E)}\\ \\text{infinitely\\ many}$ Show that it is \\mathrm{(B)}\\ \\text{one}.

### Solution

Factoring, we get $n^2 - 3n + 2 = (n-2)(n-1)$. 
Either $n-1$ or $n-2$ is odd, and the other is even.  
Their product must yield an even number.  
The only prime that is even is $2$, which is when $n$ is $3$ or $0$. 
Since $0$ is not a positive number, the answer is $\\mathrm{(B)}\\ \\text{one}$.*)



Formal:
theorem algebra_binomnegdiscrineq_10alt28asqp1:
  fixes a :: real
  shows "10 * a \\<le> 28 * a^2 + 1"
proof -
(* it suffices to show $0\\leq 28a^2 - 10a + 1$ *)
  have c0: "0 \\<le> 28*a^2 - 10*a + 1"
  proof -
    (* observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    have c1: "(a - (5/28))^2 = a^2 - 10/28*a + (5/28)^2"
      sledgehammer
    (* we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$ *)
    then have c2: "0 \\<le> a^2 - 10/28*a + (5/28)^2" using c1
      sledgehammer
    (* Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$ *)
    then have c3: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)^2)" using c2
      sledgehammer
    then have c4: "0 \\<le> 28*a^2 - 10*a + 28*((5/28)*(5/28))" using c3
      sledgehammer
    then have c5: "0 \\<le> 28*a^2 - 10*a + (25/28)" using c4
      sledgehammer
    (* Since $25/28 < 1$, the result follows. *)
    then show ?thesis using c5
      sledgehammer
  qed
  then show ?thesis
    sledgehammer
qed

Informal:
(*### Problem

For a positive real number a, show that $10a\\leq 28a^2+1$.

### Solution

It suffices to show $0\\leq 28a^2 - 10a + 1$.
First, consider completing the square for $28a^2 - 10a$ and observe that $(a - \\frac{5}{28})^2 = a^2 - \\frac{10}{28}a + (5/28)^2$.
Since $0\\leq (a - \\frac{5}{28})^2$, we have $0\\leq a^2 - \\frac{10}{28}a + (5/28)^2$.
Multiplying by 28 and simplifying terms gives $0\\leq 28*a^2 - 10*a + (25/28)$.
Since $25/28 < 1$, the result follows.*)



Formal:
theorem algebra_2rootsintpoly_am10tap11eqasqpam110:
  fixes a :: complex
  shows "(a-10) * (a+11) = a^2 + a -110"
proof -
  (* We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$. *)
  have "(a-10) * (a+11) = a^2 - 10*a + 11*a - 10 *11"
    sledgehammer
  (* This equals $a^2 + a - 10*11 = a^2 + a - 110$. *)
  also have "\\<dots> = a^2 + a - 10 * 11"
    sledgehammer
  also have "\\<dots> = a^2 + a - 110"
    sledgehammer
  finally show ?thesis
    sledgehammer
qed

Informal:
(*### Problem

Show that for any complex number a, $(a-10)(a+11) = a^2 + a - 110$.

### Solution

We first expand all terms of the left hand side to get $a^2 - 10a + 11a - 10*11$.
This equals $a^2 + a - 10*11 = a^2 + a - 110$.*)
""".strip()

        self.dataset = h5py.File(f"/import/snvm-sc-scratch2/xueliangz/Data/hdf5_data/afp_train_154k.hdf5")
        self.groups = sorted(list(self.dataset.keys()), key=lambda x:int(x))
        assert len(self.groups) == int(self.groups[-1]) + 1
        
    def get_data(self, idx, key=None):
        grp = self.groups[idx // self.num_samples]
        # sample_idx = idx % self.num_samples
        data = {
            "id": self.dataset[grp]["id"][()].decode(),
            "formal_statement": self.dataset[grp]["formal_statement"][()].decode(),
            "formal_proof": self.dataset[grp]["formal_proof"][()].decode(),
        }
        if key is not None:
            return data[key]
        else:
            return data
    
    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{self.dataset[grp]['id'][()].decode()}-{i}" for grp in self.groups for i in range(self.num_samples)]
        else:
            return [self.dataset[grp]['id'][()].decode() for grp in self.groups]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def suffix_constructor(self, formal_statement, formal_proof):
        return f"Formal:\n{formal_statement}\n{formal_proof}\n\nInformal:"

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>', '\nFormal:']

    def randomize_demonstrations(self, demonstrations, budget):
        for _ in range(300):
            random.shuffle(demonstrations)
            if self.num_tokens_from_string("\n\n".join([demo for demo in demonstrations[:3]])) < budget:
                break
        return demonstrations

    def sample_demonstrations(self, demonstrations, budget=3072):
        assert len(demonstrations) == 11
        sorted_demonstrations = self.randomize_demonstrations(demonstrations, budget=budget-10)

        used = 0
        processed_sampled_prompts = []
        for demo in sorted_demonstrations:
            sampled_prompt = demo.strip()
            to_add = self.num_tokens_from_string("{}\n\n".format(sampled_prompt))
            if used + to_add > budget-10:
                break
            else:
                used += to_add
                processed_sampled_prompts.append(sampled_prompt)
        prompt_string  = "\n\n".join(processed_sampled_prompts)
        return prompt_string
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples
        
        formal_statement = self.get_data(data_idx, "formal_statement")
        formal_proof = self.get_data(data_idx, "formal_proof")

        prompt_suffix = self.suffix_constructor(formal_statement, formal_proof)
        suffix_tokens = self.num_tokens_from_string(prompt_suffix)
        remain_budget = self.max_sequence_len - self.max_response_len - suffix_tokens

        prompt_middle = self.sample_demonstrations(self.few_shot_prompt.split("\n\n\n\n"), budget=remain_budget)
        prompt = "{}\n\n{}".format(prompt_middle, prompt_suffix)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.groups) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = set([extract_task_id(file_name) for file_name in file_names if file_name.endswith(self.filename_extension)])
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        # cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        cmd = f'find {directory} -maxdepth 1 -name "*.{self.filename_extension}" -print | xargs ls -lt | wc -l'
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.groups) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"afp-{data_idx}-{sample_idx}"
        else:
            return f"afp-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        
        return self.get_data(data_idx)

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.get_data(data_idx)

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": min(self.max_response_len, self.max_sequence_len - self.num_tokens_from_string(prompt)),
            "stop_sequences": self.stop_generation(),
        }

class InformalToFormalMinif2fInstructPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 10, 20, 50, 80, 100]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")
        self.filename_extension = "jsonl" # necessary
        self.FORMAL_PROOF_TEMPLATE = "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output"
        self.dataset = self.load_data()
        
    def load_data(self):
        data_path = f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/{self.split}.jsonl"
        dataset = []
        with open(data_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                json_obj.update({"id": f"minif2f-{len(dataset)}"})
                dataset.append(json_obj)
        return dataset

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        # sample_idx = idx % self.num_samples

        formal_statement = self.dataset[data_idx]["formal_statement"]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # prompt = f"(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}\n"
        # prompt = f"(*### Problem\n\n{informal_statement}\n\n### Solution\n\n{informal_proof}*)\n\nFormal:\n{formal_statement}"
        prompt = self.FORMAL_PROOF_TEMPLATE.format(informal_statement, formal_statement, informal_proof)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"minif2f-{data_idx}-{sample_idx}"
        else:
            return f"minif2f-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }
   

class InformalToFormalMinif2fMultiInstructPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 10, 20, 50, 80, 100]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")
        self.filename_extension = "jsonl" # necessary
        # self.FORMAL_PROOF_TEMPLATE = "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output"
        self.instructions = [
            "Employ the Isabelle proof assistant to systematically validate theorem statements, utilizing tools such as Sledgehammer for support in the proof process.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output",
            "Utilize Isabelle for the systematic verification of theorem statements, and employ tools like Sledgehammer to aid in these proofs.\n\n### Problem\n{}\n\n### Proof\n{}\n(*{}*)",
            "Systematically prove theorem statements using Isabelle, and incorporate tools like Sledgehammer to facilitate the proof effort.\n\n### Problem\n{}\n\n### Proof\n{}\n(*Sketch:\n{}*)",
            "In the process of systematically proving theorem statements, use Isabelle and leverage tools such as Sledgehammer for assistance.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}\n(*{}*)",
            "For systematic theorem statement verification, apply Isabelle and make use of supplementary tools like Sledgehammer.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}\n(*Let's think step by step. {}*)",
            "Engage Isabelle to methodically establish the validity of theorem statements, using auxiliary tools like Sledgehammer for enhanced proving capability.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output",
            "Adopt Isabelle for the systematic assertion of theorem statements, assisted by tools such as Sledgehammer for proving support.\n\n### Problem\n{}\n\n### Proof\n{}\n(*{}*)",
            "Systematically ascertain theorem statements through Isabelle, using supportive tools like Sledgehammer to streamline the proving process.\n\n### Problem\n{}\n\n### Proof\n{}\n(*Sketch:\n{}*)",
            "Harness Isabelle to methodically prove theorem statements, with the aid of tools like Sledgehammer to expedite the proof work.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}\n(*{}*)",
            "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}\n(*Let's think step by step. {}*)"
        ]
        self.dataset = self.load_data()
        
    def load_data(self):
        data_path = f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/{self.split}.jsonl"
        dataset = []
        with open(data_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                json_obj.update({"id": f"minif2f-{len(dataset)}"})
                dataset.append(json_obj)
        return dataset

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        formal_statement = self.dataset[data_idx]["formal_statement"]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # template = random.choice(self.instructions)
        template = self.instructions[sample_idx % len(self.instructions)]
        prompt = template.format(informal_statement, formal_statement, informal_proof)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"minif2f-{data_idx}-{sample_idx}"
        else:
            return f"minif2f-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }
   


class InformalToFormalMinif2fTwoInstructPromptManager:
    def __init__(self, max_response_len, **kwargs):
        self.num_samples = kwargs.get("num_samples", None)
        assert self.num_samples in [1, 10, 20, 50, 80, 100]
        self.split = kwargs.get("split", None)
        assert self.split in ["test", "validation"]
        self.temperature = kwargs.get("temperature", None)
        assert self.temperature in [0.0, 0.2, 0.4, 0.6, 0.8, 1.0]
        self.max_sequence_len = 4096 # necessary
        self.max_response_len = max_response_len # necessary
        self.tokenizer = AutoTokenizer.from_pretrained("/import/snvm-sc-scratch2/xueliangz/checkpoints/deepseek-math-7b-base")
        self.filename_extension = "jsonl" # necessary
        # self.FORMAL_PROOF_TEMPLATE = "Use Isabelle to systematically prove theorem statements. Use tools like sledgehammer to assist in proving.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output"
        self.instructions = [
            "Develop formal proofs using Isabelle, leveraging auxiliary tools such as Sledgehammer to enhance the proving process.\n\n### Input\n(*Informal Statement:\n{}*)\n{}\n(*Informal Proof:\n{}*)\n\n### Output",
            "Utilize Isabelle for the systematic verification of theorem proofs, employing Sledgehammer as a supplementary tool. Approach the problem in a step-by-step manner.\n\n### Problem\n{}\n\n### Isabelle Proof\n{}\n(*Let's think step by step. {}*)",
        ]
        self.dataset = self.load_data()
        
    def load_data(self):
        data_path = f"/import/snvm-sc-scratch2/xueliangz/Data/datasets/miniF2F/{self.split}.jsonl"
        dataset = []
        with open(data_path, encoding="utf-8") as f:
            for line in f.readlines():
                json_obj = json.loads(line)
                json_obj.update({"id": f"minif2f-{len(dataset)}"})
                dataset.append(json_obj)
        return dataset

    def get_tasks(self):
        if self.num_samples > 1:
            return [f"{data['id']}-{i}" for data in self.dataset for i in range(self.num_samples)]
        else:
            return [data['id'] for data in self.dataset]

    def num_tokens_from_string(self, string: str) -> int: # necessary
        return len(self.tokenizer.encode(string))

    def stop_generation(self):
        return ['<｜end▁of▁sentence｜>']
    
    def get_prompt(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        formal_statement = self.dataset[data_idx]["formal_statement"]
        informal_statement = self.dataset[data_idx]["informal_statement"]
        informal_proof = self.dataset[data_idx]["informal_proof"]
        # template = random.choice(self.instructions)
        template = self.instructions[sample_idx % len(self.instructions)]
        prompt = template.format(informal_statement, formal_statement, informal_proof)
        return prompt

    def get_num_prompts(self): # necessary
        return len(self.dataset) * self.num_samples
    
    def find_unfinished_prompts(self, directory):
        file_names = os.listdir(directory)
        finished = [extract_task_id(file_name) for file_name in file_names]
        unfinished = [task for task in self.get_tasks() if task not in finished]
        if self.num_samples > 1:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-2]) * self.num_samples + int(x.split("-")[-1]))
        else:
            sorted_unfinished = sorted(unfinished, key=lambda x: int(x.split("-")[-1]))
        return sorted_unfinished
    
    def are_all_workers_finished(self, directory): # necessary
        # cmd = f"ls -lt {directory} | grep 'json' | wc -l"
        cmd = f"ls -lt {directory}/*.{self.filename_extension} | wc -l"
        output = subprocess.check_output(cmd, shell=True, text=True)
        if int(output.strip()) == len(self.dataset) * self.num_samples:
            return True
        else:
            return False
    
    def distribute_tasks_to_workers(self, directory, num_workers): # necessary
        unfinished = self.find_unfinished_prompts(directory)
        tasks_per_worker = math.ceil(len(unfinished) / num_workers)
        start_indices = [0]
        for i in range(tasks_per_worker, len(unfinished), tasks_per_worker):
            task = unfinished[i]
            if self.num_samples > 1:
                start_index = int(task.split("-")[-2]) * self.num_samples + int(task.split("-")[-1])
            else:
                start_index = int(task.split("-")[-1])
            start_indices.append(start_index)
        # assert len(start_indices) == num_workers
        return start_indices

    def get_task_name(self, idx): # necessary
        data_idx = idx // self.num_samples
        sample_idx = idx % self.num_samples
        if self.num_samples > 1:
            return f"minif2f-{data_idx}-{sample_idx}"
        else:
            return f"minif2f-{data_idx}"
    
    def get_data_from_task_name(self, task_name):
        if self.num_samples > 1:
            data_idx = int(task_name.split("-")[-2])
        else:
            data_idx = int(task_name.split("-")[-1])
        return self.dataset[data_idx]

    def get_data_from_index(self, idx):
        data_idx = idx // self.num_samples
        return self.dataset[data_idx]

    def get_generation_config(self, prompt): # necessary
        return {
            "prompt": prompt,
            "do_sample": True if self.num_samples > 1 else False,
            "n": 1, # no used
            "temperature": self.temperature,
            "max_tokens": self.max_response_len,
            "stop_sequences": self.stop_generation(),
        }
   

if __name__ == "__main__":
    # prompt_manager = FormalToInformalFewshotPromptManager(max_response_len=1024, split="test", num_samples=1, temperature=0.6)
    # print("prompt: ")
    # print(prompt_manager.get_prompt(41504))
    # print(prompt_manager.num_tokens_from_string(prompt_manager.get_prompt(41504)))
    # print("data: ")
    # print(prompt_manager.get_data_from_index(41504))
    # print("task: ")
    # print(prompt_manager.get_task_name(41504))
    # print("data-2: ")
    # print(prompt_manager.get_data_from_task_name(prompt_manager.get_task_name(41504)))

    prompt_manager = InformalToFormalInstructPromptManager(max_response_len=1024, split="test", num_samples=1, temperature=0.6, autoformalization_directory="/import/snvm-sc-scratch2/xueliangz/SambaProver/informal_to_formal/0513_autoformalization_instruct")
    print("prompt: ")
    print(prompt_manager.get_prompt(87854))
    print(prompt_manager.num_tokens_from_string(prompt_manager.get_prompt(87854)))
    print("data: ")
    print(prompt_manager.get_data_from_index(87854))
    print("task: ")
    print(prompt_manager.get_task_name(87854))
    print("data-2: ")
    print(prompt_manager.get_data_from_task_name(prompt_manager.get_task_name(87854)))