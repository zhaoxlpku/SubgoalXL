import json
import os
import re
import subprocess
import time

import psutil

from pisa_client import initialise_env


class Checker(object):
    def __init__(self, working_dir, isa_path, theory_file, port=9000):
        self.working_dir = working_dir
        self.isa_path = isa_path
        self.theory_file = theory_file
        self.port = port

    def _initialize(self):
        print("Initializing environment")
        print("ISA_PATH: %s" % self.isa_path)
        print("THEORY_FILE: %s" % self.theory_file)
        print("WORKING_DIR: %s" % self.working_dir)
        env = initialise_env(
            self.port,
            working_directory=self.working_dir,
            isa_path=self.isa_path,
            theory_file_path=self.theory_file
        )
        print("Start initialising environment")
        env.post('<initialise>')
        return env

    def _exit(self, env):
        try:
            env.post('exit')
        except:
            print("env.post('exit') timed out")
            pass
        # except Exception as e:
        #     print("An exception happened: {}".format(e))
        # check whether it is necessary
        # os.system("ps aux | grep Isabelle | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")
        # os.system("ps aux | grep poly | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")

    def _parse_output(self, obs):
        """Parse the sledgehammer output, otherwise return an empty string"""
        if '<hammer>' in obs:
            output = obs.split('<hammer>')[0]
        else:
            output = ''
        return output

    def _run_step(self, step, i, tls_name, env):
        obs, reward, done, metadata = env.step_to_top_level_state(
            action=step,
            tls_name=tls_name,
            new_name='default_%d' % i
        )
        error = None
        if 'error:' in obs or 'Step error' in obs or 'Unknown error' in obs:
            error = obs
        return obs, reward, done, metadata, error

    def _run_sledgehammer(self, step, i, tls_name, env):
        # First try heuristics
        for heuristic in ['by auto', 'by simp', 'by blast', 'by fastforce', 'by force', 'by eval', 'by presburger', 'by sos', 'by arith', 'by linarith', 'by (auto simp: field_simps)']:
        # for heuristic in []:
            step_ = step.replace('sledgehammer', heuristic)
            obs, reward, done, metadata, error = self._run_step(step_, i, tls_name, env)
            if error is None:
                obs = '%s <hammer> %s' % (heuristic, obs)
                return obs, reward, done, metadata, error
        # Try sledgehammer
        return self._run_step(step, i, tls_name, env)

    def check(self, formal):
        # Initialize environment
        env = self._initialize()

        # Wrap and parse theorem
        theory = Checker.minif2f_wrap_theorem(formal)
        steps = Checker.get_parsed(env, theory)

        done = False
        reason = ''
        success = False
        step_results = []
        tls_name = 'default'
        for i, step in enumerate(steps):
            try:
                time0 = time.time()
                if 'sledgehammer' in step:
                    obs, reward, done, metadata, error = self._run_sledgehammer(step, i, tls_name, env)
                else:
                    obs, reward, done, metadata, error = self._run_step(step, i, tls_name, env)
                print("--------------------------")
                print("step: {}".format(step))
                print("obs: {}".format(obs))
                print("--------------------------")
                step_time = time.time() - time0
                step_results.append(dict(index=i, step=step, output=self._parse_output(obs), step_time=step_time))
                if error is not None:
                    reason = error
                    success = False
                    done = False
                    break
            except:
                # Timeout - end the proof attempt
                success = False
                done = False
                reason = 'timeout (%d)' % len(step_results)
                step_results.append(dict(index=i, step=step, output=''))
                break

            # Change when successful
            tls_name = 'default_%d' % i

        if done and reward == 1.0:
            success = True

        result = {
            'success': success,
            'reason': reason,
            'num_steps': len(steps),
            'last_step': len(step_results),
            'step_results': step_results
        }
        # Exit environment
        self._exit(env)
        return result

    @staticmethod
    def minif2f_wrap_theorem(theorem):
        return 'theory Interactive imports HOL.HOL Complex_Main "HOL-Library.Code_Target_Numeral" "HOL-Library.Sum_of_Squares" "Symmetric_Polynomials.Vieta" "HOL-Computational_Algebra.Computational_Algebra" "HOL-Number_Theory.Number_Theory" \n begin\n%s' % theorem

    @staticmethod
    def wrap_theorem(theorem):
        return 'theory Interactive imports Complex_Main \n "HOL-Computational_Algebra.Computational_Algebra" \n "HOL-Number_Theory.Number_Theory" \n begin\n%s' % theorem

    @staticmethod
    def get_parsed(env, theory, tls_name='default'):
        steps = env.post(f"<parse text> ${theory}")
        steps = steps.split('<SEP>')
        steps = [s for s in steps if s.strip() != '']
        # remove weird '$' step and whitespace steps
        steps = [s for s in steps if s != '$' and s.strip() != '']
        return steps


def is_successful(result_obj):
    if type(result_obj) == str:
        result_obj = json.load(open(result_obj))
    failed_steps = ["sorry", "oops"]
    eval_all_proof = "\n".join([eval_step["step"].strip() for eval_step in result_obj["result"]["step_results"]])
    return result_obj["result"]["success"] and all([failed_step not in eval_all_proof for failed_step in failed_steps]) and len(result_obj["result"]["step_results"]) > 2

def verify_a_proof(proof, residue=16):

    isa_path = "/import/snvm-sc-podscratch4/xueliangz/isabelle_server_resources/isabelle_copies"
    pisa_path = "/import/snvm-sc-podscratch4/xueliangz/isabelle_server_resources/pisa_jars"
    afp_path = "/import/snvm-sc-podscratch4/xueliangz/isabelle_server_resources/afp-2021-10-22"

    port = residue + 8000
    jar_path = os.path.join(pisa_path, "pisa_copy{}.jar".format(residue))
    true_isa_path = os.path.join(isa_path, "isabelle_copy_{}/main_isa/Isabelle2021".format(residue))

    minif2f_working_directory = os.path.join(afp_path, "thys", "Symmetric_Polynomials")
    minif2f_theory_filepath = os.path.join(minif2f_working_directory, "Interactive.thy")

    print("port: {}".format(port))
    # TODO: use more elegant ways to kill...
    os.system("ps aux | grep {}".format(port) + " | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")
    sub = subprocess.Popen(["java", "-cp", jar_path, "pisa.server.PisaOneStageServer{}".format(port)]).pid
    print("Server started with pid {}".format(sub))
    time.sleep(10)

    checker = Checker(
        working_dir=minif2f_working_directory,
        isa_path=true_isa_path,
        theory_file=minif2f_theory_filepath,
        port=port,
    )
    result = checker.check(proof)
    print(result)

    try:
        # fix Exception in thread "main"
        parent = psutil.Process(sub)
        children = parent.children(recursive=True)
        for process in children:
            process.kill()
        parent.kill()
    except psutil.NoSuchProcess:
        pass
    return result

def verify_a_proof_new(proof, working_directory, theory_filepath, residue=16):

    isa_path = "/home/xueliang/isabelle_server_resources/isabelle_copies"
    jar_path = "/home/xueliang/isabelle_server_resources/pisa_jars"
    # afp_path = "/home/xueliang/isabelle_server_resources/afp-2021-10-22"

    port = residue + 8000
    # port = residue + 8021
    jar_path = os.path.join(jar_path, "pisa_copy{}.jar".format(residue))
    true_isa_path = os.path.join(isa_path, "isabelle_copy_{}/main_isa/Isabelle2021".format(residue))
    # true_isa_path = "/home/xueliang/isabelle_server_resources/Isabelle2021"

    # minif2f_working_directory = os.path.join(afp_path, "thys", "Symmetric_Polynomials")
    # minif2f_theory_filepath = os.path.join(minif2f_working_directory, "Interactive.thy")

    print("port: {}".format(port))
    # TODO: use more elegant ways to kill...
    os.system("ps aux | grep {}".format(port) + " | awk '{print $2}' | xargs kill -9 > /dev/null 2>&1")
    sub = subprocess.Popen(["java", "-cp", jar_path, "pisa.server.PisaOneStageServer{}".format(port)]).pid
    print("Server started with pid {}".format(sub))
    time.sleep(10)

    checker = Checker(
        working_dir=working_directory,
        isa_path=true_isa_path,
        theory_file=theory_filepath,
        port=port,
    )
    result = checker.check(proof)
    # print(result)

    try:
        # fix Exception in thread "main"
        parent = psutil.Process(sub)
        children = parent.children(recursive=True)
        for process in children:
            process.kill()
        parent.kill()
    except psutil.NoSuchProcess:
        pass
    return result



def delete_comments(formal_proof):
    prompt_prefix_lines = [line for line in formal_proof.split("\n")]
    lines_to_delete = []
    to_delete = False
    for i, line in enumerate(prompt_prefix_lines):

        if line.strip().startswith("(*"):
            assert not to_delete
            to_delete = True

        if to_delete:
            lines_to_delete.append(i)

        if line.strip().endswith("*)"):
            assert to_delete
            to_delete = False
    assert (not to_delete) or ((len(prompt_prefix_lines) - 1) in lines_to_delete)
    prompt_prefix_lines = [line for i, line in enumerate(prompt_prefix_lines) if i not in lines_to_delete]
    formal_proof = "\n".join(prompt_prefix_lines)
    return formal_proof

def delete_empty_lines(formal_proof):
    lines = formal_proof.split("\n")
    return "\n".join([line for line in lines if line.strip() != ""])


def auto_fix(proof):
    old_lines = proof.strip().split("\n")
    lines = []
    for line in old_lines:
        if line.strip() == "proof":
            line = "proof -"
        if "(*" not in line and "*)" not in line and line.strip().startswith("(") and line.strip().endswith(")"):
            line = "(* {} *)".format(line.strip()[len("("):-len(")")].strip())
        if "(*" in line and "*)" not in line and line.strip().endswith(")"):
            line = "{} *)".format(line.strip()[:-len(")")].strip())
        if "(*" not in line and "*)" in line and line.strip().startswith("("):
            line = "(* {}".format(line.strip()[len("("):].strip())
        if "by simp" in line:
            line = line.replace("by simp", "sledgehammer")
        if "by auto" in line:
            line = line.replace("by auto", "sledgehammer")
        if "by blast" in line:
            line = line.replace("by blast", "sledgehammer")
        if "by fastforce" in line:
            line = line.replace("by fastforce", "sledgehammer")
        if "by force" in line:
            line = line.replace("by force", "sledgehammer")
        if "by eval" in line:
            line = line.replace("by eval", "sledgehammer")
        if "by presburger" in line:
            line = line.replace("by presburger", "sledgehammer")
        if "by sos" in line:
            line = line.replace("by sos", "sledgehammer")
        if "by arith" in line:
            line = line.replace("by arith", "sledgehammer")
        if "by linarith" in line:
            line = line.replace("by linarith", "sledgehammer")
        if "by (auto simp: field_simps)" in line:
            line = line.replace("by (auto simp: field_simps)", "sledgehammer")
        # if line.strip() == "by (simp add: sum_singleton)":
        #     premise = "sum_singleton"
        #     line = "using {} sledgehammer".format(premise)
        # if line.strip() == "by (simp add: atLeast0AtMost)":
        #     premise = "atLeast0AtMost"
        #     line = "using {} sledgehammer".format(premise)
        # if line.strip() == "by (simp add: sum.atLeast0_atMost_Suc)":
        #     premise = "sum.atLeast0_atMost_Suc"
        #     line = "using {} sledgehammer".format(premise)
        # if line.strip() == "by (simp add: atLeastAtMost_same)":
        #     premise = "atLeastAtMost_same"
        #     line = "using {} sledgehammer".format(premise)
        lines.append(line)
    return "\n".join(lines)

def remove_space_and_empty_lines(formal_proof):
    lines = formal_proof.split("\n")
    return "\n".join([line.strip() for line in lines if line.strip() != ""])


def isabelle_commands():
    return [
        "abbreviation",
        # "apply",
        # "back",
        # "by",
        "datatype",
        # "defer",
        "definition",
        # "done",
        # "end",
        "fun",
        "function",
        "imports",
        "inductive",
        "inductive_cases",
        "inductive_set",
        "lemma",
        "lemmas",
        "notation",
        # "oops",
        # "pr",
        # "prefer",
        "primrec",
        "record",
        "term",
        "theorem",
        "theory",
        "thm",
        "typ",
        "type_synonym",
        "typedecl",
        "typedef"
    ]

def extract_theories(file_path):
    theories = []
    with open(file_path, 'r') as file:
        lines = file.readlines()

    capture = False
    indent_pattern = None
    for line in lines:
        if line.strip().lower() == "theories":
            capture = True
            indent_pattern = '^' + re.match(r'\s*', line).group(0)
            continue

        if capture and indent_pattern and re.match(indent_pattern + r'\S', line) and not line.strip().lower().startswith('theory'):
            break

        if capture:
            theory = line.strip()
            if theory:
                theories.append(theory)

    return theories

def load_afp_data(data_path="/home/xueliang/Data/AFP", split="train", afp_path="/home/xueliang/isabelle_server_resources/afp-2021-10-22"):
    problem_names_split = json.load(open(f"{data_path}/problem_names_split.json", encoding='utf-8'))
    problem_names = problem_names_split[f"{split}"]
    pisa_path = f"{data_path}/{split}.jsonl"

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
            yield {
                "id": f"afp-{split}-{i}",
                "formal_statement": formal_statement,
                "formal_proof": formal_proof,
                "working_dir": working_dir,
                "theory_file": theory_file,
                "interactive_file": interactive_file,
            }

def set_cpu_affinity(cpus): # [0, 1, 2, 3]
    current_job = psutil.Process()
    current_job.cpu_affinity(cpus)
    return None

if __name__ == "__main__":
    pass


