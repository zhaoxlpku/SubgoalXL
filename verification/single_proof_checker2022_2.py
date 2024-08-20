import json
import os
import signal
import sys

import psutil
import timeout_decorator

from utils.pisa_utils import Checker

# if os.environ.get('https_proxy'):
#     del os.environ['https_proxy']
# if os.environ.get('http_proxy'):
#     del os.environ['http_proxy']

subprocess_list = []

def clean_up_subprocesses():
    def terminate_process_tree(pid):
        try:
            parent = psutil.Process(pid)
            children = parent.children(recursive=True)
            for child in children:
                # print(f"Terminating subprocess with PID: {child.pid}")
                child.terminate()
            for child in children:
                child.wait()
                # print(f"Subprocess with PID: {child.pid} has been terminated.")
            parent.terminate()
            parent.wait()
            # print(f"Subprocess with PID: {parent.pid} has been terminated.")
        except psutil.NoSuchProcess:
            pass

    for process in subprocess_list:
        terminate_process_tree(process.pid)

def signal_handler(signal, frame):
    # print("Ctrl-C pressed. Cleaning up subprocesses...")
    clean_up_subprocesses()
    sys.exit(0)

def get_log_path(output_file):
    new_parent_dir = os.path.dirname(output_file) + ".log"
    base_filename = os.path.basename(output_file)
    new_file_path = os.path.join(new_parent_dir, base_filename)
    return new_file_path

def save_log(output_file):
    log_file = get_log_path(output_file)
    with open(log_file, "w", encoding="utf-8") as f:
        f.write(json.dumps({"submitted": True}) + "\n")


def delete_log(output_file):
    log_file = get_log_path(output_file)
    try:
        os.remove(log_file)  # Attempt to delete the file
        print(f"Deleted file: {log_file}")
    except OSError as e:
        print(f"Error deleting file {log_file}: {e}")
    
@timeout_decorator.timeout(300) 
def process_file(input_file, output_file, port):
    residue = port - 8000
    
    isa_path = "/import/ml-sc-scratch2/xueliangz/isabelle_resources_2022/isabelle_copies"
    pisa_path = "/import/ml-sc-scratch2/xueliangz/isabelle_resources_2022/pisa_jars_4096"

    jar_path = os.path.join(pisa_path, f"pisa_copy{residue}.jar")
    true_isa_path = os.path.join(isa_path, f"isabelle_copy_{residue % 128}/main_isa/Isabelle2022")
    minif2f_working_directory = f"{true_isa_path}/src/HOL/Examples"
    minif2f_theory_filepath = f"{minif2f_working_directory}/Interactive.thy"
    

    # server_process = subprocess.Popen(["java", "-cp", jar_path, f"pisa.server.PisaOneStageServer{port}"], preexec_fn=os.setpgrp)
    # server_process = subprocess.Popen(
    #     ["java", "-cp", jar_path, f"pisa.server.PisaOneStageServer{port}"],
    #     stdout=subprocess.PIPE,
    #     stderr=subprocess.PIPE,
    #     preexec_fn=os.setpgrp,
    #     universal_newlines=True  # To handle the output as text
    # )

    # Wait until the server is running
    # while True:
    #     output = server_process.stdout.readline()
    #     if "Server is running. Press Ctrl-C to stop." in output:
    #         print("Server is up and running.")
    #         break
    #     time.sleep(1)
        
    # subprocess_list.append(server_process)
    # time.sleep(10)

    with open(input_file, "r", encoding="utf-8") as f:
        data = json.loads(f.read().strip())
    
    formal_statement = "\n".join(data["formal_statement"].split("\n"))
    formal_proof = "\n".join(data["formal_proof"].split("\n"))
    formal_proof = formal_proof.replace("\\\\<or>", "\\<or>")

    checker = Checker(
        working_dir=minif2f_working_directory,
        isa_path=true_isa_path,
        theory_file=minif2f_theory_filepath,
        port=port,
    )
    result = checker.check("\n".join([formal_statement, formal_proof]))
    with open(output_file, "w", encoding="utf-8") as f:
        f.write(json.dumps(result) + "\n")

def main(input_file, output_file, port=8000):
    signal.signal(signal.SIGINT, signal_handler)
    signal.signal(signal.SIGTERM, signal_handler)
    if not os.path.exists(output_file): # unfinished
        try:
            save_log(output_file)
            process_file(input_file, output_file, port)
            delete_log(output_file)
        except timeout_decorator.timeout_decorator.TimeoutError:
            clean_up_subprocesses()
        except KeyboardInterrupt:
            clean_up_subprocesses()

if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Run checker on JSONL files.")
    parser.add_argument("--input_file", type=str, help="Directory containing JSONL files with formal statements and formal proofs.")
    parser.add_argument("--output_file", type=str, help="Directory to save the checking results.")
    parser.add_argument("--port", type=int, default=8127, help="Base port number for subprocesses.")

    args = parser.parse_args()

    try:
        main(args.input_file, args.output_file, args.port)
    finally:
        clean_up_subprocesses()