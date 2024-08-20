import argparse
import os
import shutil
import subprocess
import time
from datetime import datetime, timedelta
from pathlib import Path

import timeout_decorator

# Global variable to track port usage
port_usage = {}
port_job_dict = {}
# file_start_times = {}

def parse_arguments():
    parser = argparse.ArgumentParser(description="Schedule proof checker tasks.")
    parser.add_argument("--input_dir", type=str, default="/import/snvm-sc-scratch2/xueliangz/SambaProver/auto_debug", help="Directory containing input files")
    parser.add_argument("--output_dir", type=str, default="/import/snvm-sc-scratch2/xueliangz/SambaProver/eval_debug", help="Directory containing output files")
    parser.add_argument("--script_path", type=str, default="/import/snvm-sc-scratch2/xueliangz/SambaProver/single_proof_checker.sh", help="Path to the single proof checker script")
    parser.add_argument("--port_base", type=int, default=8000, help="Base port number")
    parser.add_argument("--port_count", type=int, default=32, help="Number of ports to use")
    return parser.parse_args()

def clear_logs(log_dir):
    if os.path.exists(log_dir):
        shutil.rmtree(log_dir)
    os.makedirs(log_dir)

def get_last_update_time(file_path):
    # Get the last modification time of the file
    last_update_time = file_path.stat().st_mtime

    # Convert to datetime object
    last_update_datetime = datetime.fromtimestamp(last_update_time)

    return last_update_datetime

def find_available_port(port_base, output_dir):

    # global port_usage, file_start_times
    global port_usage, port_job_dict
    now = datetime.now()

    for port, file in port_usage.items():
        if file is None:
            return port
    
    output_dir = Path(output_dir)
    log_dir = output_dir.with_name(output_dir.name + ".log")
    # Update port usage based on file completion or timeout
    for port, file in list(port_usage.items()):
        if file is not None:
            output_file = output_dir / file
            log_file = log_dir / file

            if output_file.exists() or (log_file.exists() and now - get_last_update_time(log_file) > timedelta(minutes=20)):
                port_usage[port] = None
                port_job_dict[port] = None
                continue
                # file_start_times[port] = None
            
            # sntask_file = Path(f"/import/snvm-sc-scratch2/xueliangz/SambaProver/sntask_logs/port_{port}.log")
            # if sntask_file.exists():
            #     with open(sntask_file, encoding="utf-8") as f:
            #         content = f.read().strip()
            #     if "grpc_status:13, grpc_message:" in content or "grpc_status:14, grpc_message:" in content:
            #         if "Terminated" in content:
            #             port_usage[port] = None
            #             os.remove(sntask_file)  # Attempt to delete the file
            #             print(f"gRPC error occurred, and the log file {sntask_file} has been deleted.")
            
            sntask_file = Path(f"/import/snvm-sc-scratch2/xueliangz/SambaProver/sntask_logs/port_{port}.log")
            if sntask_file.exists():
                with open(sntask_file, encoding="utf-8") as f:
                    content = f.read().strip()
                
                if any(status in content for status in ("grpc_status:13", "grpc_status:14")) and "Terminated" in content and "Java process and its subprocesses are killed." in content:
                    if now - get_last_update_time(sntask_file) > timedelta(minutes=1):
                        port_usage[port] = None
                        job_to_stop = port_job_dict[port]
                        port_job_dict[port] = None
                        # subprocess.run(f"sntask stop {job_to_stop}", shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True) # TODO: recover
                        try:
                            sntask_file.unlink()  # Attempt to delete the file
                            print(f"gRPC error occurred, and the log file {sntask_file} has been deleted.")
                        except OSError as e:
                            print(f"Error deleting the log file {sntask_file}: {e}")



    # Find an available port
    for port, file in port_usage.items():
        if file is None:
            return port
    return -1

def run_proof_checker(input_file, output_file, port, script_path):
    cmd = [
        "sntask", "run",
        "-j", f"{port}",
        "--qos", "1",
        # "--qos", "2",
        "--inherit-env",
        "--timeout", "00:10:00",
        # "--cpus-per-task", "1",
        # "--cpus-per-task", "2", # if using java_then_python
        "--cpus-per-task", "4", # if the idc is very busy
        "-o", f"sntask_logs/port_{port}.log",
        "--host-mem", "8G",
        "-c", f"{script_path} {input_file} {output_file} {port}"
    ]
    
    # result = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True) # TODO: recover
    # job_info = result.stderr.split("INFO")[1] # TODO: recover
    # job_id = job_info.split("Submitted batch job ")[1].strip() # TODO: recover
    # return job_id # TODO: recover

    result = subprocess.Popen(cmd) # TODO: del
    return "88888888" # TODO: del
    

def clear_or_create_directory(dir_path):
    # dir_path = Path(dir_path)

    if dir_path.exists():
        # Directory exists, clear its contents
        for file in dir_path.glob("*"):
            if file.is_file():
                file.unlink()
        print(f"Cleared existing directory: {dir_path}")
    else:
        # Directory does not exist, create it
        dir_path.mkdir(parents=True, exist_ok=True)
        print(f"Created new directory: {dir_path}")


@timeout_decorator.timeout(3600 * 24) # todo: adjust the time during weekends
def main():
    # global port_usage, file_start_times
    global port_usage, port_job_dict
    args = parse_arguments()

    input_dir = args.input_dir
    output_dir = args.output_dir
    script_path = args.script_path
    port_base = args.port_base
    port_count = args.port_count

    log_dir = Path(output_dir).with_name(Path(output_dir).name + ".log")
    clear_or_create_directory(log_dir)

    os.makedirs(output_dir, exist_ok=True)

    port_usage = {port_base + i: None for i in range(port_count)}
    port_job_dict = {port_base + i: None for i in range(port_count)}
    # file_start_times = {port_base + i: None for i in range(port_count)}

    unfinished_files = []

    # List all input files
    input_files = sorted(Path(input_dir).glob('*'))
    output_files = sorted(Path(output_dir).glob('*'))

    # Find the unfinished files
    output_files_set = set(f.name for f in output_files)
    for input_file in input_files:
        if input_file.name not in output_files_set:
            to_eval = True
            if to_eval:
                unfinished_files.append(input_file)

    # Print the number of unfinished files
    print(f"Number of unfinished files: {len(unfinished_files)}")

    for input_file in unfinished_files:
        output_file = Path(output_dir) / input_file.name

        # Wait for an available port with exponential backoff
        while True:
            port = find_available_port(port_base, output_dir)
            if port != -1:
                # print(f"Assigned port: {port}")
                port_usage[port] = input_file.name
                # file_start_times[port] = datetime.now()
                break
            time.sleep(1)

        # Run the proof checker script
        sntask_job_id = run_proof_checker(input_file, output_file, port, script_path)
        port_job_dict[port] = sntask_job_id
        print(f"Number of ports in use: {sum(1 for port, service in port_usage.items() if service is not None)}; {sum(1 for port, service in port_job_dict.items() if service is not None)}")
        # time.sleep(0.1)

    print("All jobs submitted.")

if __name__ == "__main__":
    try:
        main()
    except timeout_decorator.timeout_decorator.TimeoutError:
        print("Program execution exceeded the time limit")
