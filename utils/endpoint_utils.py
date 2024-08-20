import json
import os
import re
import subprocess
import time
from datetime import datetime as dt
from pathlib import Path


def stop_job(job_id):
    snrdu_command = f"snrdu stop {job_id}"
    try:
    # Run the shell script with arguments
        result = subprocess.run(snrdu_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
    except subprocess.CalledProcessError as e:
        print(f"Error occurred while running the script: {e}")
    else:
        print(f"Job {job_id} stopped successfully.")

def monitor_files(file_paths, job_ids, interval=1):
    file_status = {}
    start_time = {}

    # Get initial status of the files

    output_files_created = False

    created = file_paths[:]

    print("Waiting for snrdu command to start running...")
    while len(created) > 0:
        next_batch = []
        for file_path in created:
            output_files_created = os.path.exists(file_path)
            if output_files_created:
                file_status[file_path] = None
                start_time[file_path] = os.stat(file_path).st_mtime
            else:
                next_batch.append(file_path)
        created = next_batch[:]
        time.sleep(interval)
    print("All snrdu commands are running")

    original_size = len(file_paths)
    completed_size = 0

    all_endpoints = {}

    while len(file_paths) > 0:
        next_batch = []
        next_job_ids = []
        for idx, file_path in enumerate(file_paths):
            current_mtime = os.stat(file_path).st_mtime
            if current_mtime != file_status[file_path]:
                try:
                    with open(file_path, 'r') as file:
                        content = file.read()
                    endpoint_address = extract_endpoint(content, method="v2")
                except:
                    endpoint_address = None
                if endpoint_address is None:
                    next_batch.append(file_path)
                    next_job_ids.append(job_ids[idx])
                else:
                    # all_endpoints.add(endpoint_address)
                    all_endpoints[endpoint_address] = job_ids[idx]
                    duration = calculate_boot_up(start_time[file_path], current_mtime)
                    completed_size += 1
                    print(f"Endpoint {completed_size}/{original_size} generated! Took {duration} to boot up.")
            else:
                test = subprocess.run(f"snrdu list {job_ids[idx]}", shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
                if 'RUNNING' not in test.stderr:
                    for job_id in job_ids:
                        stop_job(job_id)
                    raise RuntimeError(f"Endpoint {idx} FAILED during run. Please look at the log file under endpoint_log_cache to see what went wrong here")
                next_batch.append(file_path)
                next_job_ids.append(job_ids[idx])
            file_status[file_path] = current_mtime
        file_paths = next_batch[:]
        job_ids = next_job_ids[:]
        time.sleep(interval)

    return all_endpoints

def calculate_boot_up(start_time, end_time):
    datetime1 = dt.fromtimestamp(start_time)
    datetime2 = dt.fromtimestamp(end_time)
    duration = datetime2 - datetime1
    return duration

def extract_endpoint(content, method="v2"):
    if method == "v1":
        endpoint_address = None
        if 'Running on http://' in content:
            endpoint_address = content.split('Running on http://')[1].split('/')[0]
    elif method == "v2":
        if 'Running on http://' in content:
            endpoint_address = content.split('Running on http://')[-1].split('Press CTRL+C to quit')[0].strip()
    else:
        raise ValueError
    return endpoint_address

class EndpointManager:
    def __init__(self, model_name_or_path, pef, cache_dir, num_endpoints, virtual_env):
        self.model_name_or_path = model_name_or_path
        self.pef = pef
        self.cache_dir = cache_dir
        self.num_endpoints = num_endpoints
        self.virtual_env = virtual_env
        
        self.idc_config_string = '--timeout 24:00:00 --qos 5'
        self.runtime_config_string = ' PROG_LOAD=DDR PROG_UNLOAD=DDR ARG_LOAD=DDR SF_RNT_FSM_POLL_BUSY_WAIT=1 SF_RNT_DMA_POLL_BUSY_WAIT=1 SF_RNT_NUMA_BIND=2'
        
        self.all_endpoints = {} # address -> job_id
    
    def start_endpoints(self):
        script_path = Path(__file__).resolve()
        script_directory = script_path.parent

        manifest_app_path = script_directory.joinpath("rdu_manifest", "app.py")
        assert manifest_app_path.exists(), "Manifest app.py cannot be found"
        script_path = script_directory.joinpath("idc_scripts", "job_script_generic_endpoint.sh")
        assert script_path.exists(), "job_script_generic_endpoint.sh cannot be found under idc_scripts"

        try:
            software_path = Path(os.environ['SOFTWARE'])
        except:
            print("SOFTWARE environment variable is not set")
            raise

        cache_dir = Path(self.cache_dir)
        model_name_or_path = Path(self.model_name_or_path)
        pef = Path(self.pef)

        path_args = [software_path, manifest_app_path, pef, model_name_or_path, cache_dir]

        current_path = Path(os.getcwd())
        for idx, path in enumerate(path_args):
            new_path = path
            if not path.is_absolute():
                new_path = current_path.joinpath(path)
            assert new_path.exists(), f"{new_path} cannot be found"
            path_args[idx] = new_path

        args = path_args + [self.virtual_env]

        endpoint_log_path = script_directory.joinpath("endpoint_log_cache")
        if not os.path.isdir(endpoint_log_path):
            os.mkdir(endpoint_log_path)

        output_paths = []
        job_ids = []
        for i in range(self.num_endpoints):
            model = "_".join(self.model_name_or_path.split("/")[5:7])
            output_file = endpoint_log_path.joinpath(f'idc_endpoint_{model}_{i}_{int(time.time())}.log')
            script_launch = f"{script_path} {args[0]} {args[1]} {args[2]} {args[3]} {args[4]} {args[5]} {i} {self.runtime_config_string}"
            snrdu_command = f"snrdu run {self.idc_config_string}" + f" --pef {args[2]} -o {output_file}" + f" -- srun --mpi=pmi2 {script_launch}"
            print("snrdu_command: ")
            print(snrdu_command)
            try:
            # Run the shell script with argument
                result = subprocess.run(snrdu_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
                job_info = result.stderr.split("INFO")[1]
                pattern = r'\b(\d+)\b'
                match = re.search(pattern, job_info)
                job_id = match.group(1)
                job_ids.append(job_id)
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Error occurred while running the script: {e}")
            else:
                print(f"Endpoint {i} executed successfully.")
                output_paths.append(output_file)

        endpoints = monitor_files(output_paths, job_ids)
        self.all_endpoints = endpoints
        print(f"These are the generated endpoints for {self.model_name_or_path} using {self.pef}")
        print(endpoints)
        return endpoints
    
    def stop_endpoints(self):
        for endpoint_address in self.all_endpoints:
            job_id = self.all_endpoints[endpoint_address]
            stop_job(job_id=job_id)


class BatchedEndpointManager:
    def __init__(self, model_name_or_path, pef, cache_dir, num_endpoints, virtual_env):
        self.model_name_or_path = model_name_or_path
        self.pef = pef
        self.cache_dir = cache_dir
        self.num_endpoints = num_endpoints
        self.virtual_env = virtual_env
        
        # self.idc_config_string = '--timeout 24:00:00 --qos 5 --scandump'
        self.idc_config_string = '--timeout 24:00:00 --qos 6 --scandump'
        # self.runtime_config_string = ' PROG_LOAD=DDR PROG_UNLOAD=DDR ARG_LOAD=DDR SF_RNT_FSM_POLL_BUSY_WAIT=1 SF_RNT_DMA_POLL_BUSY_WAIT=1 SF_RNT_NUMA_BIND=2'
        self.node_list = ["sc3-s240", "sc3-s220", "sc3-s298", "sc3-s241", "sc3-s167"]

        self.all_endpoints = {} # address -> job_id
        self.check_availability(self.num_endpoints)
    
    def check_availability(self, n):
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            job_ids = json.loads(f.read().strip())
        assert len(job_ids) >= n

    def release_nodes(self, n):
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            job_ids = json.loads(f.read().strip())
        to_release = job_ids[:n]
        to_maintain = job_ids[n:]
        with open("rdu_jobs.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps(to_maintain) + "\n")
        for job_id in to_release:
            stop_job(job_id=job_id)
        print(f"{n} nodes have been released!")
        

    def start_endpoints(self):
        script_path = Path(__file__).resolve()
        script_directory = script_path.parent

        # manifest_app_path = script_directory.joinpath("rdu_manifest", "app.py")
        # assert manifest_app_path.exists(), "Manifest app.py cannot be found"

        # if "8b" in self.pef:
        if self.pef.split("/")[-1].strip() == "llama3_8b_pef":
            # if "Instruct" in self.model_name_or_path:
            if self.model_name_or_path.split("/")[-1].strip() == "Meta-Llama-3-8B-Instruct":
                script_path = script_directory.joinpath("idc_scripts", "8b_job_script_batch_inference.sh")
            else:
                script_path = script_directory.joinpath("idc_scripts", "8b_base_job_script_batch_inference.sh")
        # elif "70b" in self.pef:
        elif self.pef.split("/")[-1].strip() == "llama3_70B_pef":
            script_path = script_directory.joinpath("idc_scripts", "70b_job_script_batch_inference.sh")
        else:
            raise ValueError
        assert script_path.exists(), "job_script cannot be found under idc_scripts"

        # try:
        #     software_path = Path(os.environ['SOFTWARE'])
        # except:
        #     print("SOFTWARE environment variable is not set")
        #     raise

        # cache_dir = Path(self.cache_dir)
        # model_name_or_path = Path(self.model_name_or_path)
        # pef = Path(self.pef)
        if "8b" in self.pef:
            pef = os.path.join(self.pef, "bs8/coe_pef/Llama3_8B_ss8192_4096_voc128256_bs8_inference_m2_0613_main_CoE.pef")
        elif "70b" in self.pef:
            pef = os.path.join(self.pef, "BS8/coe_pef/llama3_70b_ss8192_4096_voc128256_bs8_balanced_inference_0514_CoE.pef")
        else:
            raise ValueError

        # path_args = [software_path, manifest_app_path, pef, model_name_or_path, cache_dir]

        # current_path = Path(os.getcwd())
        # for idx, path in enumerate(path_args):
        #     new_path = path
        #     if not path.is_absolute():
        #         new_path = current_path.joinpath(path)
        #     assert new_path.exists(), f"{new_path} cannot be found"
        #     path_args[idx] = new_path

        # args = path_args + [self.virtual_env]

        endpoint_log_path = script_directory.joinpath("endpoint_log_cache")
        if not os.path.isdir(endpoint_log_path):
            os.mkdir(endpoint_log_path)

        output_paths = []
        job_ids = []
        for i in range(self.num_endpoints):
            model = "_".join(self.model_name_or_path.split("/")[5:7])
            output_file = endpoint_log_path.joinpath(f'idc_endpoint_{model}_{i}_{int(time.time())}.log')
            # snrdu_command = f"snrdu run {self.idc_config_string}" + f" --pef {pef} -o {output_file} -j isabelle" + f" -- srun --mpi=pmi2 {script_path}"
            snrdu_command = f"snrdu run --nodelist {self.node_list[i]} {self.idc_config_string}" + f" --pef {pef} -o {output_file} -j isabelle" + f" -- srun --mpi=pmi2 {script_path}"
            try:
            # Run the shell script with argument
                result = subprocess.run(snrdu_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
                job_info = result.stderr.split("INFO")[1]
                pattern = r'\b(\d+)\b'
                match = re.search(pattern, job_info)
                job_id = match.group(1)
                job_ids.append(job_id)
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Error occurred while running the script: {e}")
            else:
                print(f"Endpoint {i} executed successfully.")
                output_paths.append(output_file)
        time.sleep(120)
        self.release_nodes(self.num_endpoints)
        

        endpoints = monitor_files(output_paths, job_ids)
        self.all_endpoints = endpoints
        print(f"These are the generated endpoints for {self.model_name_or_path} using {self.pef}")
        print(endpoints)
        return endpoints
    
    def stop_endpoints(self):
        to_add = []
        for endpoint_address in self.all_endpoints:
            job_id = self.all_endpoints[endpoint_address]
            # stop_job(job_id=job_id)
            to_add.append(job_id)
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            original_ids = json.loads(f.read().strip())
        job_ids = original_ids + to_add
        with open("rdu_jobs.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps(job_ids) + "\n")


class BatchedDynamicEndpointManager:
    def __init__(self, model_name_or_path, pef, cache_dir, num_endpoints, virtual_env):
        self.model_name_or_path = model_name_or_path
        self.pef = pef
        self.cache_dir = cache_dir
        self.num_endpoints = num_endpoints
        self.virtual_env = virtual_env
        
        # self.idc_config_string = '--timeout 24:00:00 --qos 5 --scandump'
        self.idc_config_string = '--timeout 24:00:00 --qos 6 --scandump'
        # self.runtime_config_string = ' PROG_LOAD=DDR PROG_UNLOAD=DDR ARG_LOAD=DDR SF_RNT_FSM_POLL_BUSY_WAIT=1 SF_RNT_DMA_POLL_BUSY_WAIT=1 SF_RNT_NUMA_BIND=2'
        self.node_list = ["sc3-s240", "sc3-s220", "sc3-s298", "sc3-s241", "sc3-s167"]
        

        self.all_endpoints = {} # address -> job_id
        self.check_availability(self.num_endpoints)
    
    def check_availability(self, n):
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            job_ids = json.loads(f.read().strip())
        # assert len(job_ids) >= n # TODO: uncomment

    def release_nodes(self, n):
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            job_ids = json.loads(f.read().strip())
        to_release = job_ids[:n]
        to_maintain = job_ids[n:]
        with open("rdu_jobs.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps(to_maintain) + "\n")
        for job_id in to_release:
            stop_job(job_id=job_id)
        print(f"{n} nodes have been released!")

    def start_endpoints(self):
        script_path = Path(__file__).resolve()
        script_directory = script_path.parent
        script_path = script_directory.joinpath("scripts", "8b_dynamic_job_script_batch_inference.sh")
        assert script_path.exists(), "job_script cannot be found under scripts"
        if "8b" in self.pef:
            pef = os.path.join(self.pef, "bs8/coe_pef/Llama3_8B_ss8192_4096_voc128256_bs8_inference_m2_0613_main_CoE.pef")
        elif "70b" in self.pef:
            pef = os.path.join(self.pef, "BS8/coe_pef/llama3_70b_ss8192_4096_voc128256_bs8_balanced_inference_0514_CoE.pef")
        else:
            raise ValueError
        endpoint_log_path = script_directory.joinpath("endpoint_log_cache")
        if not os.path.isdir(endpoint_log_path):
            os.mkdir(endpoint_log_path)

        output_paths = []
        job_ids = []
        for i in range(self.num_endpoints):
            model = "_".join(self.model_name_or_path.split("/")[5:7])
            output_file = endpoint_log_path.joinpath(f'idc_endpoint_{model}_{i}_{int(time.time())}.log')
            snrdu_command = f"snrdu run {self.idc_config_string}" + f" --pef {pef} -o {output_file} -j isabelle" + f" -- srun --mpi=pmi2 {script_path} {self.pef} {self.model_name_or_path}"
            # snrdu_command = f"snrdu run --nodelist {self.node_list[i]} {self.idc_config_string}" + f" --pef {pef} -o {output_file} -j isabelle" + f" -- srun --mpi=pmi2 {script_path} {self.pef} {self.model_name_or_path}" # TODO: recover
            try:
            # Run the shell script with argument
                result = subprocess.run(snrdu_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
                job_info = result.stderr.split("INFO")[1]
                pattern = r'\b(\d+)\b'
                match = re.search(pattern, job_info)
                job_id = match.group(1)
                job_ids.append(job_id)
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Error occurred while running the script: {e}")
            else:
                print(f"Endpoint {i} executed successfully.")
                output_paths.append(output_file)
        # time.sleep(120)
        time.sleep(300)
        self.release_nodes(self.num_endpoints)
        endpoints = monitor_files(output_paths, job_ids)
        self.all_endpoints = endpoints
        print(f"These are the generated endpoints for {self.model_name_or_path} using {self.pef}")
        print(endpoints)
        return endpoints
    
    def stop_endpoints(self):
        to_add = []
        for endpoint_address in self.all_endpoints:
            job_id = self.all_endpoints[endpoint_address]
            # stop_job(job_id=job_id)
            to_add.append(job_id)
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            original_ids = json.loads(f.read().strip())
        job_ids = original_ids + to_add
        with open("rdu_jobs.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps(job_ids) + "\n")


class BatchedDynamicSingleRduEndpointManager:
    def __init__(self, model_name_or_path, pef, cache_dir, node, virtual_env):
        self.model_name_or_path = model_name_or_path
        self.pef = pef
        self.cache_dir = cache_dir
        # self.num_endpoints = num_endpoints
        self.node = node
        self.virtual_env = virtual_env
        
        # self.idc_config_string = '--timeout 24:00:00 --qos 5 --scandump'
        self.idc_config_string = '--timeout 24:00:00 --qos 6 --scandump'
        # self.runtime_config_string = ' PROG_LOAD=DDR PROG_UNLOAD=DDR ARG_LOAD=DDR SF_RNT_FSM_POLL_BUSY_WAIT=1 SF_RNT_DMA_POLL_BUSY_WAIT=1 SF_RNT_NUMA_BIND=2'
        # self.node_list = ["sc3-s240", "sc3-s220", "sc3-s298", "sc3-s241", "sc3-s167"]
        

        self.all_endpoints = {} # address -> job_id
        # self.check_availability(self.num_endpoints)
    
    # def check_availability(self, n):
    #     with open("rdu_jobs.jsonl", encoding="utf-8") as f:
    #         job_ids = json.loads(f.read().strip())
    #     assert len(job_ids) >= n # TODO: uncomment

    def release_nodes(self):
        with open(f"rdu_jobs_{self.node}.jsonl", encoding="utf-8") as f:
            job_ids = json.loads(f.read().strip())
        with open(f"rdu_jobs_{self.node}.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps([]) + "\n")
        for job_id in job_ids:
            stop_job(job_id=job_id)
        print(f"node {self.node} has been released!")

    def start_endpoints(self):
        script_path = Path(__file__).resolve()
        script_directory = script_path.parent
        script_path = script_directory.joinpath("scripts", "8b_dynamic_job_script_batch_inference.sh")
        assert script_path.exists(), "job_script cannot be found under scripts"
        if self.pef.split("/")[-1].strip() == "llama3_8b_pef":
            pef = os.path.join(self.pef, "bs8/coe_pef/Llama3_8B_ss8192_4096_voc128256_bs8_inference_m2_0613_main_CoE.pef")
        elif self.pef.split("/")[-1].strip() == "llama3_70B_pef":
            pef = os.path.join(self.pef, "BS8/coe_pef/llama3_70b_ss8192_4096_voc128256_bs8_balanced_inference_0514_CoE.pef")
        else:
            raise ValueError
        endpoint_log_path = script_directory.joinpath("endpoint_log_cache")
        if not os.path.isdir(endpoint_log_path):
            os.mkdir(endpoint_log_path)

        output_paths = []
        job_ids = []
        for i in range(self.num_endpoints):
            model = "_".join(self.model_name_or_path.split("/")[5:7])
            output_file = endpoint_log_path.joinpath(f'idc_endpoint_{model}_{int(time.time())}.log')
            snrdu_command = f"snrdu run --nodelist {self.node} {self.idc_config_string}" + f" --pef {pef} -o {output_file} -j isabelle" + f" -- srun --mpi=pmi2 {script_path} {self.pef} {self.model_name_or_path}" # TODO: recover
            try:
            # Run the shell script with argument
                result = subprocess.run(snrdu_command, shell=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, check=True)
                job_info = result.stderr.split("INFO")[1]
                pattern = r'\b(\d+)\b'
                match = re.search(pattern, job_info)
                job_id = match.group(1)
                job_ids.append(job_id)
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Error occurred while running the script: {e}")
            else:
                print(f"Endpoint 0 executed successfully.")
                output_paths.append(output_file)
        time.sleep(120)
        self.release_nodes()
        endpoints = monitor_files(output_paths, job_ids)
        self.all_endpoints = endpoints
        print(f"These are the generated endpoints for {self.model_name_or_path} using {self.pef}")
        print(endpoints)
        return endpoints
    
    def stop_endpoints(self):
        to_add = []
        for endpoint_address in self.all_endpoints:
            job_id = self.all_endpoints[endpoint_address]
            # stop_job(job_id=job_id)
            to_add.append(job_id)
        with open("rdu_jobs.jsonl", encoding="utf-8") as f:
            original_ids = json.loads(f.read().strip())
        job_ids = original_ids + to_add
        with open("rdu_jobs.jsonl", "w", encoding="utf-8") as f:
            f.write(json.dumps(job_ids) + "\n")



if __name__ == "__main__":
    endpoint_manager = EndpointManager(
        # model_name_or_path="/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B-Instruct",
        model_name_or_path="/import/snvm-sc-podscratch4/xueliangz/checkpoints/Meta-Llama-3-8B",
        pef="/import/snvm-sc-podscratch4/xueliangz/pef/TB-PEF-7/BS1/coe_pef/ts__llama3_8b_ss8192_voc128256_bs1_3graph_m1_0606_variation_8.pef",
        cache_dir="/import/snvm-sc-podscratch4/xueliangz/cache",
        num_endpoints=1,
        virtual_env="/import/snvm-sc-podscratch4/xueliangz/software/sambaflow/apps/coe/projects/samba_modelbox/samba_venv/venv/",
    )


    all_endpoints = endpoint_manager.start_endpoints()
    if type(all_endpoints) == dict:
        all_endpoints = list(all_endpoints.items())
    print(all_endpoints)
