#!/bin/bash

# Check if the correct number of arguments is provided
if [ "$#" -ne 3 ]; then
    echo "Usage: $0 <input_file> <output_file> <port>"
    exit 1
fi

# Get the arguments
input_file=$1
output_file=$2
port=$3
basename=$(basename "$input_file")

# Enable job control
set -m

# Function to clean up all child processes
cleanup() {
    echo "Cleaning up..."
    # Kill all processes in the current process group
    pkill -TERM -P $$
    # Additionally, find and kill all descendant processes
    pgrep -P $$ | xargs -r kill -TERM
}

# Trap signals to ensure cleanup
trap cleanup EXIT SIGINT SIGTERM


# Function to create Java process first, then run Python process
run_java_then_python() {
    echo "Starting Java process..."
    
    # Create a unique log file for the Java process
    java_log_file="/import/snvm-sc-scratch2/xueliangz/SambaProver/java_logs/java_output_${basename}.log"
    echo "Log file path: $java_log_file"

    # Start the Java process and redirect its output to the log file
    java -cp "/import/snvm-sc-podscratch4/xueliangz/isabelle_server_resources/pisa_jars_4096/pisa_copy$((port-8000)).jar" pisa.server.PisaOneStageServer"$port" > "$java_log_file" 2>&1 &
    JAVA_PID=$!

    # Wait for the Java server to start
    echo "Waiting for Java server to start..."
    while ! grep -q "Server is running. Press Ctrl-C to stop." "$java_log_file"; do
        sleep 5
    done
    echo "Java server started."
    sleep 5

    echo "Running Python script..."
    python single_proof_checker2.py --input_file "$input_file" --output_file "$output_file" --port "$port" &
    PYTHON_PID=$!

    # Wait for the Python process to finish
    wait $PYTHON_PID
    echo "Python script finished."

    # Kill the Java process and its subprocesses if they are still running
    pkill -TERM -P $JAVA_PID
    echo "Java process and its subprocesses are killed."
}

# Case 2: Create Java process first, then run Python process
run_java_then_python

