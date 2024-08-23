#!/usr/bin/python3

import subprocess
import argparse
import csv
import time
import shutil
import os

def run_command(cmd):
    try:
        subprocess.run(cmd, shell=True, check=True)
    except Exception as e:
        print(e)

def main():
    parser = argparse.ArgumentParser(description='Run fuzzing commands and record results in a CSV file')
    parser.add_argument('time', type=str, help='Time')
    parser.add_argument('config', type=str, help='Path to the results dir')
    parser.add_argument('target', type=str, help='Target')
    parser.add_argument('queue_dir', type=str, help='Target')
    parser.add_argument('experiment', type=int)
    parser.add_argument('output_dir', type=str, help='Path to the results dir')
    args = parser.parse_args()

    fuzzers = ['libfuzzer']

    for checkpoint in range(0, 13):
        for fuzzer in fuzzers:
            seeds_dir = os.path.join(args.queue_dir, f"queue_{checkpoint}")
            shutil.rmtree(f"tests/{args.target}/corpus")
            shutil.copytree(seeds_dir, f"tests/{args.target}/corpus")
            print(f"Copy {seeds_dir}")
            target_name = f"{args.target}_{fuzzer}_queue_{checkpoint}_rep_{args.experiment}"
            obs_path = os.path.join("fuzz/observations", f"{target_name}_testcases.jsonl")
            results_dir = os.path.join(args.output_dir, f"hour_{checkpoint}")
            if not os.path.exists(results_dir):
                os.makedirs(results_dir)
            if os.path.exists(obs_path):
                os.remove(obs_path)
            cmd = f'DRT_OBSERVABILITY=true FUZZ_TARGET={target_name} cargo bolero test {args.target} -T {args.time} --corpus-dir tests/{args.target}/corpus 2> cov.log 1> valid.log'
            print(cmd)
            run_command(cmd)

            print(f"Copy {obs_path} to {results_dir}")
            shutil.copyfile(obs_path, os.path.join(results_dir, "obs.jsonl"))
            shutil.copyfile("cov.log", os.path.join(results_dir, "cov.log"))
            shutil.copyfile("valid.log", os.path.join(results_dir, "valid.log"))

if __name__ == "__main__":
    main()
