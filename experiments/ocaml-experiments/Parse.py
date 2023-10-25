import re
import os
import json

DATA_PATH = './oc/'
OUTPUT_FILE = './experiments/ocaml-experiments/parsed.json'

def parse(filename):
    # Sample input data
    workload, strategy, mutant, prop = os.path.splitext(os.path.basename(filename))[0].split(',')

    file = ""
    with open(f"{filename}") as f:
        file = "".join(f.readlines())

    pattern_chunk = r'(?s)\[(\w+)\|(.*?)\|\1 -> ([.0-9]+)\]'
    matches = re.findall(pattern_chunk, file)
    data = []

    for _prop, body, ms in matches:
        assert _prop == prop, f"Test file {prop} contains data from {_prop}"

        pattern = r'\[(✗|✓)\]\s+(\d+)\s+(\d+)\s+(\d+)\s+(\d+)\s+/\s+(\d+).*?s\s+(\w+)'
        matches = re.findall(pattern, body)
        assert len(matches) == 1, f"Parse error in {filename}, found incorrect number of runs"

        _success, generated, error, fail, passed, total, testname = matches[0]
        assert testname[5:] == prop, f"Parse error in {filename}, found run of {testname}"

        success = _success == '✓'
        passed = int(passed)
        ms = float(ms)
        discards = int(generated) - (int(fail) + int(passed))

        run = {
            "workload": workload,
            "discards": discards,
            "foundbug": not success,
            "strategy": strategy,
            "mutant": mutant,
            "passed": passed,
            "property": prop,
            "time": ms,
        }
        data.append(run)

    return data

def main():
    filenames = os.listdir(DATA_PATH)
    filenames = list(map(lambda s: DATA_PATH + s, filenames))
    parsed = [run for filename in filenames for run in parse(filename)]
    with open(OUTPUT_FILE, 'w') as f:
        json.dump(parsed, f, indent=4)
    print(f"Successfully parsed through {DATA_PATH} directory")

if __name__ == '__main__':
    main()