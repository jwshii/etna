import os
import subprocess
import pathlib
import json
def get_size_of(term: str):
    # sanitize the term
    # if starts with `#hash(` and ends with `)`, remove them
    if term.startswith("#hash(") and term.endswith(")"):
        term = term[6:-1]
    
    if term.startswith("(hash 'e ") and term.endswith(")"):
        term = term[9:-1]
    # Turn all `#(` into `(`
    term = term.replace("#(", "(")

    # If starts with `(e . ` and ends with `)`, remove them
    if term.startswith("(e . ") and term.endswith(")"):
        term = term[5:-1]

    if term.startswith("e: (") and term.endswith(")"):
        term = term[4:-1]
    # Turn all `struct:` into ``
    term = term.replace("struct:", "")

    if term.startswith("(just ") and term.endswith(")"):
        term = term[6:-1]


    racket_file = """
    #lang racket
    (require "Impl.rkt")

    (define/contract (size term)
    (term? . -> . number?)
    (match term
        [(Abs _ t) (+ 1 (size t))]
        [(App t1 t2) (+ 1 (size t1) (size t2))]
        [(TAbs _ t) (+ 1 (size t))]
        [(TApp t _) (+ 1 (size t))]
        [_ 1]
        )
    )

    (define term <term>)
    (displayln (size term))
    """

    with open("/Users/akeles/Programming/projects/PbtBenchmark/etna/workloads/Racket/SYSTEMF/src/tmp.rkt", "w") as f:
        f.write(racket_file.replace("<term>", term))

    # Run the racket file
    output = subprocess.check_output(["racket", "/Users/akeles/Programming/projects/PbtBenchmark/etna/workloads/Racket/SYSTEMF/src/tmp.rkt"])
    size = output.decode("utf-8")

    # Clean up
    os.remove("/Users/akeles/Programming/projects/PbtBenchmark/etna/workloads/Racket/SYSTEMF/src/tmp.rkt")

    return size

results_path = pathlib.Path(__file__).resolve().parent / "results"
for file in filter(lambda f: f.startswith("SYSTEMF"), os.listdir(results_path)):
    print("Working on ", file)
    jsonfile = results_path / file
    contents = json.load(open(jsonfile))
    for i, item in enumerate(contents):
        if item.get("size") is None:
            term = item["counterexample"]
            size = get_size_of(term)
        else:
            size = item["size"]

        print("\tWorking on ", i, item)
        
        if item["shrinked-counterexample"] == "-" or item["shrinked-counterexample"] == "#f":
            shrinked_size = -1
        else:
            if item.get("shrinked-size") is None:
                shrinked_size = get_size_of(item["shrinked-counterexample"])
            else:
                shrinked_size = item["shrinked-size"]
            # shrinked_size = item.get("shrinked-size", get_size_of(item["shrinked-counterexample"]))
        
        item["size"] = int(str(size).strip())
        item["shrinked-size"] = int(str(shrinked_size).strip())
    json.dump(contents, open(jsonfile, "w"))


shrinkages = {}

for file in filter(lambda f: f.startswith("SYSTEMF"), os.listdir(results_path)):
    jsonfile = results_path / file
    contents = json.load(open(jsonfile))
    total = 0
    [_, strategy, mutant, property] = file.split(",")

    if shrinkages.get((mutant, property)) is None:
        shrinkages[((mutant, property))] = {
            "ProplangBespoke": {
                "Shrinkage": -1,
                "Size": -1,
                "ShrinkedSize": -1
            },
            "RackcheckBespoke": {
                "Shrinkage": -1,
                "Size": -1,
                "ShrinkedSize": -1
            },
        }
    
    average_size = 0
    average_shrinked_size = 0
    for i, item in enumerate(contents):
        size = item["size"]
        shrinked_size = item["shrinked-size"]
        shrinkage = size / shrinked_size
        if shrinkage < 0:
            continue
        
        total += shrinkage
        average_size += size
        average_shrinked_size += shrinked_size
    
    total /= len(contents)
    average_size /= len(contents)
    average_shrinked_size /= len(contents)

    shrinkages[(mutant, property)][strategy] = {
        "Shrinkage": total,
        "Size": average_size,
        "ShrinkedSize": average_shrinked_size
    }
    print(shrinkages[(mutant, property)])
    shrinkages[(mutant, property)]["Proplang/Rackcheck"] = shrinkages[(mutant, property)]["ProplangBespoke"]["Shrinkage"] / shrinkages[(mutant, property)]["RackcheckBespoke"]["Shrinkage"]
    shrinkages[(mutant, property)]["Proplang/Rackcheck Size"] = shrinkages[(mutant, property)]["ProplangBespoke"]["Size"] / shrinkages[(mutant, property)]["RackcheckBespoke"]["Size"]
    # print(f"Average shrinkage for {file} is {total}")

average_win_shrinkage = 0
average_win_size = 0
average_proplang_shrinkage = 0
average_rackcheck_shrinkage = 0
for key, value in shrinkages.items():
    print(f"Mutant: {key[0]}, Property: {key[1]}")
    print(f"\tProplangBespoke: {value['ProplangBespoke']}")
    print(f"\tRackcheckBespoke: {value['RackcheckBespoke']}")
    print(f"\tProplang/Rackcheck: {value['Proplang/Rackcheck']}")
    print(f"\tProplang/Rackcheck Size: {value['Proplang/Rackcheck Size']}\n")
    average_proplang_shrinkage += value['ProplangBespoke']['Shrinkage']
    average_rackcheck_shrinkage += value['RackcheckBespoke']['Shrinkage']
    average_win_shrinkage += value['Proplang/Rackcheck']
    average_win_size += value['Proplang/Rackcheck Size']


average_win_shrinkage /= len(shrinkages)
average_win_size /= len(shrinkages)
average_proplang_shrinkage /= len(shrinkages)
average_rackcheck_shrinkage /= len(shrinkages)

print(f"Average win ratio for Proplang Shrinkage is {average_win_shrinkage}")
print(f"Average win ratio for Proplang Size is {average_win_size}")
print(f"Average Proplang Shrinkage is {average_proplang_shrinkage}")
print(f"Average Rackcheck Shrinkage is {average_rackcheck_shrinkage}")


