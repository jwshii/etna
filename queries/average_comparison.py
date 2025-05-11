
import json
import os
import pathlib

# read parallel.json
parallel = json.load(open("parallel.json"))

# read single.json
single = json.load(open("single.json"))

# create a set of mutant-property pairs
mutant_properties = set()
# get all mutant-property pairs from parallel
for record in parallel:
    mutant_properties.add((record["workload"], record["mutant"], record["property"]))

# get all mutant-property pairs from single
for record in single:
    mutant_properties.add((record["workload"], record["mutant"], record["property"]))

comparisons = []
parallel_wins = 0
single_wins = 0
uncomparable = 0
for (workload, mutant, property) in mutant_properties:
    # get the record from parallel
    parallel_record = next(
        (record for record in parallel if record["workload"] == workload and record["mutant"] == mutant and record["property"] == property), None
    )
    # get the record from single
    single_record = next(
        (record for record in single if record["workload"] == workload and record["mutant"] == mutant and record["property"] == property), None
    )

    if parallel_record is None or single_record is None:
        raise ValueError(f"Missing record for workload {workload}, mutant {mutant} and property {property}")
    # compare the records

    if abs(single_record["time"] - parallel_record["time"]) <= 1:
        print(f"Comparing mutant {mutant} and property {property}")
        uncomparable += 1
    else:
        if parallel_record["time"] < single_record["time"]:
            parallel_wins += 1
        elif parallel_record["time"] > single_record["time"]:
            single_wins += 1
        print(f"Parallel: {parallel_record['time']}")
        print(f"Single: {single_record['time']}")
        comparisons.append(parallel_record["time"] / single_record["time"])
        print(f"Comparison: {parallel_record['time'] / single_record['time']}")

print(f"Parallel wins: {parallel_wins}")
print(f"Single wins: {single_wins}")
print(f"Uncomparable: {uncomparable}")
print(f"Comparisons: {comparisons}")
print(f"Average comparison: {sum(comparisons) / len(comparisons)}")