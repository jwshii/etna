import os

from benchtool.Coq import Coq
from benchtool.Plot import all_results, create_df, generate_dashboard
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel

import itertools

RESULTS = f'{os.getcwd()}/results/Coq/IFC/'

tool = Coq(results=RESULTS, log_level=LogLevel.DEBUG, replace_level=ReplaceLevel.SKIP)

bench = next(bench for bench in tool.all_benches() if bench.name == 'IFC')
tool._preprocess(bench)

variants = tool.all_variants(bench)
properties = ["test_propSSNI_smart"]
methods = (method for method in tool.all_methods(bench) if method.name == "VariationalFuzzer")


finished = set(os.listdir(RESULTS))
all_tasks = set(map(lambda vpm: f"IFC,{vpm[2].name},{vpm[0].name},{vpm[1]}.json", itertools.product(variants, properties, methods)))
remaining_tasks = all_tasks - finished
remaining_variants = list(set(map(lambda e: e.split(".json")[0].split(",")[2], remaining_tasks)))

print(f"Remaining tasks: {len(remaining_tasks)}")

os.system(""" jq '.[] | select(.time == -1) | "results/Coq/IFC/IFC," + .method + "," + .mutant + "," + .property + ".json" ' results/Coq/IFC/* | uniq""")

