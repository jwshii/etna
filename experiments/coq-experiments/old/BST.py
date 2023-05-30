import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel
import itertools

RESULTS = f'{os.getcwd()}/results/Coq/BST/'

tool = Coq(results=RESULTS, log_level=LogLevel.DEBUG, replace_level=ReplaceLevel.REPLACE)

bench = next(bench for bench in tool.all_benches() if bench.name == 'BinarySearchTree')
tool._preprocess(bench)

variants = tool.all_variants(bench)
variants.remove(next(variant for variant in variants if variant.name == 'base'))
properties = tool.all_properties(bench)
methods = list(method for method in tool.all_methods(bench) if method.name == 'TypeBasedFuzzer')

cfg = json.load(open(f'experiments/coq-experiments/BinarySearchTree_exp_cfg.json'))
tasks = cfg['tasks']
finished = set(os.listdir(RESULTS))
all_tasks = set(
    map(
        lambda vpm: f"BinarySearchTree,{vpm[2].name},{vpm[0].name},test_{vpm[1]}.json"
        if f"test_{vpm[1]}" in tasks[vpm[0].name] else None,
        itertools.product(variants, properties, methods)))
all_tasks.remove(None)
remaining_tasks = all_tasks - finished
remaining_variants = list(set(map(lambda e: e.split(".json")[0].split(",")[2], remaining_tasks)))

for variant in (variant for variant in tool.all_variants(bench)
                if ((variant.name in tasks.keys()) and (variant.name in remaining_variants))):
    run_trial = tool.apply_variant(bench, variant, no_base=True)
    for property in (property for property in tool.all_properties(bench)
                     if "test_" + property in tasks[variant.name]):
        print(f'Running {variant.name} {property}...')
        for method in (
                method for method in tool.all_methods(bench) if method.name == 'TypeBasedFuzzer'):
            cfg = TrialConfig(bench=bench,
                              method=method.name,
                              label=method.name,
                              property="test_" + property,
                              trials=10,
                              timeout=40)
            run_trial(cfg)
