import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel

import itertools

RESULTS = f'{os.getcwd()}/results/Coq/IFC/'

tool = Coq(results=RESULTS, log_level=LogLevel.INFO, replace_level=ReplaceLevel.SKIP)
do_bench, do_plot = tool.parse_args()

bench = next(bench for bench in tool.all_benches() if bench.name == 'IFC')
tool._preprocess(bench)

variants = tool.all_variants(bench)
properties = ["test_propSSNI_smart"]
methods = (method for method in tool.all_methods(bench) if method.name == "VariationalFuzzer")

finished = set(os.listdir(RESULTS))
all_tasks = set(map(lambda vpm: f"IFC,{vpm[2].name},{vpm[0].name},{vpm[1]}.json", itertools.product(variants, properties, methods)))
remaining_tasks = all_tasks - finished
remaining_variants = list(set(map(lambda e: e.split(".json")[0].split(",")[2], remaining_tasks)))

bench = next(bench for bench in tool.all_benches() if bench.name == 'IFC')
tool._preprocess(bench)
variant = next((variant for variant in tool.all_variants(bench) if (variant.name in remaining_variants) and (variant.name != "base")))
run_trial = tool.apply_variant(bench, variant, no_base=True)
property = "propSSNI_smart"
method = next(method for method in tool.all_methods(bench) if method.name == "VariationalFuzzer")
cfg = TrialConfig(bench=bench,
                method=method.name,
                label=method.name,
                property="test_" + property,
                trials=10,
                timeout=60)
run_trial(cfg)

