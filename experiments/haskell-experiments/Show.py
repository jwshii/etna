from benchtool.Haskell import Haskell
from benchtool.Types import TrialConfig
from benchtool.Analysis import *

results = 'results/'
tool = Haskell(results)

timeout = 60

for bench in tool.all_benches():
    if bench.name not in ['STLC', 'FSUB']:
        continue

    for variant in tool.all_variants(bench):
        run_trial = tool.apply_variant(bench, variant)

        for method in tool.all_methods(bench):
            if method.name not in ['Quick', 'Lean', 'Small']:
                continue

            for property in tool.all_properties(bench):
                cfg = TrialConfig(bench=bench,
                                  method=method.name,
                                  property=property,
                                  trials=10,
                                  timeout=timeout + 5)
                run_trial(cfg)

df = parse_results(results)
print(overall_solved(df, 'all', within=timeout))