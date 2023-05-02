import os

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, LogLevel, TrialConfig
from benchtool.Analysis import *

RESULTS = f'{os.getcwd()}/results'

tool = Haskell(RESULTS, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

for bench in tool.all_benches():
    if bench.name != 'BST':
        continue

    for variant in tool.all_variants(bench):
        if variant.name != 'insert_1':
            continue

        run_trial = tool.apply_variant(bench, variant)

        for method in tool.all_methods(bench):
            if method.name != 'Correct':
                continue

            for property in tool.all_properties(bench):
                if property != 'prop_InsertPost':
                    continue

                cfg = TrialConfig(bench=bench,
                                  method=method.name,
                                  property=property,
                                  trials=1,
                                  timeout=10)
                run_trial(cfg)

df = parse_results(RESULTS)
fig = px.bar(df, x='task', y='time')
fig.show()