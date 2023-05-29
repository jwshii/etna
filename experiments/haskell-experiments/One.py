import os

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, LogLevel, TrialConfig
from benchtool.Analysis import *

RESULTS = f'{os.getcwd()}/results'

tool = Haskell(RESULTS, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

for workload in tool.all_workloads():
    if workload.name != 'BST':
        continue

    for variant in tool.all_variants(workload):
        if variant.name != 'insert_1':
            continue

        run_trial = tool.apply_variant(workload, variant)

        for strategy in tool.all_strategies(workload):
            if strategy.name != 'Correct':
                continue

            for property in tool.all_properties(workload):
                if property != 'prop_InsertPost':
                    continue

                cfg = TrialConfig(workload=workload,
                                  strategy=strategy.name,
                                  property=property,
                                  trials=1,
                                  timeout=10)
                run_trial(cfg)

df = parse_results(RESULTS)
fig = px.bar(df, x='task', y='time')
fig.show()