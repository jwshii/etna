import argparse
import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel
from benchtool.Tasks import tasks

def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['BST', 'RBT', 'STLC']:
            continue

        tool._preprocess(workload)

        for variant in tool.all_variants(workload):
            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):
                if strategy.name != 'TypeBasedFuzzer':
                    continue

                for property in tool.all_properties(workload):
                    property = 'test_' + property
                    if workload.name != 'STLC':
                        if property[10:] not in tasks[workload.name][variant.name]:
                            print(f'Skipping {workload.name},{strategy.name},{variant.name},{property}')
                            continue

                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    file = f'{workload.name},{strategy.name},{variant.name},{property}'
                    if f'{file}.json' in finished:
                        continue

                    if not run_trial:
                        run_trial = tool.apply_variant(workload, variant, no_base=True)

                    cfg = TrialConfig(workload=workload,
                                      strategy=strategy.name,
                                      property=property,
                                      trials=10,
                                      timeout=60,
                                      short_circuit=True)
                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path)
