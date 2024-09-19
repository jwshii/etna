import argparse
import os
import re

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, TrialConfig, Entry
from benchtool.Tasks import tasks


def collect(results: str):
    tool = Haskell(results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['LuParser']:
            continue

        with open(os.path.join(workload.path, 'app/Main.hs'), 'r+') as f:
            for variant in tool.all_variants(workload):
                if variant.name == 'base':
                    # Don't run on base (non-buggy) implementation.
                    continue

                for strategy in tool.all_strategies(workload):
                    if strategy.name not in ['Random', 'Hybrid', "Correct"]:
                        continue

                    run_trial = None

                    # Don't run on non-buggy tasks
                    for property in tool.all_properties(workload):
                        if property.split('_')[2] not in tasks[workload.name][variant.name]:
                            continue

                        # Don't compile tasks that are already completed.
                        finished = set(os.listdir(results))
                        file = f'{workload.name},{strategy.name},{variant.name},{property}'
                        if f'{file}.json' in finished:
                            continue

                        if not run_trial:
                            run_trial = tool.apply_variant(workload, variant)

                        cfg = TrialConfig(workload=workload,
                                          strategy=strategy.name,
                                          property=property,
                                          trials=10,
                                          timeout=5,
                                          short_circuit=True)

                        run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path)
