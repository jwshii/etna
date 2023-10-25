import argparse
import os

from benchtool.OCaml import OCaml
from benchtool.Types import ReplaceLevel, TrialConfig
from benchtool.Tasks import tasks


def collect(results: str):
    tool = OCaml(results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['BST']:
            continue

        for variant in tool.all_variants(workload):
            if variant.name == 'base':
                continue

            run_trial = None
            for strategy in tool.all_strategies(workload):
                for property in tool.all_properties(workload):
                    if workload.name in ['BST']:
                        if property.split('_')[1] not in tasks[workload.name][variant.name]:
                            continue

                        trials = 10
                        timeout = 65

                        if not run_trial:
                            run_trial = tool.apply_variant(workload, variant)

                        cfg = TrialConfig(workload=workload,
                                          strategy=strategy.name,
                                          property=property,
                                          trials=trials,
                                          timeout=timeout,
                                          short_circuit=False)

                        run_trial(cfg)

DEFAULT_DIR = 'oc'

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()
    dir = args.data if args.data else DEFAULT_DIR
    results_path = f'{os.getcwd()}/{dir}'
    collect(results_path)