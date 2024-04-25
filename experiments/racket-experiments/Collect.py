import argparse
import json
import os

from benchtool.Tasks import tasks
from benchtool.Racket import Racket
from benchtool.Types import TrialConfig, ReplaceLevel


def collect(results: str):
    tool = Racket(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():

        for variant in tool.all_variants(workload):

            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):           

                for property in tool.all_properties(workload):
                    if property.split('_')[1] not in tasks[workload.name][variant.name]:
                        continue
                    property = 'test_' + property       
                    
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
                                      timeout=3,
                                      short_circuit=False)
                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path)
