import argparse
import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel


def collect(results: str, optimize: bool = True):
    if optimize == False:
        print('The full experiment and the scaled-down experiment are the same for this one.')

    tool = Coq(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['BST', 'RBT', 'STLC']:
            continue

        tool._preprocess(workload)

        tasks_json = json.load(open(f'experiments/coq-experiments/5.2/{workload.name}_tasks.json'))

        for variant in tool.all_variants(workload):

            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):
                if strategy.name not in [
                    'TypeBasedFuzzer',    
                ]:
                    continue

                for property in tool.all_properties(workload):
                    property = 'test_' + property
                    if tasks_json['tasks'] and property not in tasks_json['tasks'][variant.name]:
                        print("SKIPPING", variant.name, property)
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
                                      timeout=60)
                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--full',
                   help='flag to disable faster version of experiment',
                   action='store_false')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path, args.full)
