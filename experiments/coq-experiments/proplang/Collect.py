import argparse
import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel
from benchtool.Tasks import tasks

def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

    for workload in tool.all_workloads():
        if not workload.name.endswith('Proplang'):
            continue

        tool._preprocess(workload)

        for variant in tool.all_variants(workload):

            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):
                if not strategy.name.endswith('Fuzzer'):
                    continue

                for property in tool.all_properties(workload):
                    if workload.name.startswith('STLC'):
                        property = 'test_' + property + '_runner'
                        pass
                    elif workload.name.endswith('Proplang'):
                        property = 'test_' + property + '_runner'
                        if property[10:-7] not in tasks[workload.name[:3]][variant.name]:
                            print(f'Skipping {workload.name},{strategy.name},{variant.name},{property}')
                            continue
                    elif workload.name == 'BST':
                        property = 'test_' + property
                        if property[10:] not in tasks["BST"][variant.name]:
                            print(f'Skipping {workload.name},{strategy.name},{variant.name},{property}')
                            continue
                    
                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    file = f'{workload.name},{strategy.name},{variable.current},{variant.name},{property}'
                    if f'{file}.json' in finished:
                        continue

                    if not run_trial:
                        run_trial = tool.apply_variant(workload, variant, no_base=True)

                    cfg = TrialConfig(workload=workload,
                                        strategy=strategy.name,
                                        property=property,
                                        file=file,
                                        trials=10,
                                        timeout=60,
                                        short_circuit=True)
                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    if not args.data:
        raise ValueError('No data path provided')

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path)
