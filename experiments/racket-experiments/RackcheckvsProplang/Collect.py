import os
import pathlib

from benchtool.Tasks import tasks
from benchtool.Racket import Racket
from benchtool.Types import TrialConfig, ReplaceLevel


def collect(results: str):
    tool = Racket(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        print(f'Collecting {workload.name}...')
        if workload.name in ['BST', 'RBT', 'STLC']:
            for variant in tool.all_variants(workload):
                print(f'Collecting {workload.name} {variant.name}...')
                if variant.name == 'base':
                    continue

                run_trial = None

                for strategy in tool.all_strategies(workload):           
                    print(f'Collecting {workload.name} {variant.name} {strategy.name}...')
                    for property in tool.all_properties(workload):
                        print(f'Collecting {workload.name} {variant.name} {strategy.name} {property}...')
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

                        print(f'Running {workload.name} {variant.name} {strategy.name} {property}...')
                        cfg = TrialConfig(workload=workload,
                                        strategy=strategy.name,
                                        property=property,
                                        trials=10,
                                        timeout=60,
                                        short_circuit=True)
                        run_trial(cfg)


if __name__ == '__main__':
    filepath = pathlib.Path(__file__).resolve().parent
    collect(pathlib.Path(filepath, 'results'))
