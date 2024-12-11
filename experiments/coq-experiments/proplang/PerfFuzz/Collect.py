import os
import pathlib

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel, Entry, Variable
from benchtool.Tasks import tasks

def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

    for workload in tool.all_workloads():
        if not workload.name.endswith('SortingProplang'):
            continue

        tool._preprocess(workload)
        
        variants = [ f'Extract Constant number_of_trials => "{i}".' for i in [100, 1000]]
        var = Variable(
            name="NumTrials",
            folder="Strategies",
            recursive=False,
            files=["*Fuzzer.v"],
            variants=variants,
        )

        for i, _ in enumerate(variants):
            tool.update_variable(workload, var, i)

            run_trial = tool.just_build(workload)

            for strategy in tool.all_strategies(workload):
                print(f'Running {strategy.name} on {workload.name}')
                for property in ['prop_sort']:
                    print(f'Running {property} on {workload.name}')
                    property = 'test_' + property
                
                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    file = f'{workload.name},{strategy.name},{i},{property}'
                    if f'{file}.json' in finished:
                        continue
                    
                    cfg = TrialConfig(workload=workload,
                                        strategy=strategy.name,
                                        property=property,
                                        file=file,
                                        trials=30,
                                        timeout=30,
                                        short_circuit=True)
                    run_trial(cfg)


if __name__ == '__main__':
    filepath = pathlib.Path(__file__).resolve().parent
    collect(pathlib.Path(filepath, 'results'))

