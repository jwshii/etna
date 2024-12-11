import os
import pathlib

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel, Variable
from benchtool.Tasks import tasks


def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)
    for workload in tool.all_workloads():
        if workload.name not in ['BSTProplang', 'RBTProplang', 'STLCProplang']:
            continue

        tool._preprocess(workload)

        for property in tool.all_properties(workload):
            old = f"(runLoop number_of_trials {property})"
            new = f"toMonad ∅ {property} tt"
            var = Variable(
                name="ToMonadShallowerProp",
                folder="Strategies",
                recursive=False,
                files=["*Generator.v"],
                variants=[old, new],
            )
            tool.update_variable(workload, var, 1)

            old = f"fun tt => (sample1 test_{property})"
            new = f"fun tt => (quickCheckWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) test_{property})"
            var = Variable(
                name="ToMonadShallowerRunner",
                folder="Runners",
                recursive=False,
                files=["*Generator_test_runner.v"],
                variants=[old, new],
            )
            tool.update_variable(workload, var, 1)

        for variant in tool.all_variants(workload):
            print(list(map(lambda v: v.name, tool.all_variants(workload))))
            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):
                if not strategy.name.endswith('Generator'):
                    continue

                for property in tool.all_properties(workload):
                    property = 'test_' + property
                    workloadname = workload.name[:-8]

                    file = f'{workload.name},{strategy.name},{variant.name},{property},toMonad'

                    if property[10:] not in tasks[workloadname][variant.name]:
                        print(f'Skipping {file}')
                        continue
                    
                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    
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
    filepath = pathlib.Path(__file__).resolve().parent
    collect(pathlib.Path(filepath, 'results'))

