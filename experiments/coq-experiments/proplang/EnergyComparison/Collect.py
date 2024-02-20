import os
import pathlib

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel, LogLevel, Entry
from benchtool.Tasks import tasks

def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

    common = tool.common()

    variables = list(filter(lambda v: v.name == "Energy-v1", tool.all_variables(common)))
    mixtures = tool.all_variable_mixtures(variables)

    for workload in tool.all_workloads():
        if not workload.name.endswith('Proplang'):
            continue

        tool._preprocess(workload)

        for mixture in mixtures:
            print("Mixture")
            for variable, version  in mixture:
                print(f"Applying Variable {variable}::{version}")
                tool.update_variable(common, variable, version)

            for variant in tool.all_variants(workload):

                if variant.name == 'base':
                    continue

                run_trial = None

                for strategy in tool.all_strategies(workload):
                    if not strategy.name.endswith('Fuzzer'):
                        continue

                    for property in tool.all_properties(workload):
                        property = 'test_' + property
                        workloadname = workload.name if not workload.name.endswith('Proplang') else workload.name[:-8]
                        if property[10:] not in tasks[workloadname][variant.name]:
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
    filepath = pathlib.Path(__file__).resolve().parent
    collect(pathlib.Path(filepath, 'results'))

