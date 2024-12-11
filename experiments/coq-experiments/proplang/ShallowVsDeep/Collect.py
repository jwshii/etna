import os
import pathlib

from benchtool.Coq import Coq
from benchtool.Types import BuildConfig, TrialConfig, ReplaceLevel, LogLevel
from benchtool.Tasks import tasks


def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)
    for workload in tool.all_workloads():
        if workload.name not in [
                                # 'BST',
                                'BSTProplang', 
                                #  'RBT', 
                                 'RBTProplang',
                                #  'STLC',
                                 'STLCProplang'
                                 ]:
            continue

        tool._preprocess(workload)

        for variant in tool.all_variants(workload):
            print(list(map(lambda v: v.name, tool.all_variants(workload))))
            if variant.name == 'base':
                continue

            run_trial = None

            for strategy in tool.all_strategies(workload):
                print(f'Processing {workload.name},{strategy.name},{variant.name}')
                if strategy.name != "TypeBasedFuzzer":
                    continue
                # print(f'Processing {workload.name},{strategy.name},{variant.name}')
                for property in tool.all_properties(workload):

                    property = 'test_' + property
                    workloadname = workload.name.removesuffix("Proplang")

                    if property[10:] not in tasks[workloadname][variant.name]:
                        print(f'Skipping {workload.name},{strategy.name},{variant.name},{property}')
                        continue
                    
                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    suffix = "deeper" if strategy.name.startswith("Proplang") else "shallow"

                    file = f'{workload.name},{strategy.name},{variant.name},{property},{suffix}'
                    if f'{file}.json' in finished:
                        continue

                    if not run_trial:
                        run_trial = tool.apply_variant(workload, variant, BuildConfig(
                            path=workload.path,
                            clean=True,
                            build_common=True,
                            build_strategies=True,
                            build_fuzzers=True,
                            no_base=True,
                        ))

                    cfg = TrialConfig(workload=workload,
                                        strategy=strategy.name,
                                        property=property,
                                        file=file,
                                        trials=10,
                                        timeout=60,
                                        short_circuit=True,
                                        experiment_id=f"ShallowVsDeep-Coq/{file}.json")
                    run_trial(cfg)


if __name__ == '__main__':
    filepath = pathlib.Path(__file__).resolve().parent
    collect(pathlib.Path(filepath, 'results'))

