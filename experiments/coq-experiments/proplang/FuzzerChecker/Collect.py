import os
import pathlib
from typing import List

from benchtool.Coq import Coq
from benchtool.Types import BuildConfig, TrialConfig, ReplaceLevel, LogLevel, Variable

def collect_fuzzers(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

    for workload in tool.all_workloads():
        if not workload.name.endswith('IFCProplang'):
            continue

        tool._preprocess(workload)

        seed_pools : Variable = next(filter(lambda v: v.name == "SeedPool", tool.all_variables(workload)))
        energy_levels : List[Variable] = list(filter(lambda v: v.name.startswith("Energy"), tool.all_variables(tool.common())))
        print(seed_pools)
        while seed_pools.current is not None:
            print(f'Running Seedpool {workload.name},{seed_pools.variants[seed_pools.current]}')
            # Iterates over different seedpool data types such as Heap, FIFO, FILO, etc.
            energies = next(filter(lambda v: v.name == f"Energy-{seed_pools.variants[seed_pools.current]}", energy_levels))
            while energies.current is not None:
                print(f'Running {workload.name},{seed_pools.variants[seed_pools.current]},{energies.variants[energies.current]}')
                # Iterates over different energy levels such as 1, 10, 100, 1000.
                for variant in tool.all_variants(workload):
                    print(f'Running {workload.name},{seed_pools.variants[seed_pools.current]},{energies.variants[energies.current]},{variant.name}')

                    if variant.name == 'base':  
                        continue

                    run_trial = None

                    for strategy in tool.all_strategies(workload):
                        print(f'Running {workload.name},{strategy.name},{variant.name}')
                        if not strategy.name.endswith('VariationalMutatingGenerator'):
                            continue

                        print(f'Running {workload.name},{strategy.name},{variant.name}')

                        for property in ["propLLNI"]:
                            print(f'Running p {workload.name},{strategy.name},{variant.name},{property}')
                            property = 'test_' + property
                            # Don't compile tasks that are already completed.
                            finished = set(os.listdir(results))
                            file = f'{workload.name},{strategy.name},{variant.name},{property},{seed_pools.variants[seed_pools.current]},{energies.variants[energies.current]}'
                            if f'{file}.json' in finished:
                                print(f'{file} already exists')
                                continue

                            if not run_trial:
                                run_trial = tool.apply_variant(workload, variant, BuildConfig(
                                    path=workload.path,
                                    clean=True,
                                    build_common=True,
                                    build_strategies=True,
                                    build_fuzzers=False,
                                    no_base=True,
                                ))
                            print(f'Running trial {workload.name},{strategy.name},{variant.name},{property}')
                            cfg = TrialConfig(workload=workload,
                                                strategy=strategy.name,
                                                property=property,
                                                file=file,
                                                trials=10,
                                                timeout=60,
                                                short_circuit=True,
                                                experiment_id=f"FuzzerChecker/{file}.json"
                                )
                            run_trial(cfg)
                print("Updating energies")
                print(1, energies)
                tool.update_variable(tool.common(), energies)
                print(2, energies)
            print("Updating seedpools")
            tool.update_variable(workload, seed_pools)


def collect_bespoke_generator(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

    for workload in tool.all_workloads():
        if not workload.name.endswith('IFCProplang'):
            continue

        tool._preprocess(workload)

        for variant in tool.all_variants(workload):
            run_trial = None

            for strategy in tool.all_strategies(workload):
                print(f'Running {workload.name},{strategy.name},{variant.name}')
                if not strategy.name.startswith('BespokeLLNIGenerator'):
                    continue

                print(f'Running {workload.name},{strategy.name},{variant.name}')

                for property in ["propLLNI"]:
                    print(f'Running Prop {workload.name},{strategy.name},{variant.name},{property}')
                    property = 'test_' + property
                    # Don't compile tasks that are already completed.
                    finished = set(os.listdir(results))
                    file = f'{workload.name},{strategy.name},{variant.name},{property}'
                    if f'{file}.json' in finished:
                        continue

                    if not run_trial:
                        run_trial = tool.apply_variant(workload, variant, BuildConfig(
                            path=workload.path,
                            clean=True,
                            build_common=False,
                            build_strategies=True,
                            build_fuzzers=False,
                            no_base=True,
                        ))
                    print(f'Running {workload.name},{strategy.name},{variant.name},{property}')
                    cfg = TrialConfig(workload=workload,
                                        strategy=strategy.name,
                                        property=property,
                                        file=file,
                                        trials=10,
                                        timeout=60,
                                        short_circuit=True,
                                        experiment_id=f"FuzzerChecker/{file}.json"
                    )
                    run_trial(cfg)


if __name__ == '__main__':
    filepath = pathlib.Path(__file__).resolve().parent
    collect_bespoke_generator(pathlib.Path(filepath, 'results'))
    collect_fuzzers(pathlib.Path(filepath, 'results'))
