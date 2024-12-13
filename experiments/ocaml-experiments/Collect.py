import argparse
import os
from benchtool.OCaml import OCaml
from benchtool.Types import BuildConfig, ReplaceLevel, TrialConfig, PBTGenerator
from benchtool.Tasks import tasks

DEFAULT_DIR = 'oc3'
REPLACE = False

WORKLOADS = ['BST']
STRATEGIES : list[PBTGenerator] = [
    # PBTGenerator('qcheck', 'bespoke'),
    PBTGenerator('qcheck', 'type'),
    # PBTGenerator('crowbar', 'bespoke'),
    # PBTGenerator('crowbar', 'type'),
    # PBTGenerator('afl', 'bespoke'),
    # PBTGenerator('afl', 'type'),
]

TRIALS = 10
TIMEOUT = 65


def collect(directory: str, workloads=WORKLOADS, strategies=STRATEGIES):
    tool = OCaml(directory, replace_level=ReplaceLevel.REPLACE if REPLACE else ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in workloads:
            continue

        for variant in tool.all_variants(workload):
            if variant.name == 'base':
                continue

            run_trial = None
            for strategy in strategies:
                for property in tool.all_properties(workload):
                    if workload.name in ['BST', 'RBT']:
                        if property.split('_')[1] not in tasks[workload.name][variant.name]:
                            continue

                    if not run_trial:
                        run_trial = tool.apply_variant(workload, variant, BuildConfig(
                                    path=workload.path,
                                    clean=False,
                                    build_common=False,
                                    build_strategies=True,
                                    build_fuzzers=False,
                                    no_base=True,
                                ))

                    cfg = TrialConfig(workload=workload,
                                        strategy=strategy.strategy,
                                        framework=strategy.framework,
                                        property=property,
                                        label=strategy.framework + strategy.strategy.capitalize(),
                                        trials=TRIALS,
                                        timeout=TIMEOUT,
                                        short_circuit=False)

                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()
    dir = args.data if args.data else DEFAULT_DIR
    results_path = f'{os.getcwd()}/{dir}'
    collect(results_path)