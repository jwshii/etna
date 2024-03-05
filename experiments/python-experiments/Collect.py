import argparse
import os

from benchtool.Python import Python
from benchtool.Types import LogLevel, TrialConfig


def collect(results: str):
    tool = Python(results, log_level=LogLevel.DEBUG)

    for workload in tool.all_workloads():
        if workload.name not in ['Toposort']:
            continue

        for variant in tool.all_variants(workload):
            if variant.name == 'base':
                # Don't run on base (non-buggy) implementation.
                continue

            for strategy in tool.all_strategies(workload):
                for property in tool.all_properties(workload):
                    trials = 1

                    run_trial = tool.apply_variant(workload, variant)

                    cfg = TrialConfig(
                        workload=workload,
                        strategy=strategy.name,
                        property=property,
                        trials=trials,
                        timeout=0,  # FIXME
                        short_circuit=True)

                    run_trial(cfg)


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path)
