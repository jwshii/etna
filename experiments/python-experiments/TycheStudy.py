import argparse
from functools import partial
from benchtool.Analysis import parse_results, overall_solved
from benchtool.Plot import stacked_barchart_times
import numpy as np
import os
from benchtool.Python import Python
from benchtool.Types import LogLevel, TrialConfig

WORKLOADS = ['Expressions']
TRIALS = 1


def collect(results: str):
    tool = Python(results, log_level=LogLevel.INFO)

    for workload in tool.all_workloads():
        if workload.name not in WORKLOADS:
            continue

        for variant in tool.all_variants(workload):
            if variant.name == 'base':
                # Don't run on base (non-buggy) implementation.
                continue

            for strategy in tool.all_strategies(workload):
                for property in tool.all_properties(workload):
                    trials = TRIALS

                    run_trial = tool.apply_variant(workload, variant)

                    cfg = TrialConfig(
                        workload=workload,
                        strategy=strategy.name,
                        property=property,
                        trials=trials,
                        timeout=0,  # FIXME
                        short_circuit=True)

                    run_trial(cfg)


def analyze(results: str, images: str):
    df = parse_results(results)
    df['timeout'] = 60
    df['foundbug'] = df['foundbug'] & (df['time'] < df['timeout'])

    if not os.path.exists(images):
        os.makedirs(images)

    # Compute solve rates.
    dfa = overall_solved(df, 'all').reset_index()
    dfa = dfa.groupby('strategy').sum(numeric_only=True)
    dfa['percent'] = dfa['solved'] / dfa['total']
    print(dfa)

    for workload in WORKLOADS:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=['bad', 'ok', 'good'],
            colors=['#000000', '#D61C4E', '#6D0E56'],
            limits=[0.5, 1, 2, 4, 8],
            limit_type='time',
            image_path=images,
            show=False,
        )


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--figures', help='path to folder for figures')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    images_path = f'{os.getcwd()}/{args.figures}'
    collect(results_path)
    analyze(results_path, images_path)
