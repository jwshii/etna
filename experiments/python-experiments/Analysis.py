import argparse
from functools import partial
from benchtool.Analysis import parse_results, overall_solved
from benchtool.Plot import stacked_barchart_times
import numpy as np
import os


def analyze(results: str, images: str):
    df = parse_results(results)
    df['timeout'] = np.where(df['strategy'] == 'Lean', 10, 60)
    df['foundbug'] = df['foundbug'] & (df['time'] < df['timeout'])

    if not os.path.exists(images):
        os.makedirs(images)

    # Compute solve rates.
    dfa = overall_solved(df, 'all').reset_index()
    dfa = dfa.groupby('strategy').sum(numeric_only=True)
    dfa['percent'] = dfa['solved'] / dfa['total']
    print(dfa)

    for workload in ['RBT']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=['arbitrary', 'bst_only', 'insert'],
            colors=['#000000', '#D61C4E', '#6D0E56'],
            limits=[0.1, 1, 10, 60],
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
    analyze(results_path, images_path)
