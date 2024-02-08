import argparse
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial


def analyze(results: str, results2: str, images: str):
    df = parse_results(results)
    df2 = parse_results(results2)

    print(df[df['foundbug'] == False])

    df['timeout'] = np.where(df['strategy'] == 'Lean', 10, 60)
    df['foundbug'] = df['foundbug'] & (df['time'] < df['timeout'])
    df2['timeout'] = np.where(df2['strategy'] == 'Lean', 10, 60)
    df2['foundbug'] = df2['foundbug'] & (df2['time'] < df2['timeout'])

    if not os.path.exists(images):
        os.makedirs(images)

    # Generate task bucket charts used in Figure 1.
    for workload in ['LuParser']:
        times = partial(double_stacked_barchart_times, case=workload, df=df, df2=df2)
        times(
            strategies=['Correct', 'Hybrid', 'Random'],
            limits=[0.01, 0.02, 0.05, 0.1, 1, 10, 60],
            limit_type='time',
            image_path=images,
            show=True,
        )

    # Compute solve rates.
    dfa = overall_solved(df, 'all').reset_index()
    dfa = dfa.groupby('strategy').sum(numeric_only=True)
    dfa['percent'] = dfa['solved'] / dfa['total']
    print(dfa)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--ldata', help='path to folder for Local JSON data')
    p.add_argument('--rdata', help='path to folder for Remote JSON data')
    p.add_argument('--figures', help='path to folder for figures')
    args = p.parse_args()

    # TODO: take in args
    results_path = f'{os.getcwd()}/{args.ldata}'
    results2_path = f'{os.getcwd()}/{args.rdata}'
    images_path = f'{os.getcwd()}/{args.figures}'
    analyze(results_path, results2_path, images_path)
