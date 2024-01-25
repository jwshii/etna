import argparse
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial


def analyze(results: str, images: str):
    df = parse_results(results)

    print(df[df['foundbug'] == False])

    df['timeout'] = np.where(df['strategy'] == 'Lean', 10, 60)
    df['foundbug'] = df['foundbug'] & (df['time'] < df['timeout'])

    if not os.path.exists(images):
        os.makedirs(images)

    # Generate task bucket charts used in Figure 1.
    for workload in ['LuParser']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=['Random', 'Hybrid', 'Correct'],
            colors=['#6D0E56'],
            limits=[0.01, 0.02, 0.05, 0.1, 0.2, 0.5],
            limit_type='time',
            image_path=images,
            show=False,
        )

    # Compute solve rates.
    dfa = overall_solved(df, 'all').reset_index()
    dfa = dfa.groupby('strategy').sum(numeric_only=True)
    dfa['percent'] = dfa['solved'] / dfa['total']
    print(dfa)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--figures', help='path to folder for figures')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    images_path = f'{os.getcwd()}/{args.figures}'
    analyze(results_path, images_path)
