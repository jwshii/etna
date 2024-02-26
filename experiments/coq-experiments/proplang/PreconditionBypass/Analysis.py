import pathlib

from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial
import itertools

def analyze(results: str, images: str):
    df = parse_results(results)

    if not os.path.exists(images):
        os.makedirs(images)

    for workload in ['RBTProplang', 'STLCProplang','BSTProplang']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=[
                'BespokeGenerator'
            ],
            # colors=['#000000', '#900D0D', '#DC5F00', '#243763', '#FFD700'],
            limits=[0.1, 1, 10, 60],
            limit_type='time',
            image_path=images,
            show=False,
        )

    df = df[df['foundbug']]
    df['throughput'] = (df['inputs'] + df['discards']) / df['time']

    # Calculate the mean throughput for each workload and strategy
    df = df.groupby(['workload', 'strategy']).mean().reset_index()
    df.to_csv(f'{images}/mean.csv')


if __name__ == "__main__":

    filepath = pathlib.Path(__file__).resolve().parent

    results_path = f'{filepath}/results'
    images_path = f'{filepath}/figures'
    analyze(results_path, images_path)
