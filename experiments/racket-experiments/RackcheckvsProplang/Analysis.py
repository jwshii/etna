import pathlib
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial


def analyze(results: str, images: str):
    df = parse_results(results)
    print(df['time'])
    print(df['strategy'])
    if not os.path.exists(images):
        os.makedirs(images)

    # Generate task bucket charts used in Figure 3.
    for workload in ['BST', 'RBT']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=[
                'ProplangBespoke',
                'RackcheckBespoke',
            ],
            colors=['#000000', '#900D0D', '#DC5F00', '#243763'],
            limits=[0.1, 1, 10, 60],
            limit_type='time',
            image_path=images,
            show=False,
        )

if __name__ == "__main__":
    filepath = pathlib.Path(__file__).resolve().parent
    results_path = f'{filepath}/results'
    images_path = f'{filepath}/figures'
    analyze(results_path, images_path)
