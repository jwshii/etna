import pathlib

from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial
import itertools

def df_insert(df: pd.DataFrame, column: str, value: any) -> pd.DataFrame:
    df.insert(len(df.columns), column, value)
    return df

def parse_results(results: str) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)
    entries = [e for e in entries if e.path.endswith('.json')]

    df = pd.concat([df_insert(pd.read_json(e.path, orient='records', typ='frame'), "version", e.name.split(',')[4]) for e in entries])
    df = df[df['version'] == "toMonad.json"]

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['passed'], axis=1)

    df['task'] = df['workload'] + ',' + df['mutant'] + ',' + df['property']
    return df


def analyze(results: str, images: str):
    df = parse_results(results)

    if not os.path.exists(images):
        os.makedirs(images)

    print(df)
    for workload in ['RBTProplang', 'STLCProplang', 'BSTProplang']:
        times = partial(stacked_barchart_times, case=workload, df=df, prefix='toMonad')
        times(
            strategies=[
                'TypeBasedGenerator', 
                'SpecificationBasedGenerator',
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
    df.to_csv(f'{images}/toMonad_mean.csv')


if __name__ == "__main__":

    filepath = pathlib.Path(__file__).resolve().parent

    results_path = f'{filepath}/results'
    images_path = f'{filepath}/figures'
    analyze(results_path, images_path)
