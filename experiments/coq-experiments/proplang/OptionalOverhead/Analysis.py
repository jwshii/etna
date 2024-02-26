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

    df = pd.concat([df_insert(pd.read_json(e.path, orient='records', typ='frame'), "version", e.name.split(',')[2]) for e in entries])

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['passed'], axis=1)

    df['task'] = df['workload'] + ',' + df['mutant'] + ',' + df['property']
    return df


def overall_solved(df: pd.DataFrame,
                   agg: Literal['any', 'all'],
                   within: Optional[float] = None,
                   solved_type: str = 'time') -> pd.DataFrame:
    df = df.copy()

    # Define new column for whether found the bug within time limit.
    df['solved'] = df['foundbug']
    if within:
        df['solved'] &= df[solved_type] < within

    df['strategy'] = df['strategy'] + '-' + df['version']
    del df['version']
    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(['workload', 'strategy', 'task'], as_index=False).agg({'solved': agg})
    df['total'] = 1
    df = df.groupby(['workload', 'strategy']).sum(numeric_only=False)

    return df[['solved', 'total']]


def stacked_barchart_times(
    case: str,
    df: pd.DataFrame,
    limits: list[float],
    limit_type: str,
    strategies: list[str] = None,
    colors: list[str] = None,
    show: bool = True,
    image_path: Optional[str] = None,
    agg: Literal['any', 'all'] = 'all',
    manual_bars: list[Bar] = [],
):

    df = df[df['workload'] == case]

    if not strategies:
        strategies = df.strategy.unique()

    vmap = {
        '0': 'PropLang',
        '1': 'MiniPropLang',
    }

    df['version'] = df['version'].apply(lambda x: vmap[x])

    versions = df.version.unique()

    print(versions)

    strategies = [f"{strategy[0]}-{strategy[1]}" for strategy in itertools.product(strategies, versions)]
    
    tasks = df.task.unique()
    total_tasks = len(tasks)

    results = pd.DataFrame(columns=limits, index=strategies, dtype=int, data=0)

    results['rest'] = total_tasks

    for within in limits:
        dft = overall_solved(df, agg=agg, within=within, solved_type=limit_type)
        print(dft)
        dft = dft.reset_index()
        dft = dft.groupby(['strategy']).sum(numeric_only=False)
        for strategy in strategies:
            # Note: I think the new version of Pandas broke some of this code.
            # Use 1.5.3 for now and come back and fix.
            results.loc[strategy].loc[within] = dft.loc[strategy]['solved'] - (
                total_tasks - results.loc[strategy].loc['rest'])
            results.loc[strategy].loc[
                'rest'] = results.loc[strategy].loc['rest'] - results.loc[strategy].loc[within]

    results = results.rename_axis('strategy')
    results = results.reset_index()

    results = results.melt(id_vars=['strategy'], value_vars=limits + ['rest'])

    if not colors:
        colors = [
            '#000000',  # black
            '#900D0D',  # red
            '#DC5F00',  # orange
            '#243763',  # blue
            '#436E4F',  # green
            '#470938',  # purple
            '#D61C4E',  # pink
            '#334756',  # dark blue
            '#290001',  # dark brown
            '#000000',  # black
        ]

    extrapolated_colors = list(
        map(light_gradient, map(ImageColor.getrgb, colors), [len(limits) + 1] * len(colors)))

    fig = go.Figure()
    fig.update_layout(
        title=f'',
        xaxis=go.layout.XAxis(showticklabels=False,),
        yaxis=go.layout.YAxis(
            title='',
            showticklabels=True,
        ),
        font_size=20,
        font={'family': 'Helvetica'},
        width=1920,
        height=1080,
        showlegend=False,
    )

    # hide y axis title

    strategy_sorter = dict(map(lambda x: (x[1], x[0]), enumerate(strategies)))

    strategies = sorted(strategies,
                        key=lambda x: strategy_sorter[x] if x in strategy_sorter.keys() else -1)

    for strategy, color in zip(strategies[::-1], extrapolated_colors):
        fig.add_trace(
            go.Bar(
                x=results[results['strategy'] == strategy]['value'],
                y=results[results['strategy'] == strategy]['strategy'],
                name=strategy,
                marker_color=color,
                text=results[results['strategy'] == strategy]['value'],
                orientation='h',
                width=0.8,
                textposition='auto',
                textfont_size=60,
                textfont={'family': 'Helvetica'},
                textangle=0,
                cliponaxis=False,
                insidetextanchor='middle',
                # don't show name on y axis
            ))

    for bar in manual_bars:
        fig.add_trace(
            go.Bar(
                x=bar.values,
                y=np.array([bar.name] * (len(limits) + 1)),
                name=bar.name,
                marker_color=light_gradient(ImageColor.getrgb(bar.color),
                                            len(limits) + 1),
                text=bar.values,
                orientation='h',
                width=0.8,
                textposition='auto',
                textfont_size=60,
                textfont={'family': 'Helvetica'},
                textangle=0,
                cliponaxis=False,
                insidetextanchor='middle',
            ))

    if image_path:
        suffix = 'time' if limit_type == 'time' else 'inputs'
        fig.write_image(f'{image_path}/{case}_{suffix}.png',
                        width=1600,
                        height=900,
                        scale=1,
                        engine='kaleido')

    if show:
        fig.show()


def analyze(results: str, images: str):
    df = parse_results(results)

    print(df)
    if not os.path.exists(images):
        os.makedirs(images)

    for workload in ['BSTProplang']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            # colors=['#000000', '#900D0D', '#DC5F00', '#243763', '#FFD700'],
            limits=[0.1, 1, 10, 60],
            limit_type='time',
            image_path=images,
            show=False,
        )


    for workload in ['RBTProplang']:
        times = partial(stacked_barchart_times, case=workload, df=df)
        times(
            strategies=[
                'BespokeGenerator',
                'TypeBasedGenerator',
                'TypeBasedFuzzer',
                'SpecificationBasedGenerator',
            ],
            colors=['#000000', '#900D0D', '#DC5F00', '#243763', '#FFD700'],
            limits=[0.1, 1, 10, 60],
            limit_type='time',
            image_path=images,
            show=False,
        )


    df['throughput'] = (df['inputs'] + df['discards']) / df['time']

    # Calculate the mean throughput for each workload and strategy
    df = df.groupby(['workload', 'strategy', 'version']).mean().reset_index()
    df.to_csv(f'{images}/mean.csv')

if __name__ == "__main__":

    filepath = pathlib.Path(__file__).resolve().parent

    results_path = f'{filepath}/results'
    images_path = f'{filepath}/figures'
    analyze(results_path, images_path)
