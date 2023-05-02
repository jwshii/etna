
from typing import Literal, Optional
from benchtool.Analysis import scandir_filter

import numpy as np
import pandas as pd
from functools import partial

from dataclasses import dataclass

import plotly.graph_objects as go

from PIL import ImageColor

import os


def parse_results(results: str, entry_filter: callable = None) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)

    if entry_filter:
        entries = list(filter(entry_filter, entries))

    df = pd.concat([pd.read_json(e.path, orient='records', typ='frame') for e in entries])

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['passed'], axis=1)

    df['task'] = df['bench'] + ',' + df['mutant'] + ',' + df['property']
    return df

def overall_solved(df: pd.DataFrame,
                   agg: Literal['any', 'all'],
                   within: Optional[float] = None,
                   solved_type: str = 'time'
                   ) -> pd.DataFrame:
    df = df.copy()

    # Define new column for whether found the bug within time limit.
    df['solved'] = df['foundbug']
    if within:
        df['solved'] &= df[solved_type] < within

    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(['bench', 'method', 'task'], as_index=False).agg({'solved': agg})
    df['total'] = 1
    df = df.groupby(['bench', 'method']).sum()

    return df[['solved', 'total']]



def light_gradient(rgb: tuple[int, int, int], n: int) -> list[tuple[int, int, int]]:
    top : tuple[int, int, int] = (240, 241, 241)

    gradient = list(map(
        lambda x: 'rgb' + str(tuple(x)),
        np.linspace(rgb, top, n).astype(int).tolist()
    ))

    return gradient

@dataclass
class Bar:
    name: str
    values : list[int]
    color: str = None


def stacked_barchart_times(
        case: str,
        df: pd.DataFrame,
        limits: list[float],
        limit_type: str,
        methods: list[str] = None,
        colors: list[str] = None,
        show: bool = True,
        save: Optional[str] = None,
        agg: Literal['any', 'all'] = 'all',
        manual_bars: list[Bar] = [],
    ):

    df = df[df['bench'] == case]

    if not methods:
        methods = df.method.unique()
    else:
        methods = methods[::-1]

    tasks = df.task.unique()
    total_tasks = len(tasks)

    results = pd.DataFrame(columns=limits, index=methods, dtype=int, data=0)

    results['rest'] = total_tasks

    for within in limits:
        dft = overall_solved(df, agg=agg, within=within, solved_type=limit_type)
        dft = dft.reset_index()
        dft = dft.groupby(['method']).sum()
        for method in methods:
            results.loc[method].loc[within] = dft.loc[method]['solved'] - (total_tasks - results.loc[method].loc['rest'])
            results.loc[method].loc['rest'] = results.loc[method].loc['rest'] - results.loc[method].loc[within]

    results = results.rename_axis('method')
    results = results.reset_index()

    results = results.melt(id_vars=['method'], value_vars=limits + ['rest'])

    if not colors:
        colors = [
            "#000000", # black
            "#900D0D", # red
            "#DC5F00", # orange
            "#243763", # blue
            "#436E4F", # green
            "#470938", # purple
            "#D61C4E", # pink
            "#334756", # dark blue
            "#290001", # dark brown
            "#000000", # black
        ]

    extrapolated_colors = list(map(light_gradient, map(ImageColor.getrgb, colors), [len(limits) + 1] * len(colors)))

    fig = go.Figure()
    fig.update_layout(
        title=f'',
        xaxis=go.layout.XAxis(
            showticklabels=False,
        ),
        yaxis=go.layout.YAxis(
            title='',
            showticklabels=False,
        ),
        font_size=60,
        font={'family': 'Helvetica'},
        width=1920,
        height=1080,
        showlegend=False,
    )

    # hide y axis title


    method_sorter = dict(map(lambda x: (x[1], x[0]), enumerate(methods)))

    methods = sorted(methods, key=lambda x: method_sorter[x] if x in method_sorter.keys() else -1)



    for method, color in zip(methods[::-1], extrapolated_colors):
        fig.add_trace(go.Bar(
            x=results[results['method'] == method]['value'],
            y=results[results['method'] == method]['method'],
            name=method,
            marker_color=color,
            text=results[results['method'] == method]['value'],
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
        fig.add_trace(go.Bar(
            x=bar.values,
            y=np.array([bar.name] * (len(limits) + 1)),
            name=bar.name,
            marker_color=light_gradient(ImageColor.getrgb(bar.color), len(limits) + 1),
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

    if save:
        fig.write_image(f"draft/figures/{case},{save}.png"
                        , width=1600
                        , height=900
                        , scale=1
                        , engine='kaleido'
                        )

    if show:
        fig.show()