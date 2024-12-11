from dataclasses import dataclass
from PIL import ImageColor
from benchtool.Analysis import overall_solved, task_average
import pandas as pd
import numpy as np
import plotly.express as px
import plotly.graph_objects as go
from dash import Dash, html, dcc, Input, Output
from typing import Literal, Optional

pd.options.mode.chained_assignment = None  # default='warn'


def light_gradient(rgb: tuple[int, int, int], n: int) -> list[tuple[int, int, int]]:
    top: tuple[int, int, int] = (240, 241, 241)

    gradient = list(
        map(lambda x: 'rgb' + str(tuple(x)),
            np.linspace(rgb, top, n).astype(int).tolist()))

    return gradient


@dataclass
class Bar:
    name: str
    values: list[int]
    color: str = None


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
    prefix: str = '',
):

    df = df[df['workload'] == case]

    if not strategies:
        strategies = sorted(df.strategy.unique())

    tasks = df.task.unique()
    total_tasks = len(tasks)

    results = pd.DataFrame(columns=limits, index=strategies, dtype=int, data=0)

    results['rest'] = total_tasks

    for within in limits:
        dft = overall_solved(df, agg=agg, within=within,
                             solved_type=limit_type)
        print(dft)
        dft = dft.reset_index()
        dft = dft.groupby(['strategy']).sum(numeric_only=False)
        print(dft)
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
    print(results)
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
        # paired color pallete
        colors = [
            '#000000',  # blue
            '#000000',  # blue
            '#334756',  # yellow
            '#334756',  # yellow
            '#436E4F',  # green
            '#436E4F',  # green
            '#900D0D',  # red
            '#900D0D',  # red
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
        font_size=60,
        font={'family': 'Helvetica'},
        width=1920,
        height=1080,
        showlegend=False,
    )

    # hide y axis title

    strategy_sorter = dict(map(lambda x: (x[1], x[0]), enumerate(strategies)))

    strategies = sorted(strategies,
                        key=lambda x: strategy_sorter[x] if x in strategy_sorter.keys() else -1)
    print(strategies)
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
        fig.write_image(f'{image_path}/{prefix}_{case}_{suffix}.png',
                        width=1600,
                        height=900,
                        scale=1,
                        engine='kaleido')

    if show:
        fig.show()


def dashboard(df: pd.DataFrame):
    app = Dash(__name__)

    div_style = {'width': '31%', 'float': 'left',
                 'display': 'inline-block', 'margin-right': '15px'}
    app.layout = html.Div([
        html.Div([
            html.Div([dcc.Dropdown(sorted(df['workload'].unique()), 'BST', id='workload')],
                     style=div_style),
            html.Div([
                dcc.Dropdown(['time', 'inputs'], 'time', id='col'),
                dcc.RadioItems(['linear', 'log'], 'linear',
                               id='yscale', inline=True)
            ],
                style=div_style),
            html.Div([
                dcc.Dropdown(
                    df['strategy'].unique(), df['strategy'].unique(), id='strategies', multi=True)
            ],
                style={
                'width': '31%',
                         'display': 'inline-block'
            })
        ],
            style={'margin-bottom': '15px'}),
        dcc.Graph(id='graph', style={'height': '85vh'})
    ])

    @app.callback(
        Output('graph', 'figure'),
        Input('workload', 'value'),
        Input('col', 'value'),
        Input('yscale', 'value'),
        Input('strategies', 'value'),
    )
    def update_graph(workload, col, yscale, strategies):
        dff = df[(df['workload'] == workload) & (
            df['strategy'].isin(strategies))]

        # Note: this only includes tasks that everyone solved
        dff = task_average(dff, col)

        dff = dff.reset_index()
        fig = px.bar(dff,
                     x='task',
                     y=col,
                     color='strategy',
                     barmode='group',
                     error_y=col + '_std',
                     log_y=yscale == 'log')
        return fig

    return app
