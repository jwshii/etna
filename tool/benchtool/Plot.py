from dataclasses import dataclass
from PIL import ImageColor
from benchtool.Analysis import overall_solved, task_average
import pandas as pd
import numpy as np
import plotly.express as px
import plotly.graph_objects as go
from dash import Dash, html, dcc, Input, Output
from typing import Literal, Optional

# TODO fix names here

pd.options.mode.chained_assignment = None  # default='warn'

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

    tasks = df.task.unique()
    total_tasks = len(tasks)

    results = pd.DataFrame(columns=limits, index=methods, dtype=int, data=0)

    results['rest'] = total_tasks

    for within in limits:
        dft = overall_solved(df, agg=agg, within=within, solved_type=limit_type)
        dft = dft.reset_index()
        dft = dft.groupby(['method']).sum()
        for method in methods:
            # Note: I think the new version of Pandas broke some of this code.
            # Use 1.5.3 for now and come back and fix.
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
        fig.write_image(f"{save}.png"
                        , width=1600
                        , height=900
                        , scale=1
                        , engine='kaleido'
                        )

    if show:
        fig.show()

def dashboard(df: pd.DataFrame):
    app = Dash(__name__)

    div_style = {'width': '31%', 'float': 'left', 'display': 'inline-block', 'margin-right': '15px'}
    app.layout = html.Div([
        html.Div([
            html.Div([dcc.Dropdown(sorted(df['bench'].unique()), 'BST', id='bench')],
                     style=div_style),
            html.Div([
                dcc.Dropdown(['time', 'inputs'], 'time', id='col'),
                dcc.RadioItems(['linear', 'log'], 'linear', id='yscale', inline=True)
            ],
                     style=div_style),
            html.Div([
                dcc.Dropdown(df['method'].unique(), df['method'].unique(), id='methods', multi=True)
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
        Input('bench', 'value'),
        Input('col', 'value'),
        Input('yscale', 'value'),
        Input('methods', 'value'),
    )
    def update_graph(bench, col, yscale, methods):
        dff = df[(df['bench'] == bench) & (df['method'].isin(methods))]

        # Note: this only includes tasks that everyone solved
        dff = task_average(dff, col)

        dff = dff.reset_index()
        fig = px.bar(dff,
                     x='task',
                     y=col,
                     color='method',
                     barmode='group',
                     error_y=col + '_std',
                     log_y=yscale == 'log')
        return fig

    return app