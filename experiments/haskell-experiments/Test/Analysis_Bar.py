import argparse
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial


def analyze(results: str, local_results: str, images: str):
    df = parse_results(results)
    df_local = parse_results(local_results)

    print(df_local)

    df['timeout'] = np.where(df['strategy'] == 'Lean', 10, 60)
    df['foundbug'] = df['foundbug'] & (df['time'] < df['timeout'])
    df_local['timeout'] = np.where(df_local['strategy'] == 'Lean', 10, 60)
    df_local['foundbug'] = df_local['foundbug'] & (
        df_local['time'] < df_local['timeout'])

    if not os.path.exists(images):
        os.makedirs(images)

    # Generate task bucket charts used in Figure 1.
    # for workload in ['LuParser']:
    #     times = partial(stacked_barchart_times, case=workload, df=df)
    #     times(
    #         strategies=['Correct'],
    #         colors=['#6D0E56'],
    #         limits=[10],
    #         limit_type='time',
    #         image_path=images,
    #         show=False,
    #     )

    # df = df[(df['strategy'] == 'Correct') | (df['strategy'] == 'Hybrid')]

    # # Original code for figure
    # fig = px.bar(df, x='task', y='inputs', color='strategy',
    #              labels={'method': 'Method'})
    # fig.update_layout(barmode='group')
    # fig.show()

    def create_color_gradient(start_color, end_color, n):
        start = np.array(start_color)
        end = np.array(end_color)
        return [start + (end - start) * i / (n - 1) for i in range(n)]

    # TODO: Refactor to Plot.py
    fig = go.Figure()

    # Create a color gradient for the number of strategies
    unique_strategies = len(df['strategy'].unique())
    gradient_colors = create_color_gradient(
        [200, 200, 255], [0, 0, 255], unique_strategies)

    for idx, strategy in enumerate(df['strategy'].unique()):
        color = f'rgb({gradient_colors[idx][0]}, {gradient_colors[idx][1]}, {gradient_colors[idx][2]})'
        fig.add_trace(go.Bar(
            x=df[df['strategy'] == strategy]['task'],
            y=df[df['strategy'] == strategy]['inputs'],
            name=strategy + " (Remote)",
            # You can change the color as needed
            marker_color=color
        ))

    unique_strategies = len(df_local['strategy'].unique())
    gradient_colors = create_color_gradient(
        [250, 200, 200], [255, 0, 0], unique_strategies)
    # Add traces for the second DataFrame
    for idx, strategy in enumerate(df_local['strategy'].unique()):
        color = f'rgb({gradient_colors[idx][0]}, {gradient_colors[idx][1]}, {gradient_colors[idx][2]})'
        fig.add_trace(go.Bar(
            x=df_local[df_local['strategy'] == strategy]['task'],
            y=df_local[df_local['strategy'] == strategy]['inputs'],
            name=strategy + " (Local)",
            # You can change the color as needed
            marker_color=color
        ))

    # Update layout
    fig.update_layout(
        barmode='group',
        title="Comparison of Local and Remote Results",
        xaxis_title="Task",
        yaxis_title="Inputs",
        legend_title="Strategy"
    )

    # Show the figure
    fig.show()

    # # Compute solve rates.
    # dfa = overall_solved(df, 'all').reset_index()
    # dfa = dfa.groupby('strategy').sum(numeric_only=True)
    # dfa['percent'] = dfa['solved'] / dfa['total']
    # print(dfa)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--remote', help='path to folder for JSON data')
    p.add_argument('--figures', help='path to folder for figures')
    p.add_argument('--local', help='path to folder for local JSON data')
    args = p.parse_args()

    results_path = f'{os.path.join(os.getcwd(), args.remote)}'
    local_results_path = f'{os.path.join(os.getcwd(), args.local)}'
    images_path = f'{os.path.join(os.getcwd(), args.figures)}'
    analyze(results_path, local_results_path, images_path)
