import pathlib
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial

from PIL import ImageColor, Image, ImageDraw, ImageFont

def process_data(results: str, figures: str):
    df = parse_results(results)
    charter = partial(
        stacked_barchart_times,
        df=df,
        limits=[0.1, 1, 10, 60],
        limit_type="time",
        strategies=["ProplangBespoke", "RackcheckBespoke"],
    )
    bst = charter(case="BST", image_path=figures)
    rbt = charter(case="RBT", image_path=figures)
    stlc = charter(case="STLC", image_path=figures)

    bst["workload"] = "BST"
    rbt["workload"] = "RBT"
    stlc["workload"] = "STLC"

    df = pd.concat([bst, rbt, stlc])

    # Turn variable/value into column, where each variable has its own column and value is the value of that column.
    df = df.pivot(
        index=["strategy", "workload"], columns="variable", values="value"
    ).reset_index()

    df.sort_values(by=["workload", "strategy"], inplace=True)

    df.to_csv(f"{figures}/workloads.csv", index=False)

    return df


def plot_data(df: pd.DataFrame, figures: str, limit_type: str, prefix: str, case: str, show_names: bool = False):
    # Generate task bucket charts used in Figure 3.
    limits = [0.1, 1, 10, 60, "rest"]
    colors = [
        "#000000",  # black
        "#900D0D",  # red
        "#DC5F00",  # orange
        "#243763",  # blue
        "#436E4F",  # green
        "#470938",  # purple
        "#D61C4E",  # pink
        "#334756",  # dark blue
        "#290001",  # dark brown
        "#000000",  # black
    ]

    extrapolated_colors = list(
        map(
            light_gradient,
            map(ImageColor.getrgb, colors),
            [len(limits) + 1] * len(colors),
        )
    )

    fig = go.Figure()
    fig.update_layout(
        title=f"",
        xaxis=go.layout.XAxis(
            showticklabels=False,
        ),
        yaxis=go.layout.YAxis(
            title="",
            showticklabels=True,
        ),
        font_size=60,
        font={"family": "Helvetica"},
        width=1920,
        height=1080,
        showlegend=False,
    )

    # hide y axis title

    strategies = df["strategy"].unique()

    strategy_sorter = dict(map(lambda x: (x[1], x[0]), enumerate(strategies)))

    strategies = sorted(
        strategies,
        key=lambda x: strategy_sorter[x] if x in strategy_sorter.keys() else -1,
    )

    tasks = {
        "BST": 53,
        "RBT": 73,
        "STLC": 20,
    }
    # Create a horizontal stacked bar chart with the following constraints:
    # - y-axis is the strategy
    # - x-axis is the number of tasks solved within a time limit
    # - colors denote the time limit, we create a gradient of colors for each strategy

    def tokey(x):
        return str(float(x)) if x != "rest" else "rest"

    def luma(r, g, b):
        return 0.299 * r + 0.587 * g + 0.114 * b
    
    suffix = "time" if limit_type == "time" else "inputs"
    im = Image.new("RGB", (1920, 1080), (255, 255, 255))
    draw = ImageDraw.Draw(im)
    font = ImageFont.truetype("/System/Library/Fonts/Supplemental/Arial Bold.ttf", 60)

    total_width = 1720
    x_start = 100
    total_tasks = tasks[case]

    if show_names:
        total_width = 1120
        x_start = 700
        for i, strategy in enumerate(strategies):
            draw.text(
                (100, 275 + 500 * i),
                strategy,
                (0, 0, 0),
                font=font,
            )

    
    print(total_tasks)
    for j, strategy in enumerate(strategies):
        current_y = 100 + 500 * j
        current_x = x_start
        for i, limit in enumerate(limits):
            print(extrapolated_colors[j][i], luma(*ImageColor.getrgb(extrapolated_colors[j][i])))
            color = ImageColor.getrgb(extrapolated_colors[j][i]) if limit != "rest" else (240, 240, 240)
            value = df[(df["strategy"] == strategy) & (df["workload"] == case)][
                tokey(limit)
            ].values[0]
            print(strategy, limit, value)
            width_value = (value / total_tasks) * total_width
            draw.rectangle(
                [
                    (current_x, current_y),
                    (current_x + width_value, current_y + 200),
                ],
                fill=color
            )
            if width_value > 40:
                draw.text(
                    (current_x + width_value / 2, current_y + 180),
                    str(value),
                    (0, 0, 0) if luma(*ImageColor.getrgb(extrapolated_colors[j][i])) > 100 else (255, 255, 255),
                    font=font,
                )
            current_x += width_value

    im.save(f"{figures}/{prefix}_{case}_{suffix}.png")


if __name__ == "__main__":
    filepath = pathlib.Path(__file__).resolve().parent
    results_path = f"{filepath}/results"
    images_path = f"{filepath}/figures"
    # analyze(results_path, images_path)
    df = process_data(results_path, images_path)
    df = pd.read_csv(f"{images_path}/workloads.csv", index_col=False)
    for case in ["BST", "RBT", "STLC"]:
        plot_data(df, images_path, "time", "task_bucket", case, show_names=False)
        plot_data(df, images_path, "time", "task_bucket_named", case, show_names=True)
