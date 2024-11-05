import pathlib
from typing import Literal, Optional
from benchtool.Analysis import *
from benchtool.Plot import *
from itertools import product

from PIL import ImageColor, Image, ImageDraw, ImageFont

import os
import json
import pandas as pd
import plotly.graph_objects as go


@dataclass
class Result:
    workload: str
    discards: int
    foundbug: bool
    strategy: str
    mutant: str
    passed: int
    property: str
    time: float
    counterexample: str | None
    process_time: float | None
    process_time_monotonic: float | None

    def task(self) -> str:
        return f"{self.mutant}-{self.property}"


def parse_results(results: str) -> list[Result]:
    entries = scandir_filter(results, os.path.isfile)
    entries = [e for e in entries if e.path.endswith(".json")]

    results = []

    for entry in entries:
        runs = json.load(open(entry.path))
        for run in runs:
            results.append(Result(
                workload=run.get("workload"),
                discards=run.get("discards"),
                foundbug=run.get("foundbug"),
                strategy=run.get("strategy"),
                mutant=run.get("mutant"),
                passed=run.get("passed"),
                property=run.get("property"),
                time=run.get("time"),
                counterexample=run.get("counterexample"),
                process_time=run.get("process_time"),
                process_time_monotonic=run.get("process_time_monotonic")
            ))

    return results


def overall_solved(
    df: pd.DataFrame,
    agg: Literal["any", "all"],
    within: Optional[float] = None,
    solved_type: str = "time",
) -> pd.DataFrame:
    df = df.copy()

    # Define new column for whether found the bug within time limit.
    df["solved"] = df["foundbug"]
    if within:
        df["solved"] &= df[solved_type] < within

    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(["workload", "strategy", "task", "version"], as_index=False).agg(
        {"solved": agg}
    )
    df["total"] = 1
    df = df.groupby(["workload", "strategy", "version"]).sum(numeric_only=False)

    return df[["solved", "total"]]

type Limit = float
type TimeSlicedResults = dict[str, dict[Limit, int]] 

def time_sliced_results(
    case: str,
    data: list[Result],
    limits: list[Limit],
    limit_type: str,
    strategies: list[str] = None,
    agg: Literal["any", "all"] = "all",
):
    data = [d for d in data if d.workload == case]

    if not strategies:
        strategies = sorted(set([d.strategy for d in data]))
    print("Strategies", strategies)
    
    tasks = set([d.task() for d in data])

    avg_data = []

    for task, strategy in product(tasks, strategies):
        task_data = [d for d in data if d.task() == task and d.strategy == strategy]
        if len(task_data) == 0:
            continue

        timed_out = [d for d in task_data if d.time == limits[-1]]
        if len(timed_out) > 0:
            task_data = timed_out
        else:
            avg_result = Result(
                workload=task_data[0].workload,
                discards=sum([d.discards for d in task_data]) / len(task_data),
                foundbug=task_data[0].foundbug,
                strategy=task_data[0].strategy,
                mutant=task_data[0].mutant,
                passed=sum([d.passed for d in task_data]) / len(task_data),
                property=task_data[0].property,
                time=sum([d.time for d in task_data]) / len(task_data),
                counterexample=task_data[0].counterexample,
                process_time=sum([d.process_time for d in task_data]) / len(task_data),
                process_time_monotonic=sum([d.process_time_monotonic for d in task_data]) / len(task_data),
            )
            avg_data.append(avg_result)

    results : TimeSlicedResults = { strategy: { limit: 0 for limit in limits } for strategy in strategies }

    for within in limits:
        within_result = list(filter(lambda r: r.__dict__[limit_type] < within, avg_data))
        for strategy in strategies:
            strategy_result = len(list(filter(lambda r: r.strategy == strategy, within_result)))
            results[strategy][within] = strategy_result - sum([w for w in results[strategy].values()])

    for strategy in strategies:
        results[strategy]["rest"] = len(tasks) - sum([w for w in results[strategy].values()])
    return results


def process_case(results: str, figures: str, case: str) -> TimeSlicedResults:
    results : list[Result] = parse_results(results)

    results : TimeSlicedResults = time_sliced_results(
        data=results,
        limits=[0.1, 1, 10, 60],
        limit_type="time",
        strategies=[
            "BespokeGenerator",
            "SpecificationBasedGenerator",
            "TypeBasedFuzzer",
            "TypeBasedGenerator",
        ],
        case=case
    )

    return results


def plot_data(
    data: pd.DataFrame,
    figures: str,
    limit_type: str,
    prefix: str,
    case: str,
    show_names: bool = False,
):
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
        "RBT": 58,
        "STLC": 20,
    }
    # Create a horizontal stacked bar chart with the following constraints:
    # - y-axis is the strategy
    # - x-axis is the number of tasks solved within a time limit
    # - colors denote the time limit, we create a gradient of colors for each strategy

    def tokey(x):
        return str(x)

    def luma(r, g, b):
        return 0.299 * r + 0.587 * g + 0.114 * b

    suffix = "time" if limit_type == "time" else "inputs"

    vspace = 60
    hspace = 50
    height = 100
    fontsize = 50
    image_width = 1920
    image_height = 8 * height + 7 * vspace + 4 * vspace // 3
    text_size = 600
    total_width = image_width - 2 * hspace

    im = Image.new("RGB", (image_width, image_height), (255, 255, 255))
    draw = ImageDraw.Draw(im)
    font = ImageFont.truetype("SourceCodePro-Medium.ttf", fontsize)

    x_start = hspace
    total_tasks = tasks[case]

    if show_names:
        total_width = total_width - text_size - hspace
        x_start = text_size + hspace
        for i, (strategy, version) in enumerate(product(strategies, ["deeper", "shallow"])):
            draw.text(
                (hspace, (vspace + height / 2 - fontsize / 2) + (vspace + height) * i),
                strategy,
                (0, 0, 0),
                font=font,
            )


    for j, (strategy, version) in enumerate(product(strategies, ["deeper", "shallow"])):
        current_y = vspace + (vspace + height) * j
        if j % 2 == 1:
            current_y -= vspace * 2 / 3

        current_x = x_start
        for i, limit in enumerate(limits):
            color = (
                ImageColor.getrgb(extrapolated_colors[j // 2][i])
                if limit != "rest"
                else (240, 240, 240)
            )
            print(strategy, case, version, limit)
            value = df[(df["strategy"] == strategy) & (df["workload"] == case) & (df["version"] == version)][
                tokey(limit)
            ].values[0]

            print("Value", value, "Limit", limit, "Strategy", strategy, "Case", case, "Version", version)

            width_value = (value / total_tasks) * total_width
            draw.rectangle(
                [
                    (current_x, current_y),
                    (current_x + width_value, current_y + height),
                ],
                fill=color,
            )
            if width_value > fontsize:
                draw.text(
                    (
                        current_x + width_value / 2 - fontsize / 4,
                        current_y + height / 2 - fontsize / 2,
                    ),
                    str(value),
                    (0, 0, 0)
                    if luma(*ImageColor.getrgb(extrapolated_colors[j // 2][i])) > 100
                    else (255, 255, 255),
                    font=font,
                )
            current_x += width_value

    im.save(f"{figures}/{prefix}_{case}_{suffix}.png")



def process_data(results_path: str, images_path: str, case: str) -> pd.DataFrame:

    shallow_results = process_case(results_path, images_path, case)
    deeper_results = process_case(results_path, images_path, case + "Proplang")

    df = pd.DataFrame(columns=["strategy","workload","version"] + [str(limit) for limit in [0.1, 1, 10, 60, "rest"]])

    for strategy, data in shallow_results.items():
        df = df.append({
            "strategy": strategy,
            "workload": case,
            "version": "shallow",
            "0.1": data[0.1],
            "1": data[1],
            "10": data[10],
            "60": data[60],
            "rest": data["rest"]
        }, ignore_index=True)

    for strategy, data in deeper_results.items():
        df = df.append({
            "strategy": strategy,
            "workload": case,
            "version": "deeper",
            "0.1": data[0.1],
            "1": data[1],
            "10": data[10],
            "60": data[60],
            "rest": data["rest"]
        }, ignore_index=True)

    # Save the data to a CSV file.
    df.to_csv(f"{images_path}/workloads.csv", index=False)

    return df


if __name__ == "__main__":
    filepath = pathlib.Path(__file__).resolve().parent
    results_path = f"{filepath}/results"
    images_path = f"{filepath}/figures"
    # analyze(results_path, images_path)

    for case in [
        "BST", 
        "RBT", 
        "STLC"
        ]:
        df = process_data(results_path, images_path, case)
        df = pd.read_csv(f"{images_path}/workloads.csv", index_col=False)
        print(df)
        plot_data(df, images_path, "time", "task_bucket", case, show_names=False)
        plot_data(df, images_path, "time", "task_bucket_named", case, show_names=True)
