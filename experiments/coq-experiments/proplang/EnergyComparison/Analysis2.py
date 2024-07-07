import pathlib
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial
from itertools import product

from PIL import ImageColor, Image, ImageDraw, ImageFont


@dataclass
class ResultColumns:
    workload: str
    strategy: str
    mutant: str
    property: str
    version: str


versionmap = {
    '0': '1',
    '1': '10',
    '2': '100',
    '3': '1000',
}
def extract(name: str) -> ResultColumns:
    name = name.split(",")

    workload = name[0]
    strategy = name[1]
    version = versionmap[name[2]]
    mutant = name[3]
    property = name[4].split(".")[0]

    return ResultColumns(
        workload=workload,
        strategy=strategy,
        mutant=mutant,
        property=property,
        version=version,
    )


def df_insert(df: pd.DataFrame, column: str, value: any) -> pd.DataFrame:
    df.insert(len(df.columns), column, value)
    return df


def parse_results(results: str) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)
    entries = [e for e in entries if e.path.endswith(".json")]

    df = pd.concat(
        [
            df_insert(
                pd.read_json(e.path, orient="records", typ="frame"),
                "version",
                extract(e.name).version,
            )
            for e in entries
        ]
    )

    df["inputs"] = df.apply(lambda x: x["passed"] + (1 if x["foundbug"] else 0), axis=1)
    df = df.drop(["passed"], axis=1)

    df["task"] = df["workload"] + "," + df["mutant"] + "," + df["property"]
    return df


def overall_solved(
    df: pd.DataFrame,
    agg: Literal["any", "all"],
    within: Optional[float] = None,
    solved_type: str = "time",
) -> pd.DataFrame:
    df = df.copy()
    print(df)
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
    print(df)
    return df[["solved", "total"]]


def time_sliced_results(
    case: str,
    df: pd.DataFrame,
    limits: list[float],
    limit_type: str,
    strategies: list[str] = None,
    agg: Literal["any", "all"] = "all",
):
    df = df[(df["workload"] == case) | (df["workload"] == case + "Proplang")]

    if not strategies:
        strategies = sorted(df.strategy.unique())

    versions = ["1", "10", "100", "1000"]

    tasks = df.task.unique()
    total_tasks = len(tasks)

    def dashmerge(sv):
        return sv[0] + "-" + sv[1]
    
    results = pd.DataFrame(
        columns=limits, index=map(dashmerge, product(strategies, versions)), dtype=int, data=0
    )

    results["rest"] = total_tasks
    print("pre-results", results)
    for within in limits:
        dft = overall_solved(df, agg=agg, within=within, solved_type=limit_type)
        dft = dft.reset_index()
        dft = dft.groupby(["strategy", "version"]).sum(numeric_only=False)
        dft = dft.reset_index()
        dft["strategy-version"] = dft["strategy"] + "-" + dft.version
        dft = dft.set_index("strategy-version")
        print(dft)
        print(dft.index)
        for sv in map(dashmerge, product(strategies, versions)):
            # Note: I think the new version of Pandas broke some of this code.
            # Use 1.5.3 for now and come back and fix.
            results.loc[sv].loc[within] = dft.loc[sv]["solved"] - (
                total_tasks - results.loc[sv].loc["rest"]
            )
            results.loc[sv].loc["rest"] = (
                results.loc[sv].loc["rest"] - results.loc[sv].loc[within]
            )
    print("results", results)
    results = results.rename_axis("strategy-version")
    results = results.reset_index()

    results = results.melt(
        id_vars=["strategy-version"], value_vars=limits + ["rest"]
    )

    results['strategy'] = results['strategy-version'].apply(lambda x: x.split("-")[0])
    results['version'] = results['strategy-version'].apply(lambda x: x.split("-")[1])
    del results['strategy-version']

    return results


def process_data(results: str, figures: str):
    df = parse_results(results)

    charter = partial(
        time_sliced_results,
        df=df,
        limits=[0.1, 1, 10, 60],
        limit_type="time",
        strategies=[
            "TypeBasedFuzzer",
        ],
    )
    bst = charter(case="BST")
    rbt = charter(case="RBT")
    stlc = charter(case="STLC")

    bst["workload"] = "BST"
    rbt["workload"] = "RBT"
    stlc["workload"] = "STLC"

    df = pd.concat([bst, rbt, stlc])
    # Turn variable/value into column, where each variable has its own column and value is the value of that column.
    df = df.pivot(
        index=["strategy", "workload", "version"], columns="variable", values="value"
    ).reset_index()

    df.sort_values(by=["workload", "strategy"], inplace=True)

    df.to_csv(f"{figures}/workloads.csv", index=False)

    return df


def plot_data(
    df: pd.DataFrame,
    figures: str,
    limit_type: str,
    prefix: str,
    case: str,
    show_names: bool = False,
):
    # Generate task bucket charts used in Figure 3.
    limits = [0.1, 1, 10, 60, "rest"]
    colors = [
        # "#000000",  # black
        # "#900D0D",  # red
        "#DC5F00",  # orange
        "#DC5F00",  # orange
        "#DC5F00",  # orange
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
        return str(float(x)) if x != "rest" else "rest"

    def luma(r, g, b):
        return 0.299 * r + 0.587 * g + 0.114 * b

    suffix = "time" if limit_type == "time" else "inputs"

    vspace = 60
    hspace = 50
    height = 100
    fontsize = 50
    image_width = 1920
    image_height = 4 * height + 5 * vspace
    text_size = 600
    total_width = image_width - 2 * hspace

    im = Image.new("RGB", (image_width, image_height), (255, 255, 255))
    draw = ImageDraw.Draw(im)
    font = ImageFont.truetype(
        "/System/Library/Fonts/Supplemental/Arial Bold.ttf", fontsize
    )

    x_start = hspace
    total_tasks = tasks[case]

    if show_names:
        total_width = total_width - text_size - hspace
        x_start = text_size + hspace
        for i, (strategy, version) in enumerate(product(strategies, ["1", "10", "100", "1000"])):
            draw.text(
                (hspace, (vspace + height / 2 - fontsize / 2) + (vspace + height) * i),
                strategy,
                (0, 0, 0),
                font=font,
            )


    for j, (strategy, version) in enumerate(product(strategies, ["1", "10", "100", "1000"])):
        current_y = vspace + (vspace + height) * j

        current_x = x_start
        for i, limit in enumerate(limits):
            color = (
                ImageColor.getrgb(extrapolated_colors[j // 2][i])
                if limit != "rest"
                else (240, 240, 240)
            )
            value = df[(df["strategy"] == strategy) & (df["workload"] == case) & (df["version"] == int(version))][
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
