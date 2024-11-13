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


def extract(name: str) -> ResultColumns:
    name = name.split(",")

    workload = (name[0],)
    strategy = (name[1],)
    mutant = (name[2],)
    property = (name[3],)

    return ResultColumns(
        workload=workload,
        strategy=strategy,
        mutant=mutant,
        property=property,
    )


def df_insert(df: pd.DataFrame, column: str, value: any) -> pd.DataFrame:
    df.insert(len(df.columns), column, value)
    return df


def parse_results(results: str) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)
    entries = [e for e in entries if e.path.endswith(".json")]

    df = pd.concat(
        [pd.read_json(e.path, orient="records", typ="frame") for e in entries]
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

    # Define new column for whether found the bug within time limit.
    df["solved"] = df["foundbug"]
    if within:
        df["solved"] &= df[solved_type] < within

    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(["workload", "strategy", "task"], as_index=False).agg(
        {"solved": agg}
    )
    df["total"] = 1
    df = df.groupby(["workload", "strategy"]).sum(numeric_only=False)

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

    tasks = df.task.unique()
    total_tasks = len(tasks)

    results = pd.DataFrame(columns=limits, index=strategies, dtype=int, data=0)

    results["rest"] = total_tasks
    print("pre-results", results)
    for within in limits:
        dft = overall_solved(df, agg=agg, within=within, solved_type=limit_type)
        dft = dft.reset_index()
        dft = dft.groupby(["strategy"]).sum(numeric_only=False)
        dft = dft.reset_index()
        dft = dft.set_index("strategy")
        print(dft)
        for sv in strategies:
            # Note: I think the new version of Pandas broke some of this code.
            # Use 1.5.3 for now and come back and fix.
            results.loc[sv].loc[within] = dft.loc[sv]["solved"] - (
                total_tasks - results.loc[sv].loc["rest"]
            )
            results.loc[sv].loc["rest"] = (
                results.loc[sv].loc["rest"] - results.loc[sv].loc[within]
            )
    print("results", results)
    results = results.rename_axis("strategy")
    results = results.reset_index()

    results = results.melt(id_vars=["strategy"], value_vars=limits + ["rest"])

    return results


def process_data(results: str, figures: str, limit_type: str) -> pd.DataFrame:
    df = parse_results(results)

    charter = partial(
        time_sliced_results,
        df=df,
        limits=[0.1, 1, 10, 60],
        limit_type=limit_type,
        strategies=[
            "ProplangBespoke",
            "RackcheckBespoke",
        ],
    )
    bst = charter(case="BST")
    rbt = charter(case="RBT")
    stlc = charter(case="STLC")
    systemf = charter(case="SYSTEMF")
    bst["workload"] = "BST"
    rbt["workload"] = "RBT"
    stlc["workload"] = "STLC"
    systemf["workload"] = "SYSTEMF"
    df = pd.concat([bst, rbt, stlc, systemf])
    print("What")
    print(df)
    # Turn variable/value into column, where each variable has its own column and value is the value of that column.
    df = df.pivot(
        index=["strategy", "workload"], columns="variable", values="value"
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
        # "#DC5F00",  # orange
        # "#243763",  # blue
        "#470938",  # purple
        "#436E4F",  # green
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
        "SYSTEMF": 36,
    }
    # Create a horizontal stacked bar chart with the following constraints:
    # - y-axis is the strategy
    # - x-axis is the number of tasks solved within a time limit
    # - colors denote the time limit, we create a gradient of colors for each strategy

    def tokey(x):
        return str(float(x)) if x != "rest" else "rest"

    def luma(r, g, b):
        return 0.299 * r + 0.587 * g + 0.114 * b

    vspace = 60
    hspace = 50
    height = 100
    fontsize = 50
    image_width = 1920
    image_height = 2 * height + 2 * vspace + 1 * vspace // 3
    text_size = 600
    total_width = image_width - 2 * hspace

    im = Image.new("RGB", (image_width, image_height), (255, 255, 255))
    draw = ImageDraw.Draw(im)
    font = ImageFont.truetype(
        "SourceCodePro-Medium.ttf", fontsize
    )

    x_start = hspace
    total_tasks = tasks[case]

    if show_names:
        total_width = total_width - text_size - hspace
        x_start = text_size + hspace
        for i, strategy in enumerate(strategies):
            draw.text(
                (hspace, (vspace + height / 2 - fontsize / 2) + (vspace + height) * i),
                strategy,
                (0, 0, 0),
                font=font,
            )

    for j, strategy in enumerate(strategies):
        current_y = vspace + (vspace + height) * j
        if j % 2 == 1:
            current_y -= vspace * 2 / 3

        current_x = x_start
        for i, limit in enumerate(limits):
            color = (
                ImageColor.getrgb(extrapolated_colors[j][i])
                if limit != "rest"
                else (240, 240, 240)
            )
            value = df[(df["strategy"] == strategy) & (df["workload"] == case)][
                tokey(limit)
            ].values[0]

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
                    if luma(*ImageColor.getrgb(extrapolated_colors[j][i])) > 100
                    else (255, 255, 255),
                    font=font,
                )
            current_x += width_value

    im.save(f"{figures}/{prefix}_{case}_{limit_type}.png")


if __name__ == "__main__":
    filepath = pathlib.Path(__file__).resolve().parent
    results_path = f"{filepath}/results"
    images_path = f"{filepath}/figures"
    # analyze(results_path, images_path)
    limit_type = "search-time"
    df = process_data(results_path, images_path, limit_type)
    df = pd.read_csv(f"{images_path}/workloads.csv", index_col=False)
    for case in ["BST", "RBT", "STLC", "SYSTEMF"]:
        plot_data(df, images_path, limit_type, "task_bucket", case, show_names=False)
        plot_data(df, images_path, limit_type, "task_bucket_named", case, show_names=True)
