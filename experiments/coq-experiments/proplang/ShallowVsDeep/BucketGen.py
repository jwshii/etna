import pathlib
from typing import List
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial
from itertools import product

from PIL import ImageColor, Image, ImageDraw, ImageFont

def gen_bucket(
    df: pd.DataFrame,
    figures: str,
    prefix: str,
    sepby: List[str],
    gpby: List[str],
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
    def tokey(x):
        return str(float(x)) if x != "rest" else "rest"

    def luma(r, g, b):
        return 0.299 * r + 0.587 * g + 0.114 * b

    if sepby:
        df = df.groupby(sepby)
    else:
        df = [("all", df)]
    for name, group in df:
        group = group.reset_index()
        group["index"] = group.index
        print(name)
        print(group)

        if gpby:
            subgroups = group.groupby(gpby)
        else:
            subgroups = [("all", group)]

        vspace = 60
        hspace = 50
        height = 100
        fontsize = 50
        image_width = 1920
        image_height = (len(group) * height) + ((len(subgroups) + 1) * vspace) + ((len(group) - len(subgroups)) * vspace // 3)
        total_width = image_width - 2 * hspace

        im = Image.new("RGB", (image_width, image_height), (255, 255, 255))
        draw = ImageDraw.Draw(im)
        font = ImageFont.truetype(
            "/Users/akeles/Programming/projects/PbtBenchmark/coderenderer/Inconsolata/static/Inconsolata-Medium.ttf", fontsize
        )

        current_x = hspace
        current_y = vspace
        x_start = hspace

        group["total"] = group.apply(lambda row: sum(row[tokey(limit)] for limit in limits), axis=1)
        total_tasks = group["total"].max()
        print(total_tasks)

        for _, subgroup in subgroups:
            for (j, (_, row)) in enumerate(subgroup.iterrows()):
                current_x = x_start

                for i, limit in enumerate(limits):
                    color = (
                        ImageColor.getrgb(extrapolated_colors[row['index'] // 2][i])
                        if limit != "rest"
                        else (240, 240, 240)
                    )
                    width_value = (row[tokey(limit)] / total_tasks) * total_width
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
                            str(row[tokey(limit)]),
                            (0, 0, 0)
                            if luma(*ImageColor.getrgb(extrapolated_colors[row['index'] // 2][i])) > 100
                            else (255, 255, 255),
                            font=font,
                        )
                    current_x += width_value
                current_y += height
                if j < len(subgroup) - 1:
                    current_y += vspace // 3
            current_y += vspace
                
        if type(name) is str:
            name = [name]
        suffix = "_".join([str(x) for x in name])
        im.save(f"{figures}/{prefix}_{suffix}.png")


if __name__ == "__main__":
    filepath = pathlib.Path(__file__).resolve().parent
    results_path = f"{filepath}/results"
    images_path = f"{filepath}/figures"
    df = pd.read_csv(f"{images_path}/comp_heap_queue_dqueue.csv", index_col=False)
    gen_bucket(df, images_path, "heap_queue_dequeue", ["workload"], [], show_names=False)

    df = pd.read_csv(f"{images_path}/workloads.csv", index_col=False)
    gen_bucket(df, images_path, "time", ["workload"], ["strategy"], show_names=False)