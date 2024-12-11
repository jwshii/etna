# Read SYSTEMF results
# Create a scatter plot of the results

import json
import os
from pathlib import Path
import random

from PIL import ImageColor, Image, ImageDraw, ImageFont, ImageFilter
from typing import TypedDict


results_path = Path(__file__).resolve().parent / "results"

shrinkages = {}

for file in filter(lambda f: f.startswith("SYSTEMF"), os.listdir(results_path)):
    print("Working on ", file)
    jsonfile = results_path / file
    contents = json.load(open(jsonfile))

    mutant = contents[0]["mutant"]
    property = contents[0]["property"]
    strategy = contents[0]["strategy"]

    if shrinkages.get((mutant, property)) is None:
        shrinkages[(mutant, property)] = {
            "ProplangBespoke": {"Size": [], "ShrinkedSize": []},
            "RackcheckBespoke": {"Size": [], "ShrinkedSize": []},
        }

    for i, item in enumerate(contents):
        size = item["size"]
        shrinked_size = item["shrinked-size"]

        shrinkages[(mutant, property)][strategy]["Size"].append(size)
        shrinkages[(mutant, property)][strategy]["ShrinkedSize"].append(shrinked_size)


def noise():
    return (0.5 - random.random()) * 10


def draw_scatter_plot(data, output_file):
    width = 4000
    height = 800
    radius = 5
    padding = 50

    img = Image.new("RGB", (width, height), "white")
    draw = ImageDraw.Draw(img)

    font = ImageFont.load_default()

    # Draw axis
    draw.line((padding, height - padding, padding, padding), fill="black", width=5)
    draw.line(
        (padding, height - padding, width - padding, height - padding),
        fill="black",
        width=5,
    )

    # Draw ticks
    data = dict(sorted(data.items()))
    numcases = len(data)

    # print the greatest size
    print(max([max(data[key]["ProplangBespoke"]["Size"]) for key in data]))

    print(numcases)
    for i in range(0, numcases):
        tick_x = padding*3/2 + i * (width - 2 * padding) / numcases + 3*radius
        # Draw uptick
        draw.line(
            (
                tick_x,
                height - padding,
                tick_x,
                height - padding + 3*radius,
            ),
            fill="black",
            width=3,
        )
        # Draw label

        textwidth = draw.textlength(f"{list(data.items())[i][0][0]}", font=font)

        draw.text(
            (
                tick_x - textwidth/2,
                height - padding + radius*3,
            ),
            f"{list(data.items())[i][0][0]}",
            fill="black",
            font=font,
        )

        textwidth = draw.textlength(f"{list(data.items())[i][0][1][10:]}", font=font)
        draw.text(
            (
                tick_x - textwidth/2,
                height - padding + radius*6,
            ),
            f"{list(data.items())[i][0][1][10:]}",
            fill="black",
            font=font,
        )

    # Draw size ticks on y axis
    textheight = draw.textbbox((0, 0), "0", font=font)[3]
    
    tick_height = (height - 2 * padding) / 50
    for i in range(5, 50, 5):
        tick_y = height - padding - i * tick_height
        draw.line(
            (padding, tick_y, padding - 3*radius, tick_y),
            fill="black",
            width=3,
        )
        draw.text(
            (
                padding - 6*radius,
                tick_y - textheight/2,
            ),
            str(i),
            fill="black",
            font=font,
        )

    colors = [
        ("purple", "rgb(212, 0, 212)"),
        ("green", "lightgreen"),
    ]
    for i, ((mutant, property), values) in enumerate(data.items()):
        for j, (strategy, sizes) in enumerate(values.items()):
            for size, shrinked_size in zip(sizes["Size"], sizes["ShrinkedSize"]):
                x = padding + i * (width - 2 * padding) / numcases + padding / 2 + j * padding/2
                size_height = tick_height
                ysize = height - padding - size * size_height
                yshrinked_size = height - padding - shrinked_size * size_height
                # print(mutant, property, size, shrinked_size)

                draw.circle((x, ysize), radius, fill=colors[j][0])
                if shrinked_size != -1:
                    draw.circle((x + 2*radius, yshrinked_size), radius, fill=colors[j][1])
                else:
                    draw.circle((x, ysize), radius/5, fill="white")
    # Create a trend line using the average of the shrinkages
    averages = []
    for i, ((mutant, property), values) in enumerate(data.items()):
        avgs = {}
        for j, (strategy, sizes) in enumerate(values.items()):
            sizeavg = sum(sizes["Size"]) / len(sizes["Size"])
            sizes["ShrinkedSize"] = list(
                filter(lambda x: x != -1, sizes["ShrinkedSize"])
            )
            shrinked_sizeavg = sum(sizes["ShrinkedSize"]) / len(sizes["ShrinkedSize"])
            avgs[strategy] = (sizeavg, shrinked_sizeavg)
        averages.append(avgs)

    for i in range(0, len(averages) - 1):
        for j, strategy in enumerate(averages[i].keys()):

            def tick_x(i):
                return padding*3/2 + i * (width - 2 * padding) / numcases + 3*radius

            def tick_y(i):
                return height - padding - i * tick_height
            
            x1 = tick_x(i)
            x2 = tick_x(i + 1)
            y1 = tick_y(averages[i][strategy][0])
            y2 = tick_y(averages[i + 1][strategy][0])
            draw.line((x1, y1, x2, y2), fill=colors[j][0], width=5, joint="curve")

            y1 = tick_y(averages[i][strategy][1])
            y2 = tick_y(averages[i + 1][strategy][1])
            draw.line((x1, y1, x2, y2), fill=colors[j][1], width=5, joint="curve")

    img.save(output_file, "PNG", quality=100, subsampling=0)


draw_scatter_plot(
    shrinkages, Path(__file__).resolve().parent / "figures" / "scatter_plot.png"
)
