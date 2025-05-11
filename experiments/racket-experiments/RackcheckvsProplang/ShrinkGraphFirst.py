# Read SYSTEMF results
# Create a scatter plot of the results

import json
import os
from pathlib import Path
import random
from turtle import width

from PIL import ImageColor, Image, ImageDraw, ImageFont, ImageFilter
from typing import TypedDict

import math

from numpy import s_
from pyparsing import col


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
    

# Get average shrinkage for ProplangBespoke
print("ProplangBespoke")
total_proplang_size = 0
total_proplang_sh_size = 0
total_rackcheck_size = 0
total_rackcheck_sh_size = 0

rackcheck_shrinked_sizes = []
rackcheck_shrinked_shrinked_sizes = []

proplang_shrinked_sizes = []
proplang_shrinked_shrinked_sizes = []

for (mutant, property), values in shrinkages.items():
    print(mutant, property)
    total_proplang_size += sum(values["ProplangBespoke"]["Size"]) / len(values["ProplangBespoke"]["Size"])
    total_proplang_sh_size += sum(values["ProplangBespoke"]["ShrinkedSize"]) / len(values["ProplangBespoke"]["ShrinkedSize"])


    proplang_zipped = list(zip(values["ProplangBespoke"]["Size"], values["ProplangBespoke"]["ShrinkedSize"]))
    print(len([x[0] for x in list(filter(lambda x: x[1] != -1, proplang_zipped))]))
    proplang_shrinked_sizes += [x[0] for x in list(filter(lambda x: x[1] != -1, proplang_zipped))]
    proplang_shrinked_shrinked_sizes += [x[1] for x in list(filter(lambda x: x[1] != -1, proplang_zipped))]


    total_rackcheck_size += sum(values["RackcheckBespoke"]["Size"]) / len(values["RackcheckBespoke"]["Size"])
    total_rackcheck_sh_size += sum(filter(lambda x: x != -1, values["RackcheckBespoke"]["ShrinkedSize"])) / len(list(filter(lambda x: x != -1, values["RackcheckBespoke"]["ShrinkedSize"])))
    
    rackcheck_zipped = list(zip(values["RackcheckBespoke"]["Size"], values["RackcheckBespoke"]["ShrinkedSize"]))
    rackcheck_shrinked_sizes += [x[0] for x in list(filter(lambda x: x[1] != -1, rackcheck_zipped))]
    rackcheck_shrinked_shrinked_sizes += [x[1] for x in list(filter(lambda x: x[1] != -1, rackcheck_zipped))]
    
print("ProplangBespoke", total_proplang_size/total_proplang_sh_size)
print("RackcheckBespoke", total_rackcheck_size/total_rackcheck_sh_size)
print("")



print("rackcheck", len(rackcheck_shrinked_sizes))
print("rackcheck-shrinked", len(rackcheck_shrinked_shrinked_sizes))

shrinkages_rackcheck = list(map(lambda x: x[0]/x[1], zip(rackcheck_shrinked_sizes, rackcheck_shrinked_shrinked_sizes)))
print(len(shrinkages_rackcheck))
mean = sum(shrinkages_rackcheck)/len(shrinkages_rackcheck)
stdev = (sum(map(lambda x: (x - mean)**2, shrinkages_rackcheck))/len(shrinkages_rackcheck))**0.5

print("rackcheck-shrinkage-mean", mean)
print("rackcheck-shrinkage-stdev", stdev)

print("rackcheck < than 1", len(list(filter(lambda x: x < 1, shrinkages_rackcheck))))
print("rackcheck > than 1", len(list(filter(lambda x: x > 1, shrinkages_rackcheck))))
print("rackcheck = 1", len(list(filter(lambda x: x == 1, shrinkages_rackcheck))))

print("proplang", len(proplang_shrinked_sizes))
print("proplang-shrinked", len(proplang_shrinked_shrinked_sizes))

shrinkages_proplang = list(map(lambda x: x[0]/x[1], zip(proplang_shrinked_sizes, proplang_shrinked_shrinked_sizes)))
mean = sum(shrinkages_proplang)/len(shrinkages_proplang)
stdev = (sum(map(lambda x: (x - mean)**2, shrinkages_proplang))/len(shrinkages_proplang))**0.5

print("proplang-shrinkage-mean", mean)
print("proplang-shrinkage-stdev", stdev)


def linedashed(x0, y0, x1, y1, dashlen=4, ratio=3, draw=None, color=(0,0,0)): 
    dx=x1-x0 # delta x
    dy=y1-y0 # delta y
    # check whether we can avoid sqrt
    if dy==0: vlen=dx
    elif dx==0: vlen=dy
    else: vlen=math.sqrt(dx*dx+dy*dy) # length of line
    xa=dx/vlen # x add for 1px line length
    ya=dy/vlen # y add for 1px line length
    step=dashlen*ratio # step to the next dash
    a0=0
    while a0<vlen:
        a1=a0+dashlen
        if a1>vlen: a1=vlen
        draw.line((x0+xa*a0, y0+ya*a0, x0+xa*a1, y0+ya*a1), fill = color, width = 5)
        a0+=step 



def noise():
    return (0.5 - random.random()) * 10


def draw_scatter_plot(data, output_file):
    width = 1200
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
    # data = dict(sorted(data.items()))
    numcases = len(data)

    print("Max size")

    # print the greatest size
    print(max([max(data[key]["ProplangBespoke"]["Size"]) for key in data]))

    print(numcases)
    for i in range(0, numcases):
        tick_x = padding*3/2 + i * (width - 2 * padding) / numcases + 3*radius
        # Draw uptick
        # draw.line(
        #     (
        #         tick_x,
        #         height - padding,
        #         tick_x,
        #         height - padding + 3*radius,
        #     ),
        #     fill="black",
        #     width=3,
        # )
        # Draw label

        # textwidth = draw.textlength(f"{list(data.items())[i][0][0]}", font=font)

        # draw.text(
        #     (
        #         tick_x - textwidth/2,
        #         height - padding + radius*3,
        #     ),
        #     f"{list(data.items())[i][0][0]}",
        #     fill="black",
        #     font=font,
        # )

        # textwidth = draw.textlength(f"{list(data.items())[i][0][1][10:]}", font=font)
        # draw.text(
        #     (
        #         tick_x - textwidth/2,
        #         height - padding + radius*6,
        #     ),
        #     f"{list(data.items())[i][0][1][10:]}",
        #     fill="black",
        #     font=font,
        # )

    # Draw size ticks on y axis
    textheight = draw.textbbox((0, 0), "0", font=font)[3]
    
    tick_height = (height - 2 * padding) / 35
    for i in range(5, 40, 5):
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

    colors = ("#470938", "#436E4F")
    
    for i, ((mutant, property), values) in enumerate(data.items()):
        # print(mutant, property)
        for j, (strategy, sizes) in enumerate(values.items()):
            for size, shrinked_size in zip(sizes["Size"], sizes["ShrinkedSize"]):
                x = padding + i * (width - 2 * padding) / numcases + padding / 2 + j * padding/2
                size_height = tick_height
                ysize = height - padding - size * size_height
                yshrinked_size = height - padding - shrinked_size * size_height
                # print(mutant, property, size, shrinked_size)

                # draw.circle((x, ysize), radius, fill=colors[j][0])
                # if shrinked_size != -1:
                #     draw.circle((x + 2*radius, yshrinked_size), radius, fill=colors[j][1])
                # else:
                #     draw.circle((x, ysize), radius/5, fill="white")
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
            # print("trendline", x1, y1, x2, y2, colors[0])
            draw.line((x1, y1, x2, y2), fill=colors[j], width=5, joint="curve")

            # print("trendline", x1, y1, x2, y2)

            y1 = tick_y(averages[i][strategy][1])
            y2 = tick_y(averages[i + 1][strategy][1])
            # draw.line((x1, y1, x2, y2), fill=colors[1], width=5, )
            linedashed(x1, y1, x2, y2, draw=draw, color=colors[j])

            # print("trendline", x1, y1, x2, y2)

    img.save(output_file, "PNG", quality=100, subsampling=0)


print("Drawing scatter plot")


# Sort shrinkages with respect to the average shrinkage of `RackCheck`
# print(shrinkages)

def sort_by_rackcheck_shrinked_size(x):
    zipped = zip(x[1]["RackcheckBespoke"]["Size"], x[1]["RackcheckBespoke"]["ShrinkedSize"])
    filtered = list(filter(lambda x: x[1] != -1, zipped))
    
    if len(filtered) == 0:
        return 0
    # print(filtered)
    shrinkage = list(map(lambda x: x[1] - x[0], filtered))
    # print(shrinkage)
    # print(sum(shrinkage)/len(shrinkage))
    return sum(shrinkage)/len(shrinkage)


sorted_shrinkages = sorted(
    shrinkages.items(),
    key=sort_by_rackcheck_shrinked_size,
)
# 
# print("\n\n")
# print(sorted_shrinkages)
sorted_shrinkages = dict(sorted_shrinkages)
# print(sorted_shrinkages)



for i, ((mutant, property), values) in enumerate(sorted_shrinkages.items()):
    # print("wtf")
    # print(mutant, property)
    # zipped = zip(values["RackcheckBespoke"]["Size"], values["RackcheckBespoke"]["ShrinkedSize"])
    # filtered = list(filter(lambda x: x[1] != -1, zipped))
    # print(filtered)

    # print("Rackcheck size", sum(values["RackcheckBespoke"]["Size"])/len(values["RackcheckBespoke"]["Size"]))
    # print("Rackcheck shrinked size", sum(values["RackcheckBespoke"]["ShrinkedSize"])/len(values["RackcheckBespoke"]["ShrinkedSize"]))

    # print("Proplang size", sum(values["ProplangBespoke"]["Size"])/len(values["ProplangBespoke"]["Size"]))
    # print("Proplang shrinked size", sum(values["ProplangBespoke"]["ShrinkedSize"])/len(values["ProplangBespoke"]["ShrinkedSize"]))

    # # print(sum(values["RackcheckBespoke"]["Size"])/len(values["RackcheckBespoke"]["Size"]))
    # # print(values["RackcheckBespoke"]["ShrinkedSize"])
    # # print(sum(values["RackcheckBespoke"]["ShrinkedSize"])/len(values["RackcheckBespoke"]["ShrinkedSize"]))
    # print(sort_by_rackcheck_shrinked_size(((mutant, property), values)))
    # print("\n\n")

    zipped = zip(values["RackcheckBespoke"]["Size"], values["RackcheckBespoke"]["ShrinkedSize"])
    filtered = list(filter(lambda x: x[1] != -1, zipped))
    values["RackcheckBespoke"]["ShrinkedSize"] = list(map(lambda x: x[1], filtered))
    values["RackcheckBespoke"]["Size"] = list(map(lambda x: x[0], filtered))




draw_scatter_plot(
    sorted_shrinkages, Path(__file__).resolve().parent / "figures" / "scatter_plot.png"
)



