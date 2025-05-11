# Read `figures/IFCProplang.csv`

import pandas as pd
import pathlib
import json

filepath = pathlib.Path(__file__).resolve().parent

df = pd.read_csv(f"{filepath}/figures/IFCProplang.csv")

df["pool"] = df["strategy"].apply(lambda x: x.split("-")[1])
df["energy"] = df["strategy"].apply(lambda x: x.split("-")[2])

pools = df.groupby(["pool"])

colors = [
    "#000B58",
    "#3D0301",
    "#740938",
    "#4C4B16",
    "#C62E2E",
    "#CB6040",
]

for i, (name, group) in enumerate(pools):
    print(name)
    chart = {
        "numBuckets": 5,
        "chartNames": ["" for _ in range(4)],
        "chartColors": [colors[i] for _ in range(4)],
        "bucketValues": [["0" for _ in range(5)] for _ in range(4)]
    }
    energies = group.groupby(["energy"])
    for i, (_, group) in enumerate(energies):
        # set group index as the row number
        group.reset_index(drop=True, inplace=True)
        for index, row in group.iterrows():
            if row["variable"] != "rest":
                chart["bucketValues"][i][index] = str(row["value"])
            else:
                chart["bucketValues"][i][index] = str(row["value"] - 39)
            chart["chartNames"][i] = row["energy"]
    print(name)
    # save chart to file
    with open(f"{filepath}/figures/{name}.json", "w") as f:
        json.dump(chart, f, indent=2)