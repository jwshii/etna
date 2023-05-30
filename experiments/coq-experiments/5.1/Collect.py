import argparse
import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel
import itertools


def collect(results: str, optimize: bool = True):
    tool = Coq(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        tool._preprocess(workload)
        break


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--full',
                   help='flag to disable faster version of experiment',
                   action='store_false')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path, args.full)
