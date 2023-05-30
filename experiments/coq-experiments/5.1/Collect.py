import argparse
import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel
import itertools


def collect(results: str, optimize: bool = True):
    tool = Coq(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['BST']:
            continue

        tool._preprocess(workload)

        for variant in tool.all_variants(workload):
            if variant.name != 'insert_1':
                continue

            run_trial = tool.apply_variant(workload, variant, no_base=True)

            for strategy in tool.all_strategies(workload):
                if strategy.name not in ['TypeBasedGenerator']:
                    continue

                for property in tool.all_properties(workload):
                    if property != 'prop_InsertPost':
                        continue

                    cfg = TrialConfig(workload=workload,
                                      strategy=strategy.name,
                                      property="test_" + property,
                                      trials=10,
                                      timeout=60)
                    run_trial(cfg)


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    p.add_argument('--full',
                   help='flag to disable faster version of experiment',
                   action='store_false')
    args = p.parse_args()

    results_path = f'{os.getcwd()}/{args.data}'
    collect(results_path, args.full)
