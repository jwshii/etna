import json
import os

from benchtool.Coq import Coq
from benchtool.Types import TrialConfig, ReplaceLevel
import itertools


def collect(results: str):
    tool = Coq(results=results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        tool._preprocess(workload)
        break