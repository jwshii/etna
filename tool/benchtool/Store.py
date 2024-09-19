from dataclasses import dataclass
import subprocess
from typing import Callable, List, Tuple
from pathlib import Path
from abc import ABC, abstractmethod

import json


@dataclass
class Workload:
    name: str
    language: str


@dataclass
class ExperimentConfig:
    name: str
    description: str
    workloads: List[Workload]
    path: Path


@dataclass
class ExperimentSnapshot:
    experiment: str
    etna: str
    scripts: List[Tuple[str, str]]
    workloads: List[Tuple[Workload, str]]


@dataclass
class Experiment:
    name: str
    id: str
    description: str
    path: Path
    snapshot: ExperimentSnapshot


class MetricWriter(ABC):
    @abstractmethod
    def write(self, experiment_id: str, metrics: dict):
        pass


class JsonFileMetricWriter(MetricWriter):
    def __init__(self, path: Path):
        self.path = path

    def write(self, experiment_id: str, metrics: dict):
        with open(self.path / f"{experiment_id}.json", "w") as f:
            json.dump(metrics, f)


class EtnaCLIStoreWriter(MetricWriter):
    def write(self, experiment_id: str, metrics: dict):
        cmd = ["etna-cli", "store", "write", experiment_id, json.dumps(metrics)]
        print(f"Writing metrics metrics to etna-cli: {metrics}")
        process = subprocess.Popen(
            cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
        )

        stdout, stderr = process.communicate()

        if process.returncode != 0:
            raise Exception(f"Failed to write metrics: {stderr}")
        
        return stdout
