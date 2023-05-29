from abc import ABC, abstractmethod
import os
from benchtool.BenchTool import BenchTool
from benchtool.Types import TrialConfig

# This is one way we're trying out to express an experiment,
# though not all experiments (e.g. the size experiment) will
# fit this model. We should refine this further.

class Experiment(ABC):
    tool: BenchTool
    scratch: str

    def __init__(self, tool):
        self.tool = tool
        self.scratch = os.path.join(self.tool.results, 'completed.txt')

    @abstractmethod
    def skip(self, workload: str, variant: str, strategy: str, property: str) -> bool:
        pass

    @abstractmethod
    def trials(self, workload: str, strategy: str) -> int:
        pass

    @abstractmethod
    def timeout(self) -> float:
        pass

    def read_completed(self) -> set[str]:
        completed = set()
        if os.path.isfile(self.scratch):
            with open(self.scratch, 'r') as f:
                for line in f.readlines():
                    if line:
                        completed.add(line.strip())
        return completed

    def write_completed(self, name: str) -> set[str]:
        with open(self.scratch, 'a') as f:
            f.write(name + '\n')

    def run(self):
        completed = self.read_completed()

        for workload in self.tool.all_workloads():
            for variant in self.tool.all_variants(workload):
                run_trial = None

                for strategy in self.tool.all_strategies(workload):
                    for property in self.tool.all_properties(workload):
                        if self.skip(workload.name, variant.name, strategy.name, property):
                            continue

                        name = f'{workload.name},{strategy.name},{variant.name},{property}'

                        if name in completed:
                            continue

                        if not run_trial:
                            run_trial = self.tool.apply_variant(workload, variant)

                        cfg = TrialConfig(workload=workload,
                                          strategy=strategy.name,
                                          property=property,
                                          trials=self.trials(workload.name, strategy.name),
                                          timeout=self.timeout(),
                                          file=name)
                        run_trial(cfg)

                        self.write_completed(name)