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
    def skip(self, bench: str, variant: str, method: str, property: str) -> bool:
        pass

    @abstractmethod
    def trials(self, bench: str, method: str) -> int:
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

        for bench in self.tool.all_benches():
            for variant in self.tool.all_variants(bench):
                run_trial = None

                for method in self.tool.all_methods(bench):
                    for property in self.tool.all_properties(bench):
                        if self.skip(bench.name, variant.name, method.name, property):
                            continue

                        name = f'{bench.name},{method.name},{variant.name},{property}'

                        if name in completed:
                            continue

                        if not run_trial:
                            run_trial = self.tool.apply_variant(bench, variant)

                        cfg = TrialConfig(bench=bench,
                                          method=method.name,
                                          property=property,
                                          trials=self.trials(bench.name, method.name),
                                          timeout=self.timeout(),
                                          file=name)
                        run_trial(cfg)

                        self.write_completed(name)