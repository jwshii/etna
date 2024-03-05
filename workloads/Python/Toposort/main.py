from __future__ import annotations
from dataclasses import dataclass
import time
import hypothesis
import dataclasses
import json
import sys


@dataclass
class TrialArgs:
    file: str
    trials: int
    workload: str
    strategy: str
    mutant: str
    property: str
    label: str
    timeout: float | None = None
    short_circuit: bool = False

    def to_json(self) -> str:
        return json.dumps(dataclasses.asdict(self))

    @staticmethod
    def from_json(d) -> TrialArgs:
        return TrialArgs(**json.loads(d))


@dataclass
class RunResult:
    workload: str
    strategy: str
    discards: int
    foundbug: bool
    method: str
    mutant: str
    output: str
    passed: int
    property: str
    time: float

    def to_json(self) -> str:
        return json.dumps(dataclasses.asdict(self))

    @staticmethod
    def from_json(d) -> RunResult:
        return RunResult(**json.loads(d))


args = TrialArgs.from_json(sys.argv[1])

for i in range(args.trials):
    # TODO: Handle timeout
    mod = __import__(f"strategies.{args.strategy}", fromlist=[args.property])

    passed = 0
    discards = 0
    foundbug = False

    def increment_count(value):
        global passed
        global discards
        global foundbug
        if value["status"] == "passed":
            passed += 1
        elif value["status"] == "gave_up":
            discards += 1
        elif value["status"] == "failed":
            foundbug = True

    hypothesis.internal.observability.TESTCASE_CALLBACKS.append(  # type: ignore
        increment_count)

    start = time.time()
    try:
        getattr(mod, args.property)()
    except Exception as e:
        print("Exception", e)
        pass
    end = time.time() - start

    hypothesis.internal.observability.TESTCASE_CALLBACKS = [  # type: ignore
    ]

    with open(args.file, "a") as f:
        f.write(
            RunResult(workload=args.workload,
                      strategy=args.strategy,
                      discards=discards,
                      foundbug=foundbug,
                      method=args.strategy,
                      mutant=args.mutant,
                      output="",
                      passed=passed,
                      property=args.property,
                      time=end).to_json() + "\n")
