import os
import re
import json
import subprocess
from benchtool.BenchTool import BenchTool
from benchtool.Store import EtnaCLIStoreWriter, S3MetricWriter
from benchtool.Types import BuildConfig, Config, Entry, LogLevel, ReplaceLevel, TrialArgs

IMPL_DIR = "src"
STRATEGIES_DIR = "Strategies"


class Racket(BenchTool):
    def __init__(
        self,
        results: str,
        log_level: LogLevel = LogLevel.INFO,
        replace_level: ReplaceLevel = ReplaceLevel.REPLACE,
        log_file: str | None = None,
    ):
        super().__init__(
            Config(
                start="#|",  # Racket multi-line comment syntax
                end="|#",
                ext=".rkt",
                path="workloads/Racket",
                ignore="util",  # This contains the library code
                strategies=STRATEGIES_DIR,
                impl_path=IMPL_DIR,
                spec_path="src/Spec.rkt",
            ),
            results,
            log_level,
            replace_level,
            log_file,
        )

    def all_properties(self, workload: Entry) -> set[str]:
        spec = os.path.join(workload.path, self._config.spec_path)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r"prop_[^\s]*")
            matches = regex.findall(contents)
            return list(dict.fromkeys(matches))

    def _build(self, cfg: BuildConfig):
        with self._change_dir(cfg.path):
            self._shell_command(["raco", "exe", "main.rkt"])

    def _run_trial(self, workload_path: str, params: TrialArgs):
        # metric_writer = EtnaCLIStoreWriter()
        metric_writer = S3MetricWriter("pldi")
        with self._change_dir(workload_path):
            cmd = ["./main", params.property, params.strategy]
            results = []
            self._log(
                f"Running {params.workload},{params.strategy},{params.mutant},{params.property}",
                LogLevel.INFO,
            )
            for _ in range(params.trials):
                trial_result = {
                    "workload": params.workload,
                    "discards": None,
                    "foundbug": None,
                    "strategy": params.strategy,
                    "mutant": params.mutant,
                    "passed": None,
                    "property": params.property,
                    "time": None,
                }
                try:
                    process = subprocess.Popen(
                        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
                    )

                    stdout_data, stderr_data = process.communicate(
                        timeout=params.timeout
                    )
                    datasource = stdout_data if len(stdout_data) > 0 else stderr_data
                    start = datasource.find("[|")
                    end = datasource.find("|]")
                    result = datasource[start + 2 : end]
                    self._log(f"{params.strategy} Result: {result}", LogLevel.INFO)
                    try:
                        json_result = json.loads(result)
                        trial_result["foundbug"] = json_result["foundbug"]
                        trial_result["discards"] = 0  # todo: fix this
                        trial_result["passed"] = json_result["passed"]
                        if "time" in json_result:
                            trial_result["time"] = (
                                json_result["time"] * 0.001
                            )  # ms as string to seconds as float conversion
                        else:
                            trial_result["time"] = (json_result["search-time"] + json_result["shrink-time"]) * 0.001
                            trial_result["search-time"] = json_result["search-time"] * 0.001
                            trial_result["shrink-time"] = json_result["shrink-time"] * 0.001

                        trial_result["counterexample"] = json_result.get("counterexample", None)
                        trial_result["shrinked-counterexample"] = json_result.get("shrinked-counterexample", None)
                        
                    except json.JSONDecodeError:
                        trial_result["foundbug"] = False
                        trial_result["discards"] = -1
                        trial_result["passed"] = -1
                        trial_result["time"] = params.timeout
                        self._log(f"({params.strategy}) Error: {result}", LogLevel.ERROR)

                except subprocess.TimeoutExpired:
                    process.kill()

                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = params.timeout
                    self._log(f"{params.strategy} Result: Timeout", LogLevel.INFO)

                results.append(trial_result)
                

                if params.short_circuit and trial_result["time"] == params.timeout:
                    break

            metric_writer.write(params.experiment_id, results)
            json.dump(results, open(params.file, "w"))

    def _preprocess(self, workload: Entry) -> None:
        pass
