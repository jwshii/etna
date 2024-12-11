from pathlib import Path
from benchtool.BenchTool import BenchTool, Entry
from benchtool.Types import BuildConfig, Config, LogLevel, ReplaceLevel, TrialArgs
from benchtool.Store import S3MetricWriter

import json
import os
import re
import subprocess
import ctypes
import platform
import jinja2
import time


IMPL_DIR = "Src"
STRATEGIES_DIR = "Strategies"
RUNNERS_DIR = "Runners"
SPEC_PATH = "Src/Spec.v"


class Coq(BenchTool):
    def __init__(
        self,
        results: str,
        log_level: LogLevel = LogLevel.INFO,
        replace_level: ReplaceLevel = ReplaceLevel.REPLACE,
    ):
        super().__init__(
            Config(
                start="(*",
                end="*)",
                ext=".v",
                path="workloads/Coq",
                ignore="Lib",
                strategies=STRATEGIES_DIR,
                impl_path=IMPL_DIR,
                spec_path=SPEC_PATH,
            ),
            results,
            log_level,
            replace_level,
        )

    def all_properties(self, workload: Entry) -> set[str]:
        spec = os.path.join(workload.path, SPEC_PATH)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r"prop_[^\s]*")
            matches = regex.findall(contents)
            return list(dict.fromkeys(matches))


    def all_strategies(self, workload: Entry) -> list[Entry]:
        '''
        Assumes that all files in the `config.strategy` folder of `workload`
        that end in `config.ext` are strategies.

        :return: List of strategies in `workload`.
        '''

        strategies = self._get_all_strategy_names(workload.path)

        def mk_entry(s: str) -> Entry:
            return Entry(s, os.path.join(workload.path, self._config.strategies, s))

        return [mk_entry(s) for s in strategies]


    def _build(self, cfg: BuildConfig):
        coq_path = os.path.join(os.getcwd(), "workloads", "Coq")
        print(f"Building {coq_path}")

        if cfg.clean:
            # Cleanup, delete all o, cmi, cmo, cmx, vo, vos, vok, glob, ml, mli, native, out, conf, aux
            self._log(f"Cleaning up {coq_path}", LogLevel.INFO)
            with self._change_dir(coq_path):
                self._shell_command(["./cleanup"])
            self._log(f"Cleaned up {coq_path}", LogLevel.INFO)

        if cfg.build_common:
            common = self.common()
            self._log(f"Building common: {common.name}", LogLevel.INFO)
            with self._change_dir(common.path):
                self._shell_command(["./build", "-i"] + ([] if cfg.clean else ["-c"]))
            self._log(f"Built common: {common.name}", LogLevel.DEBUG)

        if cfg.build_strategies or cfg.build_fuzzers:
            print(f"Building {cfg.path}")
            with self._change_dir(cfg.path):
                print(os.listdir())
                self._shell_command(["./build"] + ([] if cfg.clean else ["-c"]))

        if cfg.build_strategies:
            strategies = self._get_generator_names(cfg.path)
            with self._change_dir(cfg.path):
                for strategy in strategies:
                    self._log(f"Building strategy {strategy}", LogLevel.DEBUG)
                    self._shell_command(["./build_generator.sh", strategy])

        if cfg.build_fuzzers:
            fuzzers = self._get_fuzzer_names(cfg.path)
            with self._change_dir(cfg.path):
                for fuzzer in fuzzers:
                    self._shell_command(["./build_fuzzer.sh", fuzzer])

    def _run_trial(self, workload_path: str, params: TrialArgs):
        self._log(f"Running trial {params}", LogLevel.DEBUG)
        if "Fuzzer" in params.strategy:
            self._run_trial_fuzzer(workload_path, params)
        else:
            self._run_trial_strategy(workload_path, params)

    def _run_trial_fuzzer(self, workload_path: str, params: TrialArgs):
        metric_writer = S3MetricWriter("pldi")
        with self._change_dir(workload_path):
            results = []
            self._log(
                f"Running {params.workload},{params.strategy},{params.mutant},{params.property}",
                LogLevel.INFO,
            )
            for i in range(params.trials):
                if params.seeds:
                    cmd = ["./main_exec", f"./{params.strategy}_exec {params.property} {params.seeds[i]}"]
                else:
                    cmd = ["./main_exec", f"./{params.strategy}_exec {params.property}"]
                try:
                    trial_result = {
                        "workload": params.workload,
                        "discards": None,
                        "foundbug": None,
                        "strategy": params.strategy,
                        "mutant": params.mutant,
                        "passed": None,
                        "property": params.property,
                        "time": None,
                        "counterexample": None,
                    }
                    if os.environ.get("SYNC"):
                        os.system("sudo hwclock -s")
                    start_time = time.time()
                    start_time_monotonic = time.monotonic()
                    process = subprocess.Popen(
                        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
                    )
                    stdout_data, stderr_data = process.communicate(
                        timeout=params.timeout
                    )
                    end_time_monotonic = time.monotonic()
                    end_time = time.time()

                    start = stdout_data.find("[|")
                    end = stdout_data.find("|]")

                    if start == -1 or end == -1:
                        self._log(
                            f"Unexpected! Error Processing {params.strategy} Output:",
                            LogLevel.ERROR,
                        )
                        self._log(f"[{stdout_data}]", LogLevel.ERROR)
                        self._log(f"[{stderr_data}]", LogLevel.ERROR)
                        trial_result["foundbug"] = False
                        trial_result["discards"] = 0
                        trial_result["passed"] = 0
                        trial_result["time"] = -1
                    else:
                        result = stdout_data[start + 2 : end]
                        self._log(f"{params.strategy} Result: {result}", LogLevel.INFO)
                        json_result = json.loads(result, strict=False)
                        trial_result["foundbug"] = (
                            json_result["foundbug"]
                            if "foundbug" in json_result
                            else json_result["result"]
                            in [
                                "failed",
                                "expected_failure",
                            ]
                        )
                        trial_result["discards"] = json_result["discards"]
                        trial_result["passed"] = (
                            json_result["passed"]
                            if "passed" in json_result
                            else json_result["tests"]
                        )
                        trial_result["time"] = json_result["time"]
                        trial_result["process_time"] = end_time - start_time
                        trial_result["process_time_monotonic"] = end_time_monotonic - start_time_monotonic
                        trial_result["start"] = json_result.get("start")
                        trial_result["process_start"] = start_time
                        trial_result["ending"] = json_result.get("ending")
                        trial_result["process_ending"] = end_time
                        trial_result["counterexample"] = json_result.get("counterexample")

                except subprocess.TimeoutExpired as e:
                    print(f"Process Timed Out {process.pid}")
                    os.system(f"pkill -f {params.strategy}_exec")
                    print(f"Process Output: {e}")
                    shm_id = int(
                        e.stdout.decode("utf-8").split("|?SHM ID: ")[1].split("?|")[0]
                    )
                    print(f"Shared Memory ID: {shm_id}")
                    # Libc is platform dependent, so we need to load it dynamically
                    if platform.system() == "Darwin":
                        libc = ctypes.CDLL("/usr/lib/libc.dylib")
                    elif platform.system() == "Linux":
                        libc = ctypes.CDLL("libc.so.6")

                    self._log(
                        f"Releasing Shared Memory: {libc.shmctl(int(shm_id), 0, 0)}",
                        LogLevel.INFO,
                    )
                    self._log(
                        f"Released Shared Memory with ID: {shm_id}", LogLevel.INFO
                    )
                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = params.timeout
                    self._log(f"{params.strategy} Result: Timeout", LogLevel.INFO)

                except subprocess.CalledProcessError as e:
                    self._log(f"Error Running {params.strategy}:", LogLevel.ERROR)
                    self._log(f"[{e.stdout}]", LogLevel.ERROR)
                    self._log(f"[{e.stderr}]", LogLevel.ERROR)
                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = -1

                results.append(trial_result)
                
                if params.short_circuit and trial_result["time"] == params.timeout:
                    break
                elif trial_result["time"] == -1:
                    self._log(f"Exiting due to erroneous trial", LogLevel.ERROR)
                    exit(0)

            metric_writer.write(params.experiment_id, results)
            json.dump(results, open(params.file, "w"), indent=2)

    def _run_trial_strategy(self, workload_path: str, params: TrialArgs):
        metric_writer = S3MetricWriter("pldi")
        with self._change_dir(workload_path):
            results = []
            self._log(
                f"Running {params.workload},{params.strategy},{params.mutant},{params.property}",
                LogLevel.INFO,
            )
            for i in range(params.trials):
                if params.seeds:
                    cmd = [f"./{params.strategy}_test_runner.native", params.property, str(params.seeds[i])]
                else:
                    cmd = [f"./{params.strategy}_test_runner.native", params.property]
                trial_result = {
                    "workload": params.workload,
                    "discards": None,
                    "foundbug": None,
                    "strategy": params.strategy,
                    "mutant": params.mutant,
                    "passed": None,
                    "property": params.property,
                    "time": None,
                    "counterexample": None,
                }
                try:
                    if os.environ.get("SYNC"):
                        os.system("sudo hwclock -s")
                    start_time = time.time()
                    start_time_monotonic = time.monotonic()
                    process = subprocess.Popen(
                        cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True
                    )
            
                    stdout_data, stderr_data = process.communicate(
                        timeout=params.timeout
                    )
                    end_time_monotonic = time.monotonic()
                    end_time = time.time()

                    start = stdout_data.find("[|")
                    end = stdout_data.find("|]")
                    print(f"Result: {stdout_data}")
                    result = stdout_data[start + 2 : end]
                    self._log(f"{params.strategy} Result: {result}", LogLevel.INFO)
                    json_result = json.loads(result, strict=False)
                    trial_result["foundbug"] = (
                        json_result["foundbug"]
                        if "foundbug" in json_result
                        else json_result["result"]
                        in [
                            "failed",
                            "expected_failure",
                        ]
                    )
                    trial_result["discards"] = json_result["discards"]
                    trial_result["passed"] = (
                        json_result["passed"]
                        if "passed" in json_result
                        else json_result["tests"]
                    )
                    trial_result["time"] = json_result["time"]
                    trial_result["process_time"] = end_time - start_time
                    trial_result["process_time_monotonic"] = end_time_monotonic - start_time_monotonic
                    trial_result["start"] = json_result.get("start")
                    trial_result["process_start"] = start_time
                    trial_result["ending"] = json_result.get("ending")
                    trial_result["process_ending"] = end_time
                    trial_result["counterexample"] = json_result.get("counterexample")

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
            json.dump(results, open(params.file, "w"), indent=2)


    def _get_fuzzer_names(self, workload_path):
        return list(
            filter(
                lambda f: f.endswith("Fuzzer"),
                self._get_all_strategy_names(workload_path),
            )
        )

    def _get_generator_names(self, workload_path):
         return list(
            filter(
                lambda f: f.endswith("Generator"),
                self._get_all_strategy_names(workload_path),
            )
        )

    def _get_all_strategy_names(self, workload_path) -> list[str]:
        with open(f"{workload_path}/_CoqProject", "r") as coq_project_file:
            coq_project_file_contents = coq_project_file.read().splitlines()
            generators = []
            for line in coq_project_file_contents:
                if line.startswith(STRATEGIES_DIR):
                    generators.append(line.split("/")[-1][:-2])
    
        return generators

    def _parse_tests_qc(self, s: str) -> tuple[list, str]:
        return self._parse_tests("QuickChick", s)

    def _parse_tests_fc(self, s: str) -> tuple[list, str]:
        return self._parse_tests("FuzzChick", s)

    def _parse_tests_pl(self, s: str) -> tuple[list, str]:
        return self._parse_tests("QuickProp", s)

    def _parse_tests_all(self, s: str) -> tuple[list, str]:
        return (
            self._parse_tests_qc(s) + self._parse_tests_fc(s) + self._parse_tests_pl(s)
        )

    def _parse_tests(self, vernacular: str, s: str) -> tuple[list, str]:
        def compile(s: str) -> re.Pattern:
            return re.compile(s, flags=re.DOTALL)

        start = re.escape(self._config.start)
        end = re.escape(self._config.end)

        test_re = compile(rf"{start}!\s*{vernacular}\s*(\w+).*?{end}")
        test_ls = re.findall(test_re, s)

        return test_ls

    def _generate_test_file(
        self,
        runners_path: str,
        strategy_name: str,
        tests: list[str],
        workload: Entry,
        isPropLang: bool,
        isFuzzer: bool,
    ):
        data = {
            "workload_name": workload.name,
            "strategy_name": strategy_name,
            "type": "QuickProp" if isPropLang else "FuzzChick" if isFuzzer else "QuickChick",
            "fuzzer": isFuzzer,
            "test_names": tests,
        }

        template = Path(self.common().path, "templates", "Runner.v.jinja")

        with open(template, "r") as f:
            template = f.read()

        jinja = jinja2.Environment(loader=jinja2.BaseLoader()).from_string(template)

        with open(os.path.join(runners_path, f"{strategy_name}_test_runner.v"), "w") as f:
            f.write(jinja.render(data))


    def _preprocess(self, workload: Entry) -> None:
        # Relevant Paths
        strategies_path = Path(workload.path, STRATEGIES_DIR)
        runners_path = Path(workload.path, RUNNERS_DIR)

        # Read _CoqProject file
        with open(Path(workload.path, "_CoqProject"), "r") as coq_project_file_reader:
            coq_project_file_contents = coq_project_file_reader.read().splitlines()
            strategies = []
            # Get all strategies
            for line in coq_project_file_contents:
                if line.startswith(STRATEGIES_DIR):
                    strategies.append(line.split("/")[-1][:-2])

        # Generate runner directory if it does not exist
        os.makedirs(runners_path, exist_ok=True)
        # Empty Runner Directory
        for file in os.listdir(runners_path):
            self._log(f"Removing {file}", LogLevel.DEBUG)
            os.remove(os.path.join(runners_path, file))
        
        # Generate and Add Runners for each strategy
        for strategy in strategies:
            with open(
                os.path.join(strategies_path, f"{strategy}.v"), "r"
            ) as strategy_file:
                content = strategy_file.read()
                isPropLang = workload.name.endswith("Proplang") or strategy.startswith("Proplang")
                isFuzzer = strategy.endswith("Fuzzer")
                tests = self._parse_tests_all(content)

                self._generate_test_file(
                    runners_path, strategy, tests, workload, isPropLang, isFuzzer
                )

        # Add runners to the _CoqProject file
        # Remove runners from the _CoqProject file
        with open(Path(workload.path, "_CoqProject"), "w") as coq_project_file_writer:
            for coq_project_file_line in coq_project_file_contents:
                if (
                    not coq_project_file_line.startswith(RUNNERS_DIR)
                    and coq_project_file_line != ""
                ):
                    coq_project_file_writer.write(coq_project_file_line + "\n")
            for strategy in strategies:
                coq_project_file_writer.write(
                    f"{RUNNERS_DIR}/{strategy}_test_runner.v\n"
                )