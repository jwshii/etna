from benchtool.BenchTool import BenchTool, Entry
from benchtool.Types import Config, LogLevel, ReplaceLevel, TrialArgs

import json
import os
import re
import subprocess
import ctypes

IMPL_DIR = 'Src'
METHODS_DIR = 'Methods'
RUNNERS_DIR = 'Runners'
SPEC_PATH = 'Src/Spec.v'

class Coq(BenchTool):
    def __init__(self,
                 results: str,
                 log_level: LogLevel = LogLevel.INFO,
                 replace_level: ReplaceLevel = ReplaceLevel.REPLACE):
        super().__init__(
            Config(start='(*',
                   end='*)',
                   ext='.v',
                   path='bench-suite/Coq',
                   ignore='common',
                   methods=METHODS_DIR,
                   impl_path=IMPL_DIR,
                   spec=SPEC_PATH), results, log_level, replace_level)

    def all_properties(self, bench: Entry) -> set[str]:
        spec = os.path.join(bench.path, SPEC_PATH)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r'prop_[^\s]*')
            matches = regex.findall(contents)
            return list(dict.fromkeys(matches))

    def _build(self, bench_path: str):
        methods = self._get_generator_names(bench_path)
        method_build_commands = map(lambda method: self._get_method_build_command(method), methods)
        fuzzers = self._get_fuzzer_names(bench_path)
        fuzzer_build_commands = map(lambda fuzzer: self._get_fuzzer_build_command(fuzzer), fuzzers)
        with self._change_dir(bench_path):
            self._shell_command(['coq_makefile', '-f', '_CoqProject', '-o', 'Makefile'])
            self._shell_command(['make', 'clean'])
            self._shell_command(['make'])

            for cmd in method_build_commands:
                self._shell_command(cmd.split(" "))
                self._log(f"Built method {cmd}", LogLevel.DEBUG)

            for i, fuzzer_build_command in enumerate(fuzzer_build_commands):
                self._log(f"Built fuzzer {fuzzers[i]}", LogLevel.DEBUG)
                self._log(f"Fuzzer Command 1: {fuzzer_build_command[0]}", LogLevel.DEBUG)
                self._log(f"Fuzzer Command 2: {fuzzer_build_command[1]}", LogLevel.DEBUG)
                self._generate_extended_version_of_fuzzer(fuzzers[i])
                self._shell_command(fuzzer_build_command[2].split(" "))
                self._shell_command(fuzzer_build_command[3].split(" "))
                self._shell_command(fuzzer_build_command[0].split(" "))
                self._shell_command(fuzzer_build_command[1].split(" "))

    def _run_trial(self, bench_path: str, params: TrialArgs):
        self._log(f"Running trial {params}", LogLevel.DEBUG)
        if "Fuzzer" in params.method:
            self._run_trial_fuzzer(bench_path, params)
        else:
            self._run_trial_method(bench_path, params)

    def _run_trial_fuzzer(self, bench_path: str, params: TrialArgs):
        with self._change_dir(bench_path):
            cmd = ['./main_exec', f'./qc_exec {params.property}']
            results = []
            self._log(f"Running {params.method} on {params.bench} with {params.property}", LogLevel.INFO)
            for _ in range(params.trials):
                try:
                    trial_result = {
                        "bench": params.bench,
                        "discards": None,
                        "foundbug": None,
                        "method": params.method,
                        "mutant": params.mutant,
                        "passed": None,
                        "property": params.property,
                        "time": None
                    }
                    result = subprocess.run(cmd,
                                            check=True,
                                            capture_output=True,
                                            text=True,
                                            timeout=params.timeout)

                    start = result.stdout.find("[|")
                    end = result.stdout.find("|]")

                    if start == -1 or end == -1:
                        self._log(f"Unexpected! Error Processing {params.method} Output:", LogLevel.ERROR)
                        self._log(f"[{result.stdout}]", LogLevel.ERROR)
                        self._log(f"[{result.stderr}]", LogLevel.ERROR)
                        trial_result["foundbug"] = False
                        trial_result["discards"] = 0
                        trial_result["passed"] = 0
                        trial_result["time"] = -1
                    else:
                        result = result.stdout[start + 2:end]
                        self._log(f"{params.method} Result: {result}", LogLevel.INFO)
                        json_result = json.loads(result) 
                        trial_result["foundbug"] = json_result["result"] in ["failed", "expected_failure"]
                        trial_result["discards"] = json_result["discards"]
                        trial_result["passed"] = json_result["tests"]
                        trial_result["time"] = float(json_result["time"][:-2]) * 0.001  # ms as string to seconds as float conversion

                except subprocess.TimeoutExpired as e:
                    shm_id = int(e.stdout.decode("utf-8").split("|?SHM ID: ")[1].split("?|")[0])

                    libc = ctypes.CDLL("/usr/lib/libc.dylib")
                    self._log(f"Releasing Shared Memory: {libc.shmctl(int(shm_id), 0, 0)}", LogLevel.INFO)
                    self._log(f"Released Shared Memory with ID: {shm_id}", LogLevel.INFO)
                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = params.timeout
                    self._log(f"{params.method} Result: Timeout", LogLevel.INFO)

                except subprocess.CalledProcessError as e:
                    self._log(f"Error Running {params.method}:", LogLevel.ERROR)
                    self._log(f"[{e.stdout}]", LogLevel.ERROR)
                    self._log(f"[{e.stderr}]", LogLevel.ERROR)
                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = -1

                results.append(trial_result)
                if trial_result['time'] == params.timeout:
                    break
                elif trial_result['time'] == -1:
                    self._log(f"Exiting due to erroneous trial", LogLevel.ERROR)
                    exit(0)

            json.dump(results, open(params.file, 'w'))

    def _run_trial_method(self, bench_path: str, params: TrialArgs):
        with self._change_dir(bench_path):
            cmd = [f"./{params.method}_test_runner.native", params.property]
            results = []
            for _ in range(params.trials):
                trial_result = {
                    "bench": params.bench,
                    "discards": None,
                    "foundbug": None,
                    "method": params.method,
                    "mutant": params.mutant,
                    "passed": None,
                    "property": params.property,
                    "time": None
                }
                try:
                    result = subprocess.run(cmd,
                                            check=True,
                                            capture_output=True,
                                            timeout=params.timeout).stdout.decode('utf-8')
                    start = result.find("[|")
                    end = result.find("|]")
                    result = result[start + 2:end]
                    self._log(f"{params.method} Result: {result}", LogLevel.INFO)
                    json_result = json.loads(result)
                    trial_result["foundbug"] = json_result["result"] in [
                        "failed", "expected_failure"
                    ]
                    trial_result["discards"] = json_result["discards"]
                    trial_result["passed"] = json_result["tests"]
                    trial_result["time"] = float(
                        json_result["time"]
                        [:-2]) * 0.001  # ms as string to seconds as float conversion

                except subprocess.TimeoutExpired:
                    trial_result["foundbug"] = False
                    trial_result["discards"] = 0
                    trial_result["passed"] = 0
                    trial_result["time"] = params.timeout
                    self._log(f"{params.method} Result: Timeout", LogLevel.INFO)
                results.append(trial_result)

            json.dump(results, open(params.file, 'w'))


    def _generate_extended_version_of_fuzzer(self, fuzzer: str):
        fuzzer_path = f"./{fuzzer}_test_runner.ml"
        extended_fuzzer_path = f"./{fuzzer}_test_runner_ext.ml"
        stub_path = f"{os.environ['OPAM_SWITCH_PREFIX']}/lib/coq/user-contrib/QuickChick/Stub.ml"
        f = open(extended_fuzzer_path, "w+")
        with open(stub_path, "r") as stub:
            f.write(stub.read())
            f.write("\n\n(* -----(Stub Ends)----- *)\n\n")
        with open(fuzzer_path, "r") as fuzzer_file:
            f.write(fuzzer_file.read())
        f.close()

    def _get_executable_method_names(self, bench_path):
        methods_path = f"{bench_path}/{METHODS_DIR}"
        methods = self._get_method_names(methods_path)
        executables = list(map(lambda method: f"{method}_test_runner.native", methods))
        return executables

    def _get_method_build_command(self, method: str) -> str:
        self._log(f"Building method: {method}", LogLevel.INFO)
        return f"ocamlfind ocamlopt -linkpkg -package zarith -package unix -rectypes {method}_test_runner.mli {method}_test_runner.ml -o {method}_test_runner.native"

    def _get_fuzzer_build_command(self, fuzzer: str) -> str:
        qc_path = os.environ['OPAM_SWITCH_PREFIX'] + '/lib/coq/user-contrib/QuickChick'
        fuzzer_build_command = (
        f"ocamlfind ocamlopt -ccopt -Wno-error=implicit-function-declaration -afl-instrument -linkpkg -package unix -package str -package coq-core.plugins.extraction -package coq-quickchick.plugin -thread -rectypes -w a -o ./qc_exec ./{fuzzer}_test_runner_ext.ml {qc_path}/SHM.c",
        f"ocamlfind ocamlopt -ccopt -Wno-error=implicit-function-declaration -linkpkg -package unix -package str -rectypes -w a -I . -o main_exec {qc_path}/Main.ml {qc_path}/SHM.c",
        f"{qc_path}/cmdprefix.pl {fuzzer}_test_runner_ext.ml",
        f"{qc_path}/cmdsuffix.pl {fuzzer}_test_runner_ext.ml"
        )

        return fuzzer_build_command

    def _get_fuzzer_names(self, bench_path):
        fuzzers = list(filter(lambda f: f.endswith("Fuzzer"), self._get_all_method_names(f"{bench_path}/{METHODS_DIR}")))
        return fuzzers

    def _get_generator_names(self, bench_path):
        generators = list(filter(lambda f: f.endswith("Generator"), self._get_all_method_names(f"{bench_path}/{METHODS_DIR}")))
        return generators

    def _get_all_method_names(self, methods_path) -> list[str]:
        methods = []
        for method in os.listdir(methods_path):
            f = os.path.join(methods_path, method)
            if os.path.isfile(f) and f.endswith(".v"):
                methods.append(method[:-2])
        return methods

    def _parse_tests_qc(self, s: str) -> tuple[list, str]:
        return self._parse_tests("QuickChick", s)

    def _parse_tests_fc(self, s: str) -> tuple[list, str]:
        return self._parse_tests("FuzzChick", s)

    def _parse_tests(self, vernacular: str, s: str) -> tuple[list, str]:
        def compile(s: str) -> re.Pattern:
            return re.compile(s, flags=re.DOTALL)

        start = re.escape(self._config.start)
        end = re.escape(self._config.end)

        test_re = compile(fr"{start}!\s*{vernacular}\s*(\w+).*?{end}")
        test_ls = re.findall(test_re, s)
        return test_ls

    def _generate_test_file_qc(self, runners_path: str, method_name: str, tests: list[str], bench: Entry):
        bench_name = bench.name
        file_name = f"{method_name}_test_runner.v"
        method_import = f"From {bench_name} Require Import {method_name}.\n"
        library_import = "From QuickChick Require Import QuickChick.\n"
        set_warnings = 'Set Warnings "-extraction-opaque-accessed,-extraction".\n'
        size_axiom = 'Axiom num_tests : nat. Extract Constant num_tests => "max_int".\n'
        test_string_template = "Definition qctest_<test-name> := (fun _ : unit => print_extracted_coq_string (\"[|{\" ++ show (withTime(fun tt => (quickCheckWith (updMaxDiscard (updMaxSuccess (updAnalysis stdArgs true) num_tests) num_tests) <test-name>))) ++ \"}|]\")).\n"
        test_map = f"""

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".
Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    {'; '.join([f'(""{test_name}"", qctest_{test_name})' for test_name in tests])}
  ] in
  let test = List.assoc test_name test_map in
  test ()


let () =
  Sys.argv.(1) |> qctest_map
".

"""
        extraction_string_template = f'Extraction "{method_name}_test_runner.ml" <test-names> qctest_map.\n'

        with open(os.path.join(runners_path, file_name), "w") as runner_file:
            runner_file.write(method_import)
            runner_file.write(library_import)
            runner_file.write(set_warnings)
            runner_file.write(size_axiom)
            for test in tests:
                test_string = test_string_template.replace("<test-name>", test)
                runner_file.write(test_string)
            test_names = " ".join(list(map(lambda test: f"qctest_{test}", tests)))
            runner_file.write(test_map)
            extraction_string = extraction_string_template.replace("<test-names>", test_names)
            runner_file.write(extraction_string)

    def _generate_test_file_fc(self, runners_path: str, fuzzer_name: str, tests: list[str], bench: Entry):
        bench_name = bench.name
        file_name = f"{fuzzer_name}_test_runner.v"
        method_import = f"From {bench_name} Require Import {fuzzer_name}.\n"
        library_import = "From QuickChick Require Import QuickChick.\n"
        set_warnings = 'Set Warnings "-extraction-opaque-accessed,-extraction".\n'
        test_string_template = "Definition qctest_<test-name> := (fun _ : unit => print_extracted_coq_string (\"[|{\" ++ show (withTime (fun tt => (<test-name>_fuzzer tt))) ++ \"}|]\")).\n"
        test_map = f"""

Parameter OCamlString : Type.
Extract Constant OCamlString => "string".
Axiom qctest_map : OCamlString -> unit.
Extract Constant qctest_map => "
fun test_name ->
  let test_map = [
    {'; '.join([f'(""{test_name}"", qctest_{test_name})' for test_name in tests])}
  ] in
  let test = List.assoc test_name test_map in
  test ()


let () = 
  Printf.printf ""Entering main of qc_exec\\n""; flush stdout;
  setup_shm_aux ();
  Sys.argv.(1) |> qctest_map ; flush stdout;
".

"""
        extraction_string_template = f'Extraction "{fuzzer_name}_test_runner.ml" <test-names> qctest_map.'

        with open(os.path.join(runners_path, file_name), "w") as runner_file:
            runner_file.write(method_import)
            runner_file.write(library_import)
            runner_file.write(set_warnings)
            for test in tests:
                test_string = test_string_template.replace("<test-name>", test)
                runner_file.write(test_string)
            test_names = " ".join(list(map(lambda test: f"qctest_{test}", tests)))
            runner_file.write(test_map)
            extraction_string = extraction_string_template.replace("<test-names>", test_names)
            runner_file.write(extraction_string)

    def _preprocess(self, bench: Entry) -> None:
        # Relevant Paths
        methods_path = f"{bench.path}/{METHODS_DIR}/"
        runners_path = f"{bench.path}/{RUNNERS_DIR}/"
        # Generate runner files
        generators = self._get_generator_names(bench.path)
        fuzzers = self._get_fuzzer_names(bench.path)
        # Empty Runner Directory
        self._shell_command(['rm', f"{runners_path}*"])
        # Generate and Add Runners for each method
        for method in generators:
            with open(os.path.join(methods_path, f"{method}.v"), "r") as method_file:
                content = method_file.read()
                tests = self._parse_tests_qc(content)
                self._generate_test_file_qc(runners_path, method, tests, bench)
        # Generate and Add Runners for each fuzzer
        for fuzzer in fuzzers:
            with open(os.path.join(methods_path, f"{fuzzer}.v"), "r") as method_file:
                content = method_file.read()
                tests = self._parse_tests_fc(content)
                self._generate_test_file_fc(runners_path, fuzzer, tests, bench)
        # Add runners to the _CoqProject file
        with open(f"{bench.path}/_CoqProject", "r") as coq_project_file_reader:
            coq_project_file_contents = coq_project_file_reader.read().splitlines()

        with open(f"{bench.path}/_CoqProject", "w") as coq_project_file_writer:
            for coq_project_file_line in coq_project_file_contents:
                if not coq_project_file_line.startswith(RUNNERS_DIR) and coq_project_file_line != "":
                    coq_project_file_writer.write(coq_project_file_line + "\n")

            for method in generators + fuzzers:
                coq_project_file_writer.write(f"{RUNNERS_DIR}/{method}_test_runner.v\n")
