import os
import re
import json
from typing import TypeVar, Callable, Optional, Tuple
from benchtool.BenchTool import BenchTool
from benchtool.Types import Config, Entry, LogLevel, Modified, Original, ReplaceLevel, TrialArgs, Variant

A = TypeVar("A")


def find(f: Callable[[A], bool], l: list[A]) -> Optional[A]:
    for x in l:
        if f(x):
            return x
    return None


def findi(f: Callable[[A], bool], l: list[A]) -> Optional[Tuple[int, A]]:
    for i, x in enumerate(l):
        if f(x):
            return (i, x)
    return None


def extract_variants(workload: Entry) -> list[Variant]:
    fname = os.path.join(workload.path, "impl.py")
    with open(fname, "r") as impl_file:
        contents = impl_file.readlines()
        mutants: list[Tuple[int, str]] = []
        for i, line in enumerate(contents):
            base_tag = re.match(r"\s*#etna_base\s+([^\s]+)", line)
            if base_tag:
                mutants.append((i, base_tag.group(1)))

        variants = []
        for (base_start, mutant_name) in mutants:
            mutant_start_pair = findi((lambda line: re.match(
                fr"\s*#etna_mutant\s+{mutant_name}", line) is not None),
                                      contents)
            mutant_end_pair = findi((lambda line: re.match(
                fr"\s*#etna_mutant_end\s+{mutant_name}", line) is not None),
                                    contents)
            if mutant_start_pair is None or mutant_end_pair is None:
                raise Exception(f"Missing start or end for {mutant_name}")
            mutant_start, _ = mutant_start_pair
            mutant_end, _ = mutant_end_pair
            new_body = "".join(contents[:base_start] + list(
                map(lambda x: x[1:], contents[mutant_start + 1:mutant_end])) +
                               contents[mutant_end + 1:])
            variants.append(
                Modified(filename=fname, body=new_body, name=mutant_name))
        variants.append(Original(filename=fname, body="".join(contents)))
        return variants


class Python(BenchTool):

    def __init__(self,
                 results: str,
                 log_level: LogLevel = LogLevel.INFO,
                 replace_level: ReplaceLevel = ReplaceLevel.REPLACE):
        super().__init__(
            Config(start="",
                   end="",
                   ext='.py',
                   path='workloads/Python',
                   ignore='common',
                   strategies='strategies',
                   impl_path='.',
                   spec_path='spec.py'), results, log_level, replace_level)

    def all_properties(self, workload: Entry) -> set[str]:
        spec = os.path.join(workload.path, self._config.spec_path)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r'def (test_[^\s(]*)')
            matches = regex.findall(contents)
            return set(list(dict.fromkeys(matches)))

    def all_variants(self, workload: Entry) -> list[Variant]:
        return extract_variants(workload)

    def _build(self, workload_path: str):
        pass

    def _run_trial(self, workload_path: str, params: TrialArgs):

        def reformat():
            # Get JSONs into a format that
            # makes it easier to parse later on.
            with open(params.file) as f:
                results = [json.loads(line) for line in f]
            open('file.txt', 'w').close()
            json.dump(results, open(params.file, 'w'))

        with self._change_dir(workload_path):
            for _ in range(params.trials):
                # Re-run per trial to avoid caching problems.
                p = params.to_json()
                self._shell_command(['python', 'main.py', p])

                # if params.short_circuit:
                #     # Optimization: terminate as soon as a task is not solved
                #     # instead of running for the full umber of trials.
                #     with open(params.file) as f:
                #         if '"foundbug":false' in f.read():
                #             reformat()
                #             return

        reformat()

    def _preprocess(self, workload: Entry) -> None:
        pass
