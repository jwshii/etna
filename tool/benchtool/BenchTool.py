import argparse
import os
from re import I
import shutil as sh
import subprocess
import sys
import tempfile
from abc import ABC, abstractmethod
from typing import Callable, Optional

from numpy import var

from benchtool.Mutant import Parser
from benchtool.Types import (Config, Entry, LogLevel, ReplaceLevel, TrialArgs, TrialConfig, Variant)
from benchtool.Util import ChangeDir, print_log, scandir_filter, recursive_scandir_filter


class BenchTool(ABC):
    results: str
    __temp: str
    _log_level: LogLevel = LogLevel.INFO
    _replace_level: ReplaceLevel = ReplaceLevel.REPLACE
    _config: Config
    __variant: Optional[Variant]

    def __init__(self,
                 config: Config,
                 results: str,
                 log_level: LogLevel = LogLevel.INFO,
                 replace_level: ReplaceLevel = ReplaceLevel.REPLACE):
        self.results = results
        self._config = config
        self._log_level = log_level
        self._replace_level = replace_level
        self.__temp = tempfile.mkdtemp()

        try:
            os.mkdir(results)
        except FileExistsError:
            self._log(f'Results directory {results} already exists.', LogLevel.WARNING)

        sh.copytree(self._config.path, os.path.join(self.__temp, self._config.path))

    def parse_args(self) -> tuple[bool, bool]:
        '''
        Parses command-line arguments passed in via `--mode`.

        :return: Pair of (whether to run benchmarks, whether to plot data).
        '''

        p = argparse.ArgumentParser()
        p.add_argument('--mode', default='both', choices=['bench', 'plot', 'both'])
        args = p.parse_args()

        return (args.mode != 'plot', args.mode != 'bench')

    def set_log_level(self, log_level: LogLevel):
        ''' Sets log level.'''
        self._log_level = log_level

    def all_benches(self) -> list[Entry]:
        '''
        Assumes that all top-level directories in `config.path`
        other than `config.ignore` are benchmarks.

        :return: List of benchmarks.
        '''

        def is_bench(entry) -> bool:
            return os.path.isdir(entry) and entry.name != self._config.ignore

        return scandir_filter(self._config.path, is_bench)

    def all_variants(self, bench: Entry) -> list[Variant]:
        '''
        Assumes that all variants are in `config.impl` file.

        :return: List of variants in `bench`.
        '''

        p = Parser(self._config)
        return p.extract(p.parse(bench))

    def apply_variant(self, bench: Entry, variant: Variant, no_base=False) -> Callable[[TrialConfig], None]:
        '''
        Overwrites `config.impl` file for `bench` with contents
        of the provided `variant`.

        :return: A function that can be used to run a trial.
        '''

        if no_base and variant.name == 'base':
            return lambda _: None

        with self._change_dir(self.__temp):
            self._log(f'Applying variant {variant}', LogLevel.DEBUG)
            self.__apply_variant_in_impl(bench, variant)

            self._log(f'Building with mutant: {variant.name}', LogLevel.INFO)
            self._build(bench.path)

        self.__variant = variant

        return self.__trial

    def all_methods(self, bench: Entry) -> list[Entry]:
        '''
        Assumes that all files in the `config.method` folder of `bench`
        that end in `config.ext` are methods.

        :return: List of methods in `bench`.
        '''

        def is_method(entry) -> bool:
            return os.path.isfile(entry) and entry.name.endswith(self._config.ext)

        methods = os.path.join(bench.path, self._config.methods)
        entries = recursive_scandir_filter(methods, is_method)

        def get_base(e: Entry) -> Entry:
            # Remove file extension to get base name.
            return Entry(e.name[:-len(self._config.ext)], e.path)

        return [get_base(e) for e in entries]

    @abstractmethod
    def all_properties(self, bench: Entry) -> list[Entry]:
        pass

    @abstractmethod
    def _build(self, bench_path: str):
        '''
        Takes a path and returns the command to build the benchmark suite.
        '''
        pass

    @abstractmethod
    def _run_trial(self, bench_path: str, args: TrialArgs):
        '''
        Takes a path and an argument structure, and returns the command to run
        the benchmark suite.
        '''
        pass

    def _log(self, msg: str, level: LogLevel):
        print_log(msg, level, self._log_level)

    def _shell_command(self, cmd: list[str]) -> None:
        '''
        Helper for running a subprocess with `subprocess`.
        '''
        try:
            subprocess.call(
                cmd,
                stdout=sys.stdout if self._log_level == LogLevel.DEBUG else subprocess.DEVNULL,
                stderr=sys.stderr if self._log_level == LogLevel.DEBUG else subprocess.DEVNULL)
        except Exception as e:
            self._log(f'Error running {cmd}: {e}', LogLevel.ERROR)
            sys.exit(1)

    def _change_dir(self, path: str) -> ChangeDir:
        '''
        Helper for changing working directory.

        Usage:
        ```
        with change_dir(path):
            ...
        ```
        '''
        return ChangeDir(path)

    def __apply_variant_in_impl(self, bench: Entry, variant: Variant) -> None:
        '''
        Private helper for applying variant.
        '''

        # Overwrite `config.impl` file with current variant.
        with open(variant.filename, 'w') as f:
            f.write(variant.body)

    def __trial(self, cfg: TrialConfig) -> None:
        '''
        Generate one set of data for `bench`.

        Assumes that `bench` is already instantiated
        (via `apply_variant`) with the current variant.

        This is private; it should not be called directly. Instead you should
        call `apply_variant` first.
        '''
        if not self.__variant:
            raise Exception('Cannot run trial without variant')

        method_label = cfg.label if cfg.label else cfg.method

        if not cfg.file:
            experiment = f'{cfg.bench.name},{method_label},{self.__variant.name},{cfg.property}'
        else:
            experiment = cfg.file
        file = os.path.join(self.results, f'{experiment}.json')

        if os.path.isfile(file):
            match self._replace_level:
                case ReplaceLevel.REPLACE:
                    pass
                case ReplaceLevel.SKIP:
                    self._log(f'Skipping {experiment}', LogLevel.WARNING)
                    return
                case ReplaceLevel.FAIL:
                    raise Exception(f'Already have data for {experiment}')

        self._log(f'Running {experiment}', LogLevel.INFO)
        with self._change_dir(self.__temp):
            self._run_trial(
                cfg.bench.path,
                TrialArgs(file=file,
                          trials=cfg.trials,
                          bench=cfg.bench.name,
                          method=cfg.method,
                          mutant=self.__variant.name,
                          property=cfg.property,
                          timeout=cfg.timeout,
                          label=method_label))

    @abstractmethod
    def _preprocess(self, bench: Entry) -> None:
        '''
        Takes a bench and does the required preprocessing.
        '''
        pass
