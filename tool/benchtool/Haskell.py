import os
import re
import json
from benchtool.BenchTool import BenchTool
from benchtool.Types import Config, Entry, LogLevel, ReplaceLevel, TrialArgs


class Haskell(BenchTool):

    def __init__(self,
                 results: str,
                 log_level: LogLevel = LogLevel.INFO,
                 replace_level: ReplaceLevel = ReplaceLevel.REPLACE):
        super().__init__(
            Config(start='{-',
                   end='-}',
                   ext='.hs',
                   path='workloads/Haskell',
                   ignore='common',
                   strategies='src/Strategy',
                   impl_path='src',
                   spec_path='src/Spec.hs'), results, log_level, replace_level)

    def all_properties(self, workload: Entry) -> set[str]:
        spec = os.path.join(workload.path, self._config.spec_path)
        with open(spec) as f:
            contents = f.read()
            regex = re.compile(r'prop_[^\s]*')
            matches = regex.findall(contents)
            return list(dict.fromkeys(matches))

    def _build(self, workload_path: str):
        with self._change_dir(workload_path):
            self._shell_command(['stack', 'build'])

    def _run_trial(self, workload_path: str, params: TrialArgs):

        def helper(t):
            with self._change_dir(workload_path):
                for _ in range(t):
                    p = params.to_json()
                    self._shell_command(['stack', 'exec', 'etna-workload', '--', p])

        def reformat():
            with open(params.file) as f:
                results = [json.loads(line) for line in f]
            open('file.txt', 'w').close()
            json.dump(results, open(params.file, 'w'))

        # This is an optimization that stops running the deterministic strategies
        # if it fails to find the bug in the first two trials. Should eventually
        # stop hardcoding the list of deterministic strategies.
        small = 2
        if params.trials > small and \
                params.strategy in ['Lean', 'Small', 'LeanRev', 'SmallRev']:
            helper(small)

            with open(params.file) as f:
                count = sum([line.count('"foundbug":false') for line in f])
                if count == small:
                    reformat()
                    return

            helper(params.trials - small)
        else:
            helper(params.trials)

        reformat()

    def _preprocess(self, workload: Entry) -> None:
        pass