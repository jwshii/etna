import os

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, LogLevel
from benchtool.Experiment import Experiment

RESULTS = f'{os.getcwd()}/jwshi'

tool = Haskell(RESULTS, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)


class MyExperiment(Experiment):

    def skip(self, bench: str, variant: str, method: str, property: str) -> bool:
        if method not in ['QuickIndex']:
            return True

        if variant == 'base':
            return True

        return False

    def trials(self, _: str, method: str) -> int:
        return 10

    def timeout(self) -> float:
        return 65


experiment = MyExperiment(tool)
experiment.run()