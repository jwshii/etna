import os

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, LogLevel, TrialConfig
from Tasks import tasks

RESULTS = f'{os.getcwd()}/jwshi'

tool = Haskell(RESULTS, replace_level=ReplaceLevel.REPLACE, log_level=LogLevel.DEBUG)

for bench in tool.all_benches():
    if bench.name != 'BST':
        continue

    for variant in tool.all_variants(bench):
        if variant.name == 'base':
            continue

        run_trial = tool.apply_variant(bench, variant)

        for method in tool.all_methods(bench):
            trials = 100

            if method.name != 'Size':
                continue

            for property in tool.all_properties(bench):
                if property.split('_')[1] not in tasks[bench.name][variant.name]:
                    continue

                for size in range(3, 31, 3):
                    os.environ['BSTSIZE'] = str(size)

                    file = f'{size:02},{bench.name},{method.name},{variant.name},{property}'
                    cfg = TrialConfig(bench=bench,
                                      method=method.name,
                                      property=property,
                                      label=f'{method.name}{size:02}',
                                      trials=trials,
                                      timeout=65,
                                      file=file)
                    run_trial(cfg)
