import argparse
import os
import re

from benchtool.Haskell import Haskell
from benchtool.Types import ReplaceLevel, TrialConfig, Entry
from benchtool.Tasks import tasks

# Section 4.1 (Comparing Frameworks)


def collect(results: str):
    tool = Haskell(results, replace_level=ReplaceLevel.SKIP)

    for workload in tool.all_workloads():
        if workload.name not in ['LuParser']:
            continue

        # Replace property strng in Main.hs
        with open(os.path.join(workload.path, 'app/Main.hs'), 'r+') as f:
            oirginal_file = f.read()

            # TODO: string should not be hardcoded
            old_string = r'\(allProps "src/Spec.hs"\)'
            # workload name not added since it is not used in all_properties
            new_content = str(tool.all_properties(
                Entry(workload.name, workload.path))).replace('\'', '\"')

            new_file = re.sub(old_string, new_content, oirginal_file)
            print(new_file)
            f.seek(0)
            f.write(new_file)
            f.truncate()

            for variant in tool.all_variants(workload):
                # if variant.name not in ['boolValP_1', 'stringValP_1']:
                #     continue
                print(variant.name + "\n")

                if variant.name == 'base':
                    # Don't run on base (non-buggy) implementation.
                    continue

                run_trial = None

                for strategy in tool.all_strategies(workload):
                    # , 'Hybrid', 'Random']:
                    if strategy.name not in ['Random', 'Hybrid', "Correct"]:
                        continue

                    for property in tool.all_properties(workload):
                        if property != 'prop_roundtrip_exp':
                            continue

                        # if workload.name in ['BST', 'RBT']:
                        #     if property.split('_')[1] not in tasks[workload.name][variant.name]:
                        #         continue

                        # TO SAVE TIME:
                        # Run only 1 trial for deterministic strategies
                        trials = 1 if strategy.name in [
                            'Lean', 'Small'] else 10

                        # Also, stop trials as soon as fail to find bug.
                        # (via short_circuit flag below)

                        # See README discussion about LeanCheck.
                        timeout = 65 if strategy.name != 'Lean' else 12

                        # Don't compile tasks that are already completed.
                        finished = set(os.listdir(results))
                        file = f'{workload.name},{strategy.name},{variant.name},{property}'
                        if f'{file}.json' in finished:
                            continue

                        if not run_trial:
                            run_trial = tool.apply_variant(workload, variant)

                        cfg = TrialConfig(workload=workload,
                                          strategy=strategy.name,
                                          property=property,
                                          trials=trials,
                                          timeout=5,
                                          short_circuit=True)

                        run_trial(cfg)
            f.seek(0)
            f.write(oirginal_file)
            f.truncate()


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--data', help='path to folder for JSON data')
    args = p.parse_args()

    results_path = f'{os.path.join(os.getcwd(), args.data)}'
    collect(results_path)
