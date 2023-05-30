import json
import os

from benchtool.Analysis import parse_results

names = ['BST', 'RBT', 'STLC', 'FSub', 'IFC']


def get_useful_mutant_property_pairs(df):
    pairs = set()
    df = df[df['foundbug'] == True]
    for _, row in df.iterrows():
        pairs.add((row['mutant'], row['property']))
    return list(pairs)

def generate_tasks(df):
    pairs = get_useful_mutant_property_pairs(df)
    tasks = dict()
    for mutant, property in pairs:
        if mutant not in tasks:
            tasks[mutant] = set()
        tasks[mutant].add(property)
    
    for mutant, properties in tasks.items():
        tasks[mutant] = sorted(list(properties))

    return tasks

def generate_variants(df):
    return list(df["mutant"].unique())

def generate_methods(df):
    return list(df["method"].unique())

def generate_properties(df):
    return list(df["property"].unique())


def generate_experiment_config(name):
    path = f'{os.getcwd()}/results/Coq/{name}/'
    df = parse_results(path)
    experiment_config = {
        "name": name,
        "variants": sorted(generate_variants(df)),
        "properties": sorted(generate_properties(df)),
        "methods": sorted(generate_methods(df)),
        "tasks": generate_tasks(df),
    }
    return experiment_config



if __name__ == '__main__':
    for name in names:
        try:
            cfg = generate_experiment_config(name)

            with open(f'experiments/coq-experiments/{name}_exp_cfg.json', 'w') as f:
                json.dump(cfg, f, indent=4)
        except Exception as e:
            print(e)
            print('This experiment is not yet run.')