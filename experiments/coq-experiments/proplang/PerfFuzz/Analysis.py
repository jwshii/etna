import pathlib
from typing import List
import random
from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial
import itertools

def df_insert(df: pd.DataFrame, column: str, value: any) -> pd.DataFrame:
    df.insert(len(df.columns), column, value)
    return df

def parse_results(results: str) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)
    entries = [e for e in entries if e.path.endswith('.json')]

    df = pd.concat([df_insert(pd.read_json(e.path, orient='records', typ='frame'), "version", e.name.split(',')[2]) for e in entries])

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['passed'], axis=1)

    df['task'] = df['workload'] + ',' + df['mutant'] + ',' + df['property']
    return df


def insertion_sort(ls: List[int]) -> int:
    num_comparisons = 0
    for i in range(1, len(ls)):
        j = i
        while j > 0 and ls[j] < ls[j-1]:
            num_comparisons += 1
            ls[j], ls[j-1] = ls[j-1], ls[j]
            j -= 1
    return num_comparisons

def mkList(s: str) -> List[int]:
    try:
        stripped = s[4:-1]
        nums = stripped.split('; ')
        return [int(n) for n in nums]
    except Exception as e:
        return []


def insertion_sort_on_random_lists() -> float:
    sum = 0
    n = 100
    for i in range(n):
        ls = [random.randint(0, 10) for _ in range(1000)]
        sum += (insertion_sort(ls) / (len(ls) ** 2))
    return sum / n 

def insertion_sort_on_reverse_sorted_lists() -> float:
    sum = 0
    n = 100
    for i in range(n):
        ls = list(range(1000, 0, -1))
        sum += (insertion_sort(ls) / (len(ls) ** 2))
    return sum / n

if __name__ == "__main__":

    filepath = pathlib.Path(__file__).resolve().parent

    results_path = f'{filepath}/results'
    images_path = f'{filepath}/figures'

    df = parse_results(results_path)

    df['comparisons'] = df['counterexample'].apply(mkList).apply(insertion_sort)
    df['lengths'] = df['counterexample'].apply(mkList).apply(len)
    df['comp/lens^2'] = df['comparisons'] / (df['lengths'] ** 2)

    df = df.drop(['workload', 'discards', 'foundbug', 'strategy', 'mutant', 'property', 'version', 'task', 'time', 'counterexample'], axis=1)

    df.to_csv(f'{results_path}/results.csv')


    print(df.groupby('inputs').mean())

    