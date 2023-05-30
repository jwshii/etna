import itertools
import numpy as np
import os
import pandas as pd
import plotly.express as px
import scipy.stats as sc
from benchtool.Util import scandir_filter
from typing import Literal, Optional


def parse_results(results: str) -> pd.DataFrame:
    entries = scandir_filter(results, os.path.isfile)

    df = pd.concat([pd.read_json(e.path, orient='records', typ='frame') for e in entries])

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['passed'], axis=1)

    df['task'] = df['workload'] + ',' + df['mutant'] + ',' + df['property']
    return df


def overall_solved(df: pd.DataFrame,
                   agg: Literal['any', 'all'],
                   within: Optional[float] = None,
                   solved_type: str = 'time') -> pd.DataFrame:
    df = df.copy()

    # Define new column for whether found the bug within time limit.
    df['solved'] = df['foundbug']
    if within:
        df['solved'] &= df[solved_type] < within

    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(['workload', 'strategy', 'task'], as_index=False).agg({'solved': agg})
    df['total'] = 1
    df = df.groupby(['workload', 'strategy']).sum(numeric_only=False)

    return df[['solved', 'total']]


def everyone_solved(df: pd.DataFrame) -> pd.DataFrame:
    df = df.copy()

    # Only include tasks where every strategy found the bug.
    dft = df.copy()
    dft = dft.groupby(['task']).agg({'foundbug': 'all'})

    return df[df['task'].isin(dft[dft['foundbug']].index)]


def task_average(df: pd.DataFrame, col: str) -> pd.DataFrame:
    df = df.copy()
    df = everyone_solved(df)

    # Compute averages and standard deviations.
    std = col + '_std'
    df[std] = df[col]
    df = df.groupby(['workload', 'strategy', 'task']).agg({col: 'mean', std: 'std'})

    return df[[col, std]]


def statistical_differences(df: pd.DataFrame,
                            col: str,
                            alpha: float = 0.05,
                            det: list[str] = []) -> tuple[pd.DataFrame, pd.DataFrame, int]:
    df = df.copy()
    df = everyone_solved(df)

    tasks = df['task'].unique()
    strategies = df['strategy'].unique()

    df = df.groupby(['task', 'strategy'])[col].apply(list)

    def pair_name(m1, m2):
        if m1 > m2:
            (m1, m2) = (m2, m1)
        return m1 + '/' + m2

    results = {}
    for task in tasks:
        dft = df.loc[task]
        for (m1, m2) in itertools.combinations(dft.index, 2):
            c1 = dft.loc[m1]
            c2 = dft.loc[m2]

            if m1 not in det and m2 not in det:
                # For random strategies, Mann-Whitney U test.
                pvalue = sc.mannwhitneyu(c1, c2).pvalue
            elif m1 in det and m2 in det:
                # For two deterministic strategies, trivially significant.
                pvalue = 0
            else:
                if m1 in det:
                    det, rands = c1[0], c2
                else:
                    det, rands = c2[0], c1
                # For one random and one deterministic strategy,
                # one-sample Wilcoxon test.
                pvalue = sc.wilcoxon([r - det for r in rands]).pvalue

            results[(pair_name(m1, m2), task)] = [pvalue]

    idx = pd.MultiIndex.from_tuples(results.keys(), names=('strategies', 'task'))
    pvalues = pd.DataFrame(list(results.values()), index=idx, columns=['pvalue'])
    # The row
    #   m1/m2   t   value
    # means that the p-value for [m1] and [m2] having statistically
    # different distributions on task [t] is [value]

    results = {}
    for m1 in strategies:
        results[m1] = []
        for m2 in strategies:
            score = 0
            for task in tasks:  # Assumes that all strategies are run on all tasks.
                c1 = np.mean(df.loc[task, m1])
                c2 = np.mean(df.loc[task, m2])
                if c1 < c2 and pvalues.loc[pair_name(m1, m2), task]['pvalue'] < alpha:
                    score = score + 1

            results[m1].append(score)

    scores = pd.DataFrame(list(results.values()), index=strategies, columns=strategies)
    # The table
    #       m1  m2
    #   m1   0   7
    #   m2   4   0
    # means that [m1] is statistically significantly better than [m2] on 7 tasks
    # and that [m2] ... better than [m1] on 4 tasks

    return (pvalues, scores, len(tasks))


def effect_sizes(df: pd.DataFrame, col: str, strategy1: str, strategy2: str) -> pd.DataFrame:

    def a12(l1, l2):
        # Compute the Vargha and Delaney's A12 statistic.
        m = len(l1)
        n = len(l2)

        ranks = sc.rankdata([l1, l2])
        r1 = sum(ranks[:m])

        numer = (r1 / m) - ((m + 1) / 2)
        return numer / n

    df = df.copy()
    df = df[df['strategy'].isin([strategy1, strategy2])]
    df = everyone_solved(df)

    tasks = df['task'].unique()

    df = df.groupby(['task', 'strategy'])[col].apply(list)

    results = {}
    # Pairwise comparisons per task.
    # > 0.5 if [strategy1] values are *higher* than [strategy2].
    for task in tasks:
        c1 = df.loc[task, strategy1]
        c2 = df.loc[task, strategy2]
        a12_value = a12(c1, c2)
        results[task] = [a12_value]

    a12_values = pd.DataFrame.from_dict(results, columns=['a12'], orient='index')

    return a12_values


def boxplots(df: pd.DataFrame, col: str, strategy1: str, strategy2: str, workload_orders: list[str]):
    dfes = []
    for workload in df['workload'].unique():
        dfb = df[df['workload'] == workload]

        effects = effect_sizes(dfb, col, strategy1, strategy2)
        effects['workload'] = workload
        dfes.append(effects)

    dfe = pd.concat(dfes)
    boxplot = px.box(dfe, x='workload', y='a12', category_orders={'workload': workload_orders})
    return boxplot


