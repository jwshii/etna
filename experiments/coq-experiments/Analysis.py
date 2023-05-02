from typing import Literal, Optional
from benchtool.Analysis import parse_results, overall_solved

import numpy as np
import pandas as pd

import plotly.express as px

import datetime

class MarkdownTable:
    def __init__(self, explanation: str, df: pd.DataFrame) -> None:
        self.explanation = explanation
        self.table = self.gen_md_table(df)

        self.text = f"{self.explanation}\n\n{self.table}"

    def gen_md_table(self, df: pd.DataFrame):
        return df.to_markdown().replace('nan', '   ')

    def __str__(self) -> str:
        return self.text


class MarkdownHeader:
    def __init__(self, name: str, level: int = 2) -> None:
        self.header_name = f'{"#" * level} {name}'

    def __str__(self) -> str:
        return f"{self.header_name}\n\n"

class MarkdownSection:
    def __init__(self, name: str, level: int = 2, text: str = '') -> None:
        self.section_name = f'{"#" * level} {name}'
        self.text = text

    def __str__(self) -> str:
        return f"{self.section_name}\n\n{self.text}\n\n"

class MarkdownDocument:
    def __init__(self, name: str) -> None:

        self.name = f"{name}: {datetime.datetime.now()}"
        self.doc = []
    
    def add_section(self, section: MarkdownSection):
        self.doc.append(section)
    
    def __str__(self) -> str:
        return f"# {self.name}\n\n" + ''.join([str(section) for section in self.doc])

    def save(self, path: str = None):
        if path is None:
            path = f"{self.name}.md"

        with open(path, 'w') as f:
            f.write(str(self))
    

def gen_md_table(df: pd.DataFrame):
    return df.to_markdown().replace('nan', '   ')


def generate_table(fields: list[str], comparisons: dict[tuple[str, str], float]) -> pd.DataFrame:
    """Generate a Markdown table from the results of the pairwise comparisons."""
    # Convert comparisons dict into a pandas DataFrame
    df = pd.DataFrame(columns=fields, index=fields)
    for (method1, method2), comparison in comparisons.items():
        df.loc[method1, method2] = comparison.round(2)
    
    return df



def pairwise_compare_successful_methods(results: pd.DataFrame, buffer: float) -> pd.DataFrame:
    results = results[results['foundbug'] == True]
    times = {}
    for method in results['method'].unique():
        method_results = results[results['method'] == method]
        times[method] = method_results.groupby(['task'])['time'].mean()
    
    # Get the list of methods
    methods = times.keys()
    # Create a pairwise comparison table of the methods
    comparisons = {}
    for method1 in methods:
        for method2 in methods:
            if method1 == method2:
                continue
            intersection = pd.merge(times[method1], times[method2], left_index=True, right_index=True, how='inner')
            t1 = intersection['time_x']
            t2 = intersection['time_y']
            comparison = t1 < t2
            threshold = (np.minimum(t1, t2) / np.maximum(t1, t2)) < (1-buffer)
            comparisons[(method1, method2)] = comparison[(comparison == True) & (threshold == True)].count() / comparison.count()

    return generate_table(methods, comparisons)

def exp_pairwise_comparison_with_bufffers(results: pd.DataFrame, benchmark: str) -> MarkdownSection:

    section_name = f"Pairwise comparison of methods in the {benchmark} benchmark"

    tables = []
    explanation = f"Following is the table showing the percentage of tasks where method on the row is faster than method on the column"    
    table = pairwise_compare_successful_methods(results, 0.0)
    
    tables.append(MarkdownTable(explanation, table))

    for buffer in [0.1, 0.2, 0.3, 0.4, 0.5]:
        explanation = f"Following is the table showing the percentage of tasks where method on the row is faster than method on the column, with at least by {int(buffer*100)}%"
        table = pairwise_compare_successful_methods(results, buffer)
        
        tables.append(MarkdownTable(explanation, table))
    
    text = '\n\n'.join([str(table) for table in tables])

    return MarkdownSection(section_name, 3, text)

def method_success_rate_for_task(results: pd.DataFrame, method: str, task: str) -> float:
    method_results = results[(results['method'] == method) & (results['task'] == task)]
    return method_results['foundbug'].mean()


def exp_success_rate_of_methods(results: pd.DataFrame, benchmark: str, detailed: bool = True):
    methods = results['method'].unique()
    tasks = results['task'].unique()
    success_rates = {}

    for method in methods:
        success_rates[method] = {}
        for task in tasks:
            success_rates[method][task] = method_success_rate_for_task(results, method, task)

    df = pd.DataFrame(success_rates)

    # delete rows with all zeros
    df = df.loc[(df != 0).any(axis=1)]
    
    # add a row with the average success rate of each method
    mean = df.mean().round(2)

    # add a row with the total number of successes of each method
    total = df[df == 1].count()


    if detailed:
        # add a column with the average success rate of each task
        df['Average'] = df.mean(axis=1).round(2)

    # Update the Index
    df['Variant'] = [task.split(',')[1] for task in df.index]
    df['Property'] = [task.split(',')[2].split('prop_')[1] for task in df.index]

    df = df.set_index(['Property', 'Variant'])
    df = df.sort_index()
    print(df)
    # print([[task.split(',')[1], task.split(',')[2].split('prop_')[1]] for task in df.index])
    # df.index = pd.MultiIndex([[task.split(',')[1], task.split(',')[2].split('prop_')[1]] for task in df.index], names=['Mutant', 'Property'])
    

    df.loc['Average Success Rate for Method'] = mean
    df.loc['Fully Successful Tasks for Method'] = total


    if not detailed:
        df = df.loc[['Average Success Rate for Method', 'Fully Successful Tasks for Method']]

    section_name = f"Success rate of each method for all tasks in the {benchmark} benchmark"
    explanation = f"Following is the table showing the success rate of each method for all tasks in the {benchmark} benchmark"
    
    table = MarkdownTable(explanation, df)


    return MarkdownSection(section_name, 3, str(table))




def exp_bst_size() -> MarkdownSection:
    import os
    entries = os.scandir('results/Coq/BST-size/')

    df = pd.DataFrame()
    for e in entries:
        res = pd.read_json(e.path, orient='records', typ='frame')
        res['size'] = np.int64(e.name.split(',')[0])
        df = pd.concat([df, res])

    df['inputs'] = df.apply(lambda x: x['passed'] + (1 if x['foundbug'] else 0), axis=1)
    df = df.drop(['bench', 'passed', 'method', 'discards', 'foundbug'], axis=1)

    # Group by task
    df = df.groupby(['mutant', 'property', 'size'])

    # Take average of the runs for each task
    df = df.aggregate(np.mean)

    # Get size out of the group
    df = df.reset_index()

    # Combine mutant-property into a single column
    df['mutant-property'] = df.apply(lambda x: f"{x['mutant']},{x['property']}", axis=1)
    del df['mutant']
    del df['property']


    # Create a linear regression line for each mutant-property
    time_regression_line = df.groupby('mutant-property').apply(lambda x: np.polyfit(x['size'], x['time'], 1))
    inputs_regression_line = df.groupby('mutant-property').apply(lambda x: np.polyfit(x['size'], x['inputs'], 1))

    # Filter the mutant-property where the correlation is not significant
    df = df[df.apply(lambda x: abs(time_regression_line[x['mutant-property']][0]) > 10**-6, axis=1)]
    df = df[df.apply(lambda x: abs(inputs_regression_line[x['mutant-property']][0]) > 10**-2, axis=1)]

    # Plot the trendline for size vs time and size vs inputs for each mutant-property using plotly express
    fig = px.scatter(df, x='size', y='time', color='mutant-property', trendline='ols', log_y=True, title='Size vs Time for Each Task')
    fig.data = [t for t in fig.data if t.mode == "lines"]
    fig.update_traces(showlegend=True) 
    fig.write_image("size_v_time.png")

    fig = px.scatter(df, x='size', y='inputs', color='mutant-property', trendline='ols', log_y=True, title='Size vs Inputs for Each Task')
    fig.data = [t for t in fig.data if t.mode == "lines"]
    fig.update_traces(showlegend=True) 
    fig.write_image("size_v_inputs.png")

    section_name = f"Plots for the BST-size benchmark"
    text = f"Following are the plots for the BST-size benchmark, first plot is the size vs time for each task, second plot is the size vs inputs for each task\n\n"
    text += "![Size vs Time](size_v_time.png){ width=70% }\n\n"
    text += "![Size vs Inputs](size_v_inputs.png){ width=70% }"

    return MarkdownSection(section_name, 2, text)

def compare_best_time_and_tests_to_failure() -> MarkdownSection:
    pass


def overall_solved_inputs(df: pd.DataFrame,
                   agg: Literal['any', 'all'],
                   within: Optional[float] = None) -> pd.DataFrame:
    df = df.copy()

    # Define new column for whether found the bug within time limit.
    df['solved'] = df['foundbug']
    if within:
        df['solved'] &= df['inputs'] < within

    # Compute number of tasks where any / all trials were solved.
    df = df.groupby(['bench', 'method', 'task'], as_index=False).agg({'solved': agg})
    df['total'] = 1
    df = df.groupby(['bench', 'method']).sum()

    return df[['solved', 'total']]


def exp_different_timeouts():
    df = parse_results('results/Coq/BST/')
    for within in [0.1, 1, 10]:
        dft = overall_solved(df, agg='all', within=within)
        dft = dft.reset_index()
        dft = dft.groupby(['method']).sum()
        print('\n\nWithin', within, 'seconds:')
        print(dft)

    print('\n\n------------------\n\n')
    for within in [10, 100, 1000, 10000, 100000]:
        dft = overall_solved_inputs(df, agg='all', within=within)
        dft = dft.reset_index()
        dft = dft.groupby(['method']).sum()
        print('\n\nWithin', within, 'inputs:')
        print(dft)


def fuzzer_fails():
    df = parse_results('results/Coq/BST/')
    df = df[df['foundbug'] == False]
    print(df['method'].unique())
    fuzzy_random_fails : set[str] = set(df[df['method'] == 'FuzzyRandom']['task'].unique())
    mutate_random_fails  : set[str] = set(df[df['method'] == 'MutateRandom']['task'].unique())
    from pprint import pprint
    print('Only FuzzyRandom fails:')
    pprint(fuzzy_random_fails - mutate_random_fails)
    print('Only MutateRandom fails:')
    pprint(mutate_random_fails - fuzzy_random_fails)
    print('Both fail:')
    pprint(fuzzy_random_fails & mutate_random_fails)

if __name__ == '__main__':

    doc = MarkdownDocument('Results')

    # for case in ['BST', 'RBT', 'FSub']:

    #     doc.add_section(MarkdownHeader(f"Results for the {case} benchmark", 2))
    #     # Get results as a pandas DataFrame
    #     results = parse_results(f'results/Coq/{case}/')

    #     # Exp 0: Mean time to failure and mean tests to failure for each method
    #     # doc.add_section(exp_mean_time_and_tests_to_failure(results, case))
        
    #     # Exp 1: Pairwise comparison of successful methods
    #     doc.add_section(exp_pairwise_comparison_with_bufffers(results, case))


    #     # Exp 2: Success rate of methods
    #     doc.add_section(exp_success_rate_of_methods(results, case, detailed=True))

    # # Exp3 : Affect of size on the time to failure and tests to failure
    # doc.add_section(exp_bst_size())

    # print(doc)
    # doc.save()

    fuzzer_fails()