from benchtool.Analysis import *
from benchtool.Plot import *
from functools import partial

RESULTS = '../qcb-results/final/exp1'
df = parse_results(RESULTS)
df['foundbug'] = df['foundbug'] & (df['time'] < 60)

dfidx = df[df['method'] == 'QuickIndex']
df = df[df['method'] != 'QuickIndex']

# dfs = df[df['bench'] == 'STLC']
# dfs['solved'] = dfs['foundbug']
# dfs['solved'] &= dfs['time'] < 0.1
# dfs = dfs.groupby(['bench', 'method', 'task'], as_index=False).agg({'solved': 'all'})
# one = list(dfs[(dfs['method'] == 'Correct') & dfs['solved']]['task'])
# two = list(dfs[(dfs['method'] == 'Lean') & dfs['solved']]['task'])
# tasks = [task for task in two if task not in one]
# print(df[(df['method'] == 'Lean') & (df['task'].isin(tasks))])

def charts(df):
    for bench in ['BST', 'RBT', 'STLC', 'FSUB']:
        times = partial(
            stacked_barchart_times,
            case=bench,
            df=df[df['bench'] == bench],
            show=False,
        )
        times(methods=['Correct', 'Small', 'Lean', 'Quick'],
              colors=['#000000', '#D61C4E', '#6D0E56', '#243763'],
              limits=[0.1, 1, 10, 60],
              limit_type='time',
              show=True)
# R1

dashboard(df).run_server()

def rates(df):
    for agg in ['all', 'any']:
        print(agg)
        dfa = overall_solved(df, agg).reset_index()
        dfa = dfa.groupby('method').sum()
        dfa['percent'] = dfa['solved'] / dfa['total']
        print(dfa)


def diffs(df):
    for col in ['time', 'inputs']:
        print(col)
        (_, table, total) = statistical_differences(df[df['method'].isin(['Quick', 'Correct'])],
                                                    col=col,
                                                    alpha=0.05)
        print(table)
        print(total)


# R2


def slow(df):
    df = df[df['method'].isin('Lean', 'Small')]
    df = df[df['bench'] == 'BST']
    df = df.groupby(['task', 'method'], as_index=False).agg({'time': 'mean', 'foundbug': 'all'})
    df = df[df['foundbug']]
    df = df.set_index('task')

    task = df[df['method'] == 'Small']['time'].idxmax()
    print(df.loc[task])


def testrates(df):
    df = df[df['method'].isin(['Lean', 'Small'])]
    df = df.groupby(['task', 'method'], as_index=False).agg({
        'time': 'mean',
        'inputs': 'mean',
        'discards': 'mean',
        'foundbug': 'all'
    })
    df = everyone_solved(df)
    df['discards'] = df['discards'].fillna(0)
    df['tests'] = df['inputs'] + df['discards']
    df = df.groupby('method').agg({'tests': sum, 'time': 'sum'})
    df['testrate'] = df['tests'] / df['time']
    print(df)


# R3


def solved_by(df, method: str, agg='all'):
    df = df.groupby(['bench', 'method', 'task'], as_index=False).agg({'foundbug': agg})
    return list(df[(df['method'] == method) & df['foundbug']]['task'])


def sometimes(df, method: str):
    return [
        t for t in solved_by(df, method, agg='any') if t not in solved_by(df, method, agg='all')
    ]


def leanquick(df):
    df = df[df['method'].isin(['Quick', 'Lean'])]

    assert (len([t for t in solved_by(df, 'Quick') if t not in solved_by(df, 'Lean')]) == 0)
    leanonlys = [t for t in solved_by(df, 'Lean') if t not in solved_by(df, 'Quick')]
    somequicks = sometimes(df, 'Quick')
    someleans = sometimes(df, 'Lean')
    print(len(somequicks), len(someleans))

    df = df[df['task'].isin(somequicks + someleans + leanonlys)]
    df['foundbug'] = df['foundbug'].astype('int')
    df['mintime'] = df['time']
    df['maxtime'] = df['time'].map(lambda x: x if x < 60 else 0)
    df = df.groupby(['task', 'method']).agg({'foundbug': 'sum', 'mintime': 'min', 'maxtime': 'max'})
    print(df)
