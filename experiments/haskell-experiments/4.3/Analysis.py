from benchtool.Analysis import *
from functools import partial

RESULTS = '../qcb-results/final/exp3'
df = parse_results(RESULTS)
df['foundbug'] = df['foundbug'] & (df['time'] < 60)

# for benches in [('trees', ['BST', 'RBT']), ('langs', ['STLC', 'FSUB'])]:
#     times = partial(stacked_barchart_times,
#                     case=benches[0],
#                     df=df[df['bench'].isin(benches[1])],
#                     show=False)
#     times(methods=['SmallRev', 'Small', 'LeanRev', 'Lean'],
#           colors=['#D61C4E', '#D61C4E', '#6D0E56', '#6D0E56'],
#           limits=[0.1, 1, 10, 60],
#           save='revs')

df = df[df['bench'].isin(['BST', 'RBT'])]


def solved_by(df, method: str, agg='all'):
    df = df.groupby(['bench', 'method', 'task'], as_index=False).agg({'foundbug': agg})
    return list(df[(df['method'] == method) & df['foundbug']]['task'])


def oneorder(df, method: str):
    return [t for t in solved_by(df, f'{method}Rev') if t not in solved_by(df, method)]


assert (len([t for t in solved_by(df, 'Lean') if t not in solved_by(df, 'LeanRev')]) == 0)
assert (len([t for t in solved_by(df, 'Small') if t not in solved_by(df, 'SmallRev')]) == 0)

leanonly = oneorder(df, 'Lean')
smallonly = oneorder(df, 'Small')

dfsc = df[(df['method'] == 'SmallRev') & (df['task'].isin(smallonly))]
dfsc = dfsc.groupby('task').mean()
print(dfsc)

dflc = df[(df['method'] == 'LeanRev') & (df['task'].isin(leanonly))]
dflc = dflc.groupby('task').mean()
print(dflc)