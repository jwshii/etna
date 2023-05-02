from benchtool.Analysis import *

RESULTS = '../qcb-results/final/exp0'
df = parse_results(RESULTS)
df['foundbug'] = df['foundbug'] & (df['time'] < 5)

dfcorrect = df[(df['method'] == 'Correct') & (df['mutant'] != 'base')]
assert (dfcorrect['foundbug'].all())
assert (len(dfcorrect.index) == 167)

dfbase = df[df['mutant'] == 'base']
assert ((~dfbase['foundbug']).all())