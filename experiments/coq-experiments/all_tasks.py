from benchtool.Analysis import *

RESULTS = 'results/Coq/'

tasks = set()

for name in ['BST', 'RBT', 'STLC']:
    df = parse_results(RESULTS + name)
    print(df['task'].unique())
    tasks = tasks | set(df['task'].unique())
with open('coq-all.txt', 'w') as f:
    f.write(str(sorted(tasks)))