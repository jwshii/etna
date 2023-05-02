import plotly.express as px
from benchtool.Analysis import *

RESULTS = '../qcb-results/final/exp2'
df = parse_results(RESULTS)

assert (df['foundbug'].all())

df['size'] = df['method'].str[-2:]
df['size'] = df['size'].astype(int)
df = df[['task', 'size', 'inputs', 'time']]

df = df.groupby(['task', 'size'], as_index=False).agg({'inputs': 'mean', 'time': 'mean'})

colors = {
    'BST,delete_5,prop_DeleteDelete': 'black',
    'BST,insert_3,prop_InsertInsert': 'black',
    'BST,union_8,prop_UnionPost': 'black'
}
color_map = {task: colors[task] if task in colors else 'lightgray' for task in df['task'].unique()}

fig = px.line(df,
              x='size',
              y='inputs',
              color='task',
              color_discrete_map=color_map,
              category_orders={
                  'task': [
                      'BST,delete_5,prop_DeleteDelete', 'BST,insert_3,prop_InsertInsert',
                      'BST,union_8,prop_UnionPost'
                  ]
              })
fig.data = fig.data[::-1]
fig.update_layout(xaxis_title='size of tree', yaxis_title='inputs to failure', showlegend=False)
fig.update_layout(font={'family': 'Helvetica', 'size': 50}, width=1500, height=1200)
fig.update_layout(xaxis=dict(tickmode='linear', tick0=3, dtick=3))
fig.show()
