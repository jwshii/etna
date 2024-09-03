bst = {
    'base': [],
    'insert_1': [
        'InsertPost',
        'InsertModel',
        'DeleteInsert',
        'InsertInsert',
        'InsertUnion',
        'UnionDeleteInsert',
    ],
    'insert_2': [
        'InsertPost',
        'InsertModel',
        'InsertDelete',
        'DeleteInsert',
        'InsertInsert',
        'InsertUnion',
        'UnionDeleteInsert',
    ],
    'insert_3': [
        'InsertPost',
        'InsertModel',
        'InsertDelete',
        'InsertInsert',
        'InsertUnion',
        'UnionDeleteInsert',
    ],
    'delete_4': [
        'DeleteModel',
        'DeletePost',
        'DeleteDelete',
        'DeleteInsert',
        'DeleteUnion',
        'InsertDelete',
        'UnionDeleteInsert',
    ],
    'delete_5': [
        'DeleteModel',
        'DeletePost',
        'DeleteDelete',
        'DeleteInsert',
        'DeleteUnion',
        'UnionDeleteInsert',
    ],
    'union_6': [
        'UnionValid',
        'UnionPost',
        'UnionModel',
        'DeleteUnion',
        'InsertUnion',
        'UnionDeleteInsert',
        'UnionUnionAssoc',
        'UnionUnionIdem',
    ],
    'union_7': [
        'UnionValid',
        'UnionPost',
        'UnionModel',
        'DeleteUnion',
        'InsertUnion',
        'UnionDeleteInsert',
        'UnionUnionAssoc',
    ],
    'union_8': [
        'UnionPost',
        'UnionModel',
        'DeleteUnion',
        'InsertUnion',
        'UnionDeleteInsert',
        'UnionUnionAssoc',
    ],
}

redblack = {
    'miscolor_insert': [
        'InsertValid',
        'DeleteInsert',
    ],
    'miscolor_delete': ['DeleteValid'],
    'miscolor_balLeft': [
        'DeleteValid',
        'DeleteDelete',
    ],
    'miscolor_balRight': [
        'DeleteValid',
        'DeleteDelete',
    ],
    'miscolor_join_1': ['DeleteValid'],
    'miscolor_join_2': [
        'DeleteValid',
        'DeleteDelete',
    ],
    'no_balance_insert_1': [
        'InsertValid',
        'DeleteInsert',
        'InsertDelete',
    ],
    'no_balance_insert_2': [
        'InsertValid',
        'DeleteInsert',
        'InsertDelete',
    ],
    'swap_cd': [
        'InsertValid',
        'InsertModel',
        'InsertPost',
        'DeleteValid',
        'DeletePost',
        'DeleteModel',
        'DeleteDelete',
        'DeleteInsert',
        'InsertDelete',
        'InsertInsert',
    ],
    'swap_bc': [
        'InsertValid',
        'InsertModel',
        'InsertPost',
        'DeleteValid',
        'DeletePost',
        'DeleteModel',
        'DeleteDelete',
        'DeleteInsert',
        'InsertDelete',
        'InsertInsert',
    ],
}

lu = {
    'base': [],
    'wsP_1': [
        'val',
        'exp',
        'stat',
    ],
    'stringP_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'boolValP_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'stringValP_1': [
        'val',
        'exp',
        'stat',
    ],
    'stringValP_2': [
        'val',
        'exp',
        'stat',
    ],
    'stringValP_3': [
        # 'val',
        'exp',
        'stat',
    ],
    'stringValP_4': [
        'val',
        'exp',
        'stat',
    ],
    'reserved_1': [
        # 'val',
        # 'exp',
        # 'stat',
    ],
    'reserved_2': [
        # 'val',
        'exp',
        'stat',
    ],
    'reserved_3': [
        # 'val',
        'exp',
        'stat',
    ],
    'nameP_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'nameP_2': [
        # 'val',
        'exp',
        'stat',
    ],
    'bofP_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'tableConstP_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'statementP_1': [
        # 'val',
        # 'exp',
        'stat',
    ],
    'level_1': [
        # 'val',
        'exp',
        'stat',
    ],
    'ppNot_1': [
        # 'val',
        'exp',
        'stat',
    ]
}

tasks = {'BST': bst, 'RBT': {**bst, **redblack}, 'LuParser': lu}
