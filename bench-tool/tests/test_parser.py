
from benchtool.Mutant import Parser
from benchtool.BenchTool import Config
from benchtool.Types import Entry

import os

def test_parse_valid_mutants():
    config = Config(
        start='{-',
        end='-}',
        ext='.hs',
        path='benchtool/tests/test_data',
        ignore="",
        methods='test',
        impl='test.hs',
        spec="",
    )
    parser = Parser(config)
    bench = Entry('test.hs', 'test_data')
    nodes_dict = parser.parse(bench)
    assert len(nodes_dict) == 2
    nodes = nodes_dict['test_data/test.hs']
    
    assert nodes[0].text.find('code start') != -1
    assert nodes[2].text.find('hey last') != -1
    assert nodes[1].base.find('base mutant') != -1
    assert nodes[1].mutants[0].tag == 'mut_1'
    assert nodes[1].mutants[1].body.find('mut 2.5') != -1
    nodes2 = nodes_dict['test_data/test2.hs']
    assert nodes2[0].text.find('node end') != -1
    assert nodes2[1].base.find('base nomut') != -1
    assert nodes2[2].text.find('ley first') != -1

def test_parse_no_base():
    config = Config(
        start='(*',
        end='*)',
        ext='.v',
        path='benchtool/tests/test_data',
        ignore="",
        methods='test',
        impl='test.v',
        spec="",
    )
    parser = Parser(config)
    bench = Entry('test.v', 'test_data')
    try:
        nodes = parser.parse(bench)
    except Exception as e:
        assert str(e) == 'No base mutant found' #todo@keles: 'for test.v'


    
test_parse_valid_mutants()