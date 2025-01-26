import pandas as pd
from final_parser.RNGLR import RNParseTableConstructer, RNGLRParser
# from final_parser.LRs import add_start_state
# from final_parser.LRs import LR0DFA, SLR1DFA, LR1DFA, LALR1DFA
# from final_parser.LRs import LR0Parser, SLR1Parser, LR1Parser, LALR1Parser
from final_parser.Earley import EarleyParser, LeoParser, EnhancedExtractor, tree_to_str
from final_parser.CYK import CYKParser
from final_parser.GLL import compile_grammar

import time
import random
import tracemalloc
from collections import defaultdict



def benchmark(parsers, grammar, start, test_cases):
    results = []
    for test_str, is_ambiguous in test_cases:
        # test_str = "a"*length
        row = {
            'length': len(test_str),
            'ambiguous': is_ambiguous,
            'parsers': {}
        }
        for name in parsers:
            if name == "GLL":
                gll = compile_grammar(grammar)
            elif name == "CYK":
                cyk = CYKParser(grammar)
            elif name == "Earley":
                earley = EarleyParser(grammar)
            elif name == "Leo":
                leo = LeoParser(grammar)
            elif name == "RNGLR":
                rntable = RNParseTableConstructer(grammar, start)
                rnglr = RNGLRParser(rntable.grammar, rntable.non_terminals, rntable.terminals, rntable.start, rntable.parse_table, rntable.epsilon_sppf)
            
            

            if name == "GLL":
                start_time = time.perf_counter()
                tracemalloc.start()
                gll_result = gll.parse_on(test_str, start)
                parse_time = time.perf_counter() - start_time
                memory_peak = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()
            elif name == "CYK":
                start_time = time.perf_counter()
                tracemalloc.start()
                cyk_result = cyk.parse_on(test_str, start)
                parse_time = time.perf_counter() - start_time
                memory_peak = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()
            elif name == "Earley":
                start_time = time.perf_counter()
                tracemalloc.start()
                earley_result = EnhancedExtractor(earley, test_str, start)
                parse_time = time.perf_counter() - start_time
                memory_peak = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()
            elif name == "Leo":
                start_time = time.perf_counter()
                tracemalloc.start()
                leo_result = leo.parse_on(test_str, start)
                print(leo_result)
                for tree in leo_result:
                    pass
                parse_time = time.perf_counter() - start_time
                memory_peak = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()
            elif name == "RNGLR":
                import cProfile
                profiler = cProfile.Profile()
                profiler.enable()
                start_time = time.perf_counter()
                tracemalloc.start()

                rnglr_result = rnglr.parse(list(test_str))

                parse_time = time.perf_counter() - start_time
                memory_peak = tracemalloc.get_traced_memory()[1]
                tracemalloc.stop()

                profiler.disable()
                profiler.print_stats(sort="time")



            # parser.metrics.reset()
            # success = parser.parse(test_str, start)
            row['parsers'][name] = {
                'time': parse_time,
                'memory': memory_peak,
                # 'edges': parser.metrics.edges,
                # 'cells': parser.metrics.cells,
                # 'nodes': parser.metrics.nodes,
                # 'ambiguous_trees': parser.metrics.ambiguous_trees,
                # 'success': success
            }
        results.append(row)
    return results

# Example grammar
# grammar = {
#     '<S>': [['<A>']],
#     '<A>': [['a', '<A>'], ['a']]  # Right-recursive but unambiguous
# }

# grammar = {
#     "<S>": [["a", "<S>", "<B>", "<B>"], ["a"]],
#     "<B>": [["b"], []]
# }

# grammar = {
#     '<S>': [
#           ['<A>', '<B>'],
#           ['<B>', '<C>'],
#           ['<A>', '<C>'],
#           ['c']],
#    '<A>': [
#         ['<B>', '<C>'],
#         ['a']],
#    '<B>': [
#         ['<A>', '<C>'],
#         ['b']],
#    '<C>': [
#         ['c']],
# }

# start = "<S>"

# # Test cases: (input_length, is_ambiguous)
# test_cases = [
#     ("bcac", False),
#     ('a' + 'c' * 198 + 'b', False)
#     # ("a"*10, False),
#     # ("a"*100, False),
#     # ("a"*1000, False)
# ]


import simplefuzzer as fuzzer

def parents(g):
    parent = {}
    for k in g:
        for r in g[k]:
            for t in r:
                if t not in g: continue
                if t not in parent: parent[t] = set()
                parent[t].add(k)
    return parent


def _k_paths(g, k, parent):
    if k == 1: return [[k] for k in g]
    _k_1_paths = _k_paths(g, k-1, parent)
    # attach parents to each of the _k_1_paths.
    new_paths = []
    for path in _k_1_paths:
        if path[0] not in parent: continue
        for p in parent[path[0]]:
            new_paths.append([p] + path)
    return new_paths


def k_paths(g, k):
    g_parents = parents(g)
    return _k_paths(g, k, g_parents)


def find_rule_containing_key(g, key, root):
    leaf = root[0]
    for rule in g[key]:
        r = []
        while rule:
            token, *rule = rule
            if leaf != token:
                r.append((token, None))
            else:
                return r + [root] + [(t, None) for t in rule]
    assert False


def path_to_tree(path_, g):
    leaf, *path = reversed(path_)
    root = (leaf, [])
    # take the lowest
    while path:
        leaf, *path = path
        if not path: return root
        rule = find_rule_containing_key(g, leaf, root)
        root = [leaf, rule]

def tree_fill_(g, pt, f):
    key, children = pt
    if not children:
        if key in g:
            return (key, [(f.fuzz(key), [])])
        else:
            return (key, [])
    else:
        return (key, [tree_fill_(g, c, f) for c in children])


def tree_fill(g, pt):
    rgf = fuzzer.LimitFuzzer(g)
    return tree_fill_(g, pt, rgf)


def collapse(t):
    key, children = t
    if not children:
        return key
    return ''.join([collapse(c) for c in children])

def display_tree(node, level=0, c='-'):
    key, children = node
    if children is None:
        print(' ' * 4 * level + c+'> ' + key)
    else:
        print(' ' * 4 * level + c+'> ' + key)
        for c in children:
            if isinstance(c, str):
                print(' ' * 4 * (level+1) + c)
            else:
                display_tree(c, level + 1, c='+')


grammar = {
    "<E>": [
            ["<E>", "+", "<T>"],       # Rule 1: E → E + T
            ["<T>"]                  # Rule 2: E → T
            ],        
    "<T>": [
            ["<T>", "*", "<F>"],       # Rule 3: T → T * F
            ["<F>"]                  # Rule 4: T → F
            ],           
    "<F>": [
            ["(", "<E>", ")"],       # Rule 5: F → ( E )
            ["a"]                  # Rule 6: F → a
            ]
}

start = "<E>"

test_cases = []
for path in k_paths(grammar, 20)[:10]:
    if path[0] in start: 
        tree = path_to_tree(path, grammar)
        for i in range(1):
            t = tree_fill(grammar, tree)
            s = collapse(t)

            test_cases.append((s, True))
        break



parsers = {
    # 'CYK',
    'GLL',
    # 'Earley',
    # 'Leo',
    'RNGLR'
}

results = benchmark(parsers, grammar, start, test_cases)


import csv

def print_results_table(results):
    # Print header
    # print("\n{:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10}".format(
    #     "Length", "Ambiguous", "Parser", "Time(s)", "Memory(MB)", "Edges", "Cells", "Nodes", "Ambiguous\nTrees"))
    # print("-" * 95)
    print("\n{:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10} {:<10}".format(
        "Length", "Ambiguous", "Parser", "Time(s)", "Memory(MB)", "Edges", "Cells", "Nodes", "Ambiguous\nTrees"))
    print("-" * 95)

    # Print rows
    for row in results:
        for parser_name, stats in row['parsers'].items():
            print("{:<10} {:<10} {:<10} {:<10.4f} {:<10.2f}".format(
                row['length'],
                str(row['ambiguous']),
                parser_name,
                stats['time'],
                stats['memory'] ,  # Convert bytes to MB
                # stats.get('edges', 'N/A'),
                # stats.get('cells', 'N/A'),
                # stats.get('nodes', 'N/A'),
                # stats['ambiguous_trees'])
            ))

def export_to_csv(results, filename="benchmark_results.csv"):
    with open(filename, 'w', newline='') as csvfile:
        fieldnames = ['length', 'ambiguous', 'parser', 'time', 'memory', 
                     'edges', 'cells', 'nodes', 'ambiguous_trees', 'success']
        writer = csv.DictWriter(csvfile, fieldnames=fieldnames)
        
        writer.writeheader()
        
        for row in results:
            for parser_name, stats in row['parsers'].items():
                writer.writerow({
                    'length': row['length'],
                    'ambiguous': row['ambiguous'],
                    'parser': parser_name,
                    'time': stats['time'],
                    'memory': stats['memory'],
                    # 'edges': stats.get('edges', ''),
                    # 'cells': stats.get('cells', ''),
                    # 'nodes': stats.get('nodes', ''),
                    # 'ambiguous_trees': stats['ambiguous_trees'],
                    # 'success': stats['success']
                })


print_results_table(results)
# export_to_csv(results)










#####################3




