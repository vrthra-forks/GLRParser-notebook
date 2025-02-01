# import pandas as pd
import final_parser.RNGLR as rnglr
# from final_parser.LRs import add_start_state
# from final_parser.LRs import LR0DFA, SLR1DFA, LR1DFA, LALR1DFA
# from final_parser.LRs import LR0Parser, SLR1Parser, LR1Parser, LALR1Parser
import final_parser.Earley as earley
import final_parser.CYK as cyk
import final_parser.GLL as gll
import final_parser.Valiant as valiant


import time
import random
import tracemalloc
from collections import defaultdict
import traceback
import sys
import csv 
import os
maxInt = sys.maxsize

while True:
    # decrease the maxInt value by factor 10 
    # as long as the OverflowError occurs.
    try:
        csv.field_size_limit(maxInt)
        break
    except OverflowError:
        maxInt = int(maxInt/10)




def benchmark(parsers, grammar, start, test_cases, export_path):
    results = {name: {'length': [], 'time': [], 'memory': []} for name in parsers}

    for test_no, test_str in enumerate(test_cases):
        for name in parsers:
            if name == "GLL":
                gll_parser = gll.compile_grammar(grammar)
            elif name == "Valiant":
                valiant_parser = valiant.ValiantParser(grammar)
            elif name == "CYK":
                cyk_parser = cyk.CYKParser(grammar)
            elif name == "Earley":
                earley_parser = earley.EarleyParser(grammar)
            elif name == "RNGLR":
                rnglr_parser = rnglr.RNGLRParser(start, export_path, grammar)
            
            
            try:
                if name == "GLL":
                    start_time = time.perf_counter()
                    tracemalloc.start()

                    gll_result = gll_parser.recognize_on(test_str, start)
                    ee = gll.EnhancedExtractor(gll_result)
                    while True:
                        t = ee.extract_a_tree()
                        if t is None: break

                    parse_time = time.perf_counter() - start_time
                    memory_peak = tracemalloc.get_traced_memory()[1]
                    tracemalloc.stop()

                elif name == "Valiant":
                    start_time = time.perf_counter()
                    tracemalloc.start()

                    v = valiant_parser.parse_on(test_str, start)
                    for t in v:
                        pass

                    parse_time = time.perf_counter() - start_time
                    memory_peak = tracemalloc.get_traced_memory()[1]
                    tracemalloc.stop()

                elif name == "CYK":
                    start_time = time.perf_counter()
                    tracemalloc.start()

                    cyk_result = cyk_parser.parse_on(test_str, start)
                    for t in cyk_result:
                        pass

                    parse_time = time.perf_counter() - start_time
                    memory_peak = tracemalloc.get_traced_memory()[1]
                    tracemalloc.stop()

                elif name == "Earley":
                    start_time = time.perf_counter()
                    tracemalloc.start()

                    ee = earley.EnhancedExtractor(earley_parser, test_str, start)
                    while True:
                        t = ee.extract_a_tree()
                        if t is None: break

                    parse_time = time.perf_counter() - start_time
                    memory_peak = tracemalloc.get_traced_memory()[1]
                    tracemalloc.stop()

                elif name == "RNGLR":
                    # import cProfile
                    # profiler = cProfile.Profile()
                    # profiler.enable()
                    start_time = time.perf_counter()
                    tracemalloc.start()

                    rnglr_root, res = rnglr_parser.parse(list(test_str))
                    ee = rnglr.EnhancedExtractor(rnglr_root)
                    while True:
                        t = ee.extract_a_tree()
                        if t is None: break

                    parse_time = time.perf_counter() - start_time
                    memory_peak = tracemalloc.get_traced_memory()[1]
                    tracemalloc.stop()

                    # profiler.disable()
                    # profiler.print_stats(sort="time")


                results[name]['length'].append(len(test_str))
                results[name]['time'].append(parse_time)
                results[name]['memory'].append(memory_peak)
                

            except Exception as e:
                traceback.print_exc()
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



import csv

def print_grammar(grammar, start, property):
    """
    Prints the grammar rules in a human-readable format.

    Args:
        grammar (dict): Grammar rules in the given format.
        start (str): The start symbol of the grammar.
    """
    print(f"\n{property}")
    print(f"Start Symbol: {start}")
    print("Grammar Rules:")
    for non_terminal, productions in grammar.items():
        # Join productions for the same non-terminal with " | "
        production_strings = []
        for production in productions:
            if not production:  # Empty production
                production_strings.append("ε")
            else:
                production_strings.append(" ".join(production))
        print(f"  {non_terminal} → {' | '.join(production_strings)}")


def print_results_table(results):
    # print("\n{:<10} {:<15} {:<15} {:<15} {:<15} {:<15}".format(
    #      "Parser", "Avg Length", "Avg Time(s)", "Min Time(s)", "Max Time(s)", "Avg Memory(MB)"))
    # print("-" * 85)

    # for parser_name, stats in results.items():
    #     if not stats['time']:  # If no successful results, skip
    #         continue
        
    #     avg_len = sum(stats['length']) / len(stats['length'])
    #     avg_time = sum(stats['time']) / len(stats['time'])
    #     min_time = min(stats['time'])
    #     max_time = max(stats['time'])
    #     avg_memory = sum(stats['memory']) / len(stats['memory']) / (1024 * 1024)

    #     print("{:<10} {:<15.1f} {:<15.4f} {:<15.4f} {:<15.4f} {:<15.2f}".format(
    #         parser_name, avg_len, avg_time, min_time, max_time, avg_memory))
        
    print("\n{:<10} {:<15} {:<15} {:<10}".format(
         "Parser", "Input Length", "Time(s)", "Avg Memory(MB)"))
    print("-" * 60)

    for parser_name, stats in results.items():
        if not stats['time']:  # If no successful results, skip
            continue
        
        avg_len = sum(stats['length']) / len(stats['length'])
        avg_time = sum(stats['time']) / len(stats['time'])
        min_time = min(stats['time'])
        max_time = max(stats['time'])
        avg_memory = sum(stats['memory']) / len(stats['memory']) / (1024 * 1024)

        print("{:<10} {:<15.0f} {:<15.4f} {:<10.4f}".format(
            parser_name, avg_len, avg_time, avg_memory))
        

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

def test0():
    def remove_whitespace(json_str):
        return [char for char in json_str if char not in " \t\n\r"]

    grammar = {
        "<json>": [["<object>"], ["<array>"]],

        "<object>": [["{", "<members>", "}"], ["{", "}"]],
        "<members>": [["<pair>"], ["<pair>", ",", "<members>"]],
        "<pair>": [["<string>", ":", "<value>"]],

        "<array>": [["[", "<elements>", "]"], ["[", "]"]],
        "<elements>": [["<value>"], ["<value>", ",", "<elements>"]],

        "<value>": [
            ["<string>"],
            ["<number>"],
            ["<object>"],
            ["<array>"],
            ["true"],
            ["false"],
            ["null"]
        ],

        "<string>": [["\"", "<characters>", "\""]],
        "<characters>": [["<character>", "<characters>"], []],  # ε (empty string)
        
        "<character>": [["%s" % chr(i)] for i in range(32, 127) if i not in [34, 92]],  # Excluding '"' (34) and '\' (92)

        "<number>": [["<integer>", "<fraction>", "<exponent>"]],
        "<integer>": [["-", "<digit>", "<digits>"], ["<digit>", "<digits>"]],
        "<fraction>": [[".", "<digit>", "<digits>"], []],  # ε (optional fraction)
        "<exponent>": [["e", "<sign>", "<digit>", "<digits>"], ["E", "<sign>", "<digit>", "<digits>"], []],  # ε (optional exponent)
        "<sign>": [["+"], ["-"], []],  # ε (optional sign)

        "<digits>": [["<digit>", "<digits>"], []],  # ε (empty or sequence of digits)
        "<digit>": [["%s" % str(i)] for i in range(10)]  # Generates ["0"], ["1"], ..., ["9"]
    }
    start = "<json>"
    property = "JSON Grammar"

    parsers = {
        # 'Valiant',
        # 'CYK',
        # 'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    # json_test1 = """
    # {
    #     "name": "Alice",
    #     "age": 25,
    #     "address": {
    #         "street": "123 Main St",
    #         "city": "Wonderland",
    #         "zip": "12345"
    #     },
    #     "phones": ["+1234567890", "+0987654321"],
    #     "preferences": {
    #         "notifications": "false",
    #         "theme": "dark"
    #     },
    #     "history": [
    #         {"date": "2024-01-01", "action": "login"},
    #         {"date": "2024-01-02", "action": "purchase"}
    #     ]
    # }
    # """
    json_test1 = """
    {
        "name": "Alice",
        "age": 25,
        "address": {
            "street": "123 Main St",
            "city": "Wonderland",
            "zip": "12345"
        }
    }
    """
    # print(remove_whitespace(json_test1))
    test_cases.append("".join(remove_whitespace(json_test1)))

    # rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark1.csv"
    # rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)

def test1():
    grammar = {
        '<S>': [['<A>', '<B>'],
              ['<B>', '<C>'],
              ['<A>', '<C>'],
              ['c']],
       '<A>': [
            ['<B>', '<C>'],
            ['a']],
       '<B>': [
            ['<A>', '<C>'],
            ['b']],
       '<C>': [
            ['c']],
    }
    start = '<S>'
    property = "Normal Grammar"

    parsers = {
        # 'Valiant',
        # 'CYK',
        'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 100

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark2.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)



def test2():
    grammar = {
        "<E>": [["<E>", "+", "<T>"], ["<T>"]],        
        "<T>": [["<T>", "*", "<F>"], ["<F>"]],           
        "<F>": [["(", "<E>", ")"], ["a"]]
    }
    start = "<E>"
    property = "Highly Ambiguous Grammar"

    parsers = {
        # 'Valiant',
        # 'CYK',
        'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 5

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark3.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)
    print_grammar(grammar, start, property)
    print_results_table(results)


def test3():
    grammar = {
        "<S>": [["<A>"], ["<B>"]],
        "<A>": [["a", "<A>", "b"], []],
        "<B>": [["a", "<B>", "b"], []]
    }
    start = "<S>"
    property = "Ambiguous Grammar with Nullable Non-terminals"

    parsers = {
        # 'Valiant',
        # 'CYK',
        # 'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 100

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark4.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)


def test4():
    grammar = {
        "<S>": [["<S>", "a"], ["a"]]
    }
    start = "<S>"
    property = "Left Recursive Grammar"

    parsers = {
        # 'Valiant',
        # 'CYK',
        'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 100

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark5.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)


def test5():
    grammar = {
        "<S>": [["a", "<S>", "b"], ["a"], []]
    }
    start = "<S>"
    property = "Grammar with Non-Determinism"

    parsers = {
        # 'Valiant',
        # 'CYK',
        # 'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 100

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark6.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)


def test6():
    grammar = {
        "<S>": [["a", "<S>"], ["a"]]
    }
    start = "<S>"
    property = "Right Recursive Grammar"

    parsers = {
        # 'Valiant',
        # 'CYK',
        'GLL',
        'Earley',
        'RNGLR'
    }

    test_cases = []
    count = 0
    k_path_depth = 100

    for path in k_paths(grammar, k_path_depth):
        if path[0] in start:

            tree = path_to_tree(path, grammar)
            t = tree_fill(grammar, tree)
            s = collapse(t)

            if count == 3:
                break
            count += 1

            t = tree_fill(grammar, tree)
            s = collapse(t)
            test_cases.append((s))

    rntable = rnglr.RNParseTableConstructer(grammar, start)
    export_path = "tables/benchmark7.csv"
    rntable.export_to_csv(export_path)
    results = benchmark(parsers, grammar, start, test_cases, export_path)

    print_grammar(grammar, start, property)
    print_results_table(results)


test0()
test1()
test2()
test3()
test4()
test5()
test6()
