import simplefuzzer as fuzzer
import random
from typing import NewType

Grammar = NewType('Grammar', dict[str, list[list[str]]])
Table = NewType('Table', list[list[dict]])

class CYKRecognizer():
    def __init__(self, grammar: Grammar):
        self.grammar = grammar
        self.productions = [(k,r) for k in grammar for r in grammar[k]]
        self.cell_width = 5 

        # let us get an inverse cache
        self.terminal_rules = {}
        self.nonterminal_rules = {}
        for k, rule in self.productions:
            if fuzzer.is_terminal(rule[0]):
                if k not in self.terminal_rules:
                    if rule[0] not in self.terminal_rules:
                        self.terminal_rules[rule[0]] = []
                self.terminal_rules[rule[0]].append(k)
            else:
                if k not in self.nonterminal_rules:
                    self.nonterminal_rules[(rule[0],rule[1])] = []
                self.nonterminal_rules[(rule[0],rule[1])].append(k)


class CYKRecognizer(CYKRecognizer):
    def init_table(self, text, length) -> Table:
        res = [[{} for i in range(length+1)] for j in range(length+1)]
        # this is just for demonstration of which lterals are invloved.
        # You can remove the loop
        for i in range(length):
            res[i][i] = {text[i]: text[i]}
        return res

# Let us define a printing routine.
class  CYKRecognizer(CYKRecognizer):
    def print_table(self, table):
        row_size = len(table[0])
        for i, row_ in enumerate(table):
            row = {i:list(cell.keys()) for i,cell in enumerate(row_)}
            # f"{value:{width}.{precision}}"
            rows = [row]
            while rows:
                row, *rows = rows
                s = f'{i:<2}'
                remaining = {}
                for j in range(row_size):
                    if j in row: ckeys = row[j]
                    else: ckeys = []
                    if len(ckeys) == 0:
                        r = ''
                        s += f'|{r:>{self.cell_width}}'
                    elif len(ckeys) >= 1:
                        r = ckeys[0]
                        s += f'|{r:>{self.cell_width}}'
                        remaining[j] = ckeys[1:]
                print(s + '|')
                # construct the next row
                nxt_row = {}
                for k in remaining:
                    if remaining[k]:
                        nxt_row[k] = remaining[k]
                if nxt_row: rows.append(nxt_row)
            #
            print('  |'+'_____|'*row_size)



class CYKRecognizer(CYKRecognizer):
    def parse_1(self, text, length, table):
        for s in range(0,length):
            for key in self.terminal_rules[text[s]]:
                table[s][s+1][key] = True
        return table



class CYKRecognizer(CYKRecognizer):
    def parse_n(self, text, n, length, table):
        # check substrings starting at s, with length n
        for s in range(0, length-n+1):
            # partition the substring at p (n = 1 less than the length of substring)
            for p in range(1, n):
                pairs = [(b,c) for b in table[s][s+p] for c in table[s+p][s+n]]
                matching_pairs = [(b,c) for (b,c) in pairs
                            if (b,c) in self.nonterminal_rules]
                keys = {k:True for pair in matching_pairs
                               for k in self.nonterminal_rules[pair]}
                table[s][s+n].update(keys)
        return table



class CYKRecognizer(CYKRecognizer):
    def recognize_on(self, text, start_symbol):
        length = len(text)
        table = self.init_table(text, length)
        self.parse_1(text, length, table)
        for n in range(2,length+1): # n is the length of the sub-string
            self.parse_n(text, n, length, table)
        return start_symbol in table[0][-1]


def is_nt(k):
    return (k[0], k[-1]) == ('<', '>')

def rem_terminals(g):
    g_cur = {}
    for k in g:
        alts = []
        for alt in g[k]:
            ts = [t for t in alt if not is_nt(t)]
            if not ts:
                alts.append(alt)
        if alts:
            g_cur[k] = alts
    return g_cur

def nullable(g):
    nullable_keys = {k for k in g if [] in g[k]}

    unprocessed  = list(nullable_keys)

    g_cur = rem_terminals(g)
    while unprocessed:
        nxt, *unprocessed = unprocessed
        g_nxt = {}
        for k in g_cur:
            g_alts = []
            for alt in g_cur[k]:
                alt_ = [t for t in alt if t != nxt]
                if not alt_:
                    nullable_keys.add(k)
                    unprocessed.append(k)
                    break
                else:
                    g_alts.append(alt_)
            if g_alts:
                g_nxt[k] = g_alts
        g_cur = g_nxt

    return nullable_keys



def extend_chain(guarantee_1):
    # initialize it with the first level parent
    chains = {k:set(guarantee_1[k]) for k in guarantee_1}
    while True:
        modified = False
        for k in chains:
            # for each token, get the guarantees, and add it to current
            for t in list(chains[k]):
                for v in chains[t]:
                    if v not in chains[k]:
                        chains[k].add(v)
                        modified = True
        if not modified: break
    return chains

def identify_gauranteed_parses(grammar):
    guarantee_1 = {k:[] for k in grammar}
    nullable_keys = nullable(grammar)
    for k in grammar:
        for r in grammar[k]:
            if len(r) == 0: continue
            if len(r) == 1: continue
            # <A>:k := <B> <C>
            b, c = r
            if b in nullable_keys:
                # parsing with c guarantees parsing with A
                guarantee_1[c].append(k)
            if c in nullable_keys:
                # parsing with b guarantees parsing with A
                guarantee_1[b].append(k)
    return extend_chain(guarantee_1)

class CYKRecognizer(CYKRecognizer):
    def __init__(self, grammar):
        self.grammar = grammar
        self.productions = [(k,r) for k in grammar for r in grammar[k]]
        self.cell_width = 5 

        # let us get an inverse cache
        self.terminal_rules = {}
        self.nonterminal_rules = {}
        for k, rule in self.productions:
            if not rule: continue # empty
            if fuzzer.is_terminal(rule[0]):
                if k not in self.terminal_rules:
                    self.terminal_rules[rule[0]] = []
                self.terminal_rules[rule[0]].append(k)
            else:
                if k not in self.nonterminal_rules:
                    self.nonterminal_rules[(rule[0],rule[1])] = []
                self.nonterminal_rules[(rule[0],rule[1])].append(k)

        self.chains = identify_gauranteed_parses(grammar)

    def parse_1(self, text, length, table):
        for s in range(0,length):
            table[s][s+1] = {key:True for key in self.terminal_rules[text[s]]}
            for k in list(table[s][s+1]):
                table[s][s+1].update({v:True for v in self.chains[k]})
        return table

    def parse_n(self, text, n, length, table):
        # check substrings starting at s, with length n
        for s in range(0, length-n+1):
            # partition the substring at p (n = 1 less than the length of substring)
            for p in range(1, n):
                matching_pairs = [
                        (b,c) for b in table[s][s+p] for c in table[s+p][s+n]
                            if (b,c) in self.nonterminal_rules]
                keys = {k:True for pair in matching_pairs
                               for k in self.nonterminal_rules[pair]}
                table[s][s+n].update(keys)

        for s in range(0, length-n+1):
            for k in list(table[s][s+n]):
                # for each key, add the chain.
                table[s][s+n].update({v:True for v in self.chains[k]})
        return table


def replace_terminal_symbols(grammar):
    new_g = {}
    for k in grammar:
        new_g[k] = []
        for r in grammar[k]:
            new_r = []
            new_g[k].append(new_r)
            for t in r:
                if fuzzer.is_terminal(t):
                    nt = '<_' + t + '>'
                    new_g[nt] = [[t]]
                    new_r.append(nt)
                else:
                    new_r.append(t)
    return new_g


# Next, we want to replace any rule that contains more than two tokens with
# it decomposition.
# [] = []
# [t1] = [t1]
# [t1, t2] = [t1, t2]
# [t1, t2, t3] = [t1, _t2], _t2 = [t2, t3]

def decompose_rule(rule, prefix):
    l = len(rule)
    if l in [0, 1, 2]: return rule, {}
    t, *r = rule
    kp = prefix + '_'
    nr, d = decompose_rule(r, kp)
    k = '<' + kp + '>'
    d[k] = [nr]
    return [t, k], d


def decompose_grammar(grammar):
    new_g = {}
    for k in grammar:
        new_g[k] = []
        for i,r in enumerate(grammar[k]):
            nr, d = decompose_rule(r, k[1:-1] + '_' + str(i))
            new_g[k].append(nr)
            new_g.update(d)
    return new_g

# all that remains now is to ensure that each rule is exactly two
# token nonterminal, or a single token terminal.
def is_newterminal(k):
    return k[1] == '_'

def balance_grammar(grammar):
    new_g = {}
    for k in grammar:
        if is_newterminal(k):
            assert len(grammar[k]) == 1
            new_g[k] = grammar[k]
            continue
        new_g[k] = []
        for r in grammar[k]:
            l = len(r)
            if l == 0:
                new_g[k].append([])
            elif l == 1:
                new_g[k].append([r[0]])
            elif l == 2:
                new_g[k].append(r)
            else:
                assert False
    return new_g

def remove_unit_rules(g: Grammar):
    new_g = {}

    # for every non-terminal k
    for k in g:
        visited = set()
        queue = [k]
        new_g[k] = []

        while len(queue) > 0:
            top = queue.pop()
            if top in visited:
                continue
            visited.add(top)

            for production in g[top]:
            # Is a unit rule
                if len(production) == 1 and fuzzer.is_nonterminal(production[0]):
                    queue.append(production[0])
                else:
                    new_g[k].append(production)

    return new_g

# connecting everything together

def cfg_to_cnf(g: Grammar):
    g1 = replace_terminal_symbols(g)
    g2 = decompose_grammar(g1)
    g3 = balance_grammar(g2)
    g4 = remove_unit_rules(g3)
    return g4



class CYKParser(CYKRecognizer):
    def __init__(self, grammar: Grammar):
        self.cell_width = 5 
        self.grammar = grammar
        self.productions = [(k,r) for k in grammar for r in grammar[k]]
        self.terminal_productions = [(k,r[0])
            for (k,r) in self.productions if fuzzer.is_terminal(r[0])]
        self.nonterminal_productions = [(k,r)
            for (k,r) in self.productions if not fuzzer.is_terminal(r[0])]


class CYKParser(CYKParser):
    def parse_1(self, text, length, table):
        for s in range(0,length):
            for (key, terminal) in self.terminal_productions:
                if text[s] == terminal:
                    if key not in table[s][s+1]:
                        table[s][s+1][key] = []
                    table[s][s+1][key].append((key, [(text[s], [])]))
        return table


class CYKParser(CYKParser):
    def parse_n(self, text, n, length, table):
        for s in range(0, length-n+1):
            for p in range(1, n):
                for (k, [R_b, R_c]) in self.nonterminal_productions:
                    if R_b in table[s][s+p]:
                        if R_c in table[s+p][s+n]:
                            if k not in table[s][s+n]:
                                table[s][s+n][k] = []
                            table[s][s+n][k].append(
                                (k,[table[s][s+p][R_b], table[s+p][s+n][R_c]]))


class CYKParser(CYKParser):
    def trees(self, forestnode):
        if forestnode:
            if isinstance(forestnode, list):
                key, children = random.choice(forestnode)
            else:
                key,children = forestnode
            ret = []
            for c in children:
                t = self.trees(c)
                ret.append(t)
            return (key, ret)

        return None

    def parse_on(self, text: str, start_symbol: str):
        length = len(text)
        table = self.init_table(text, length)
        self.parse_1(text, length, table)
        for n in range(2,length+1):
            self.parse_n(text, n, length, table)
        return [self.trees(table[0][-1][start_symbol])]

