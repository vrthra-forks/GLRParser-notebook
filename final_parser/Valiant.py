
import simplefuzzer as fuzzer

# We use the `display_tree()` method in earley parser for displaying trees.

# We use the chart display from cykparser
import final_parser.utility_parser.CYK as cykp

# We use the random choice to extract derivation trees from the parse forest.

import random

# As before, we use the [fuzzingbook](https://www.fuzzingbook.org) grammar style.
# A terminal symbol has exactly one character
# (Note that we disallow empty string (`''`) as a terminal symbol).
# Secondly, as per traditional implementations,
# there can only be one expansion rule for the start ymbol.

# Let us start with the following grammar.

g1 = {
    '<S>': [
          ['<X>', '<Y>']],
    '<X>': [
          ['<X>', '<A>'],
          ['<A>', '<A>']],
    '<Y>': [
          ['<Y>', '<B>'],
          ['<B>', '<B>']],
   '<A>': [['a']],
   '<B>': [['b']],
}
g1_start = '<S>'

# ## ValiantRecognizer
# We initialize our recognizer with the grammar, and identify the terminal and
# nonterminal productions separately. termiinal productions are those that
# are of the form `<A> ::= a` where a is a terminal symbol. Nonterminal
# productions are of the form `<A> ::= <B><C>` where `<B>` and `<C>` are
# nonterminal symbols.

class ValiantRecognizer(cykp.CYKRecognizer):
    def __init__(self, grammar):
        self.cache = {}
        self.cell_width = 5
        self.grammar = grammar
        self.productions = [(k,r) for k in grammar for r in grammar[k]]
        self.terminal_productions = [(k,r[0])
            for (k,r) in self.productions if fuzzer.is_terminal(r[0])]
        self.nonterminal_productions = [(k,r)
            for (k,r) in self.productions if not fuzzer.is_terminal(r[0])]

# ### Initialize the table
# We first initialize the matrix that holds the results. The `cell[i][j]`
# represents the nonterminals that can parse the substring `text[i..j]`
# Note that this table is exactly the same as what CYK produces.

class ValiantRecognizer(ValiantRecognizer):
    def init_table(self, text, length):
        return [[{} for i in range(length+1)] for j in range(length+1)]

class ValiantRecognizer(ValiantRecognizer):
    def parse_1(self, text, length, table):
        for s in range(0,length):
            for (key, terminal) in self.terminal_productions:
                if text[s] == terminal:
                    table[s][s+1][key] = True
        return table

def multiply_subsets(N1, N2, P):
    return {Ai:True for Ai, (Aj,Ak) in P if Aj in N1 and Ak in N2}


def multiply_matrices(A, B, P):
    m = len(A)
    C = [[{} for _ in range(m)] for _ in range(m)]
    for i in range(m):
        for j in range(m):
            for k in range(m):
                C[i][j] |= multiply_subsets(A[i][k], B[k][j], P)
    return C

# the corresponding cell in $$M_k$$ will be `true`, and `false` otherwise.
# We do the same for matrix $$b$$, getting $$2*h$$ boolean matrices.

def bool_matrices(A, nonterminals):
    m = len(A)
    M_ks = {nt: [[False for _ in range(m)] for _ in range(m)]
                       for nt in nonterminals}
    for i in range(m):
        for j in range(m):
            for nt in A[i][j]:
                M_ks[nt][i][j] = True

    return M_ks
 
# Let us call these $$M_k^a$$ and $$M_k^b$$ where $$k$$ indicates the nonterminal.
#  
# Next, we pair each matrix from $$M_k^a$$ and $$M_k^b$$ for each $$k \in N$$
# obtaining $$h^2$$ pairs, and compute the boolean matrix multiplication of each
# pairs. We address each as $$r(l,m)$$ where $$l \in N$$ and $$m \in N$$.

def multiply_pairs(bool_As, bool_Bs):
    r = {}
    for a_key in bool_As:
        r[a_key] = {}
        for b_key in bool_Bs:
            r[a_key][b_key] = multiply_bool_matrices(bool_As[a_key], bool_Bs[b_key])
    return r

# multiply two boolean matrices
def multiply_bool_matrices(A, B):
    m = len(A)
    C = [[False for _ in range(m)] for _ in range(m)]

    for i in range(m):
        for j in range(m):
            for k in range(m):
                if A[i][k] and B[k][j]:
                    C[i][j] = True
                    break
    return C

# In the final matrix $$c = a * b$$, for the cell $$c(i,j)$$ it will contain the
# nonterminal $$p \in N$$ iff there exist l,m such that a rule $$ p -> l m $$
# exists, and the matrix $$r(l,m)$$ contains $$1$$ in cell $$(i,j)$$.
  
def get_final_matrix(r, P, m):
    result = []
    for i in range(m):
        rows = []
        result.append(rows)
        for j in range(m):
            res = {Ai:True for Ai, (Aj,Ak) in P if r[Aj][Ak][i][j]}
            rows.append(res)
    return result

def multiply_matrices_b(A, B, P, nonterminals):
    length = len(A)
    bool_As = bool_matrices(A, nonterminals)
    bool_Bs = bool_matrices(B, nonterminals)
    r = multiply_pairs(bool_As, bool_Bs)
    res = get_final_matrix(r, P, length)
    return res

# ### Matrix union
# Next, we want to define how to make a union of two matrices

def union_matrices(A, B):
    C = [[{} for _ in range(len(A))] for _ in range(len(A))]
    for i in range(len(A)):
        for j in range(len(A)):
            for k in [l for l in A[i][j]] + [l for l in B[i][j]]:
                C[i][j][k] = True
    return C
# -- *parsable in i steps* -- can be computed using matrix multiplication.
# For a matrix $$ a^{(i)} $$, the relation is given by:
#  
#  $$a^{(i)} = U_{j=1}^{i-1} a^{(j)} * a^{(i-j)}$$ when $$ i > 1 $$
#   
#  $$a^{(1)} = a$$ when $$ i = 1 $$
#  
#  The intuition here is that if we have a 4 letter input, it may be parsed by
#  splitting into 1+3, 2+2, or 3+1. So, we compute
#  $$ a^{(1)}*a^{(3)} U a^{(2)}*a^{(2)} U a^{(3)}*a^{(1)} $$.
#   
#  At this point, we are ready to define the transitive relation.

class ValiantRecognizer(ValiantRecognizer):
    def parsed_in_steps(self, A, i, P):
        if i == 1: return A
        if (str(A), i) in self.cache: return self.cache[(str(A), i)]
        # 1 to i-1
        res = [[{} for _ in range(len(A))] for _ in range(len(A))]
        for j in range(1,i):
            a = self.parsed_in_steps(A, j, P)
            b = self.parsed_in_steps(A, i-j, P)
            #a_j = multiply_matrices(a, b, P)
            a_j = multiply_matrices_b(a, b, P, list(self.grammar.keys()))
            res = union_matrices(res, a_j)
        self.cache[(str(A), i)] = res
        return res

# We can now test it.
# step 2 `b1 = A(1)`

# ### Transitive closure
# Valiant further showed that the transitive closure of all these matrices,
# that is
#  
# $$ a^{+} = a^{(1)} U a^{(2)} ... $$
#  
# is the parse matrix.
# That is, building the transitive closure builds the complete parse chart.
# We can now check if the input was parsed.

class ValiantRecognizer(ValiantRecognizer):
    def transitive_closure(self, A, P, l):
        res = [[{} for _ in range(len(A))] for _ in range(len(A))]
        for i in range(1,l+1):
            a_i = self.parsed_in_steps(A, i, P)
            res = union_matrices(res, a_i)
        return res

# Tes
# Let us hook it up.
class ValiantRecognizer(ValiantRecognizer):
    def recognize_on(self, text, start_symbol):
        n = len(text)
        tbl = self.init_table(txt, n)
        my_A = self.parse_1(text, n, tbl)
        my_P = self.nonterminal_productions
        v = self.transitive_closure(my_A, my_P, n)
        return start_symbol in v[0][n]

# At this point, we have the *recognition matrix*. To make this into a true
# parser, similar to CYK, we can add back pointers. However, Ruzzo[^ruzzo1979on]
# showed that if we have the CYK or Valiant recognition matrix (both are same)
# we can extract a parse tree in at most $$ O(log(n))$$ slower than the recognizer.
# Here, we implement a naive algorithm that just shows how we can extract a
# single tree.
#  
# ### Extracting trees
# Unlike GLL, GLR, and Earley, and like
# CYK, due to restricting epsilons to the start symbol, there are no infinite
# parse trees. Furthermore, we only pick the first available tree. This can be
# trivially extended if needed.
#  
# The basic idea here is that, given a rule $$ S -> A B $$ that parsed text
# $$W$$, and we find $$S$$ in the recognition matrix, the nonterminal $$B$$ that
# helped in parsing $$W$$ has to be found in the same column as that of $$S$$.
# So, we look through the final column and generate a list of tuples where the
# tuple has the format `(idx, nonterminal)` where `idx` is the point where $$B$$
# started parsing from. At this point, if we look at the column `idx-1`, then at
# the top of the column (in 0th row) there has to be the nonterminal $$A$$ that
# is on the other side of the rule.

def find_breaks(table, sym, P):
    rules = [(l, (m, n)) for (l, (m, n)) in P if l == sym]
    # get the last column.
    if not table: return [] # terminal symbol
    m = len(table)
    last_column = [row[m-1] for row in table]
    assert sym in last_column[0]

    # Now, identify the index, and nonterminal
    tuples = []
    for idx, cell in enumerate(last_column):
        for k in cell: # cell is {k:true}*
            tuples.append((idx, k))
    # remove start symbol
    B_tuples = [(idx, k) for (idx,k) in tuples if k != sym or idx != 0]
    A_tuples = []
    for idx, B_k in B_tuples:
        B_rules = [(d, (l, r)) for d,(l,r) in rules if r == B_k]
        A_cell_ = table[0][idx]
        A_rules = [(idx, (l, r)) for d,(l,r) in B_rules if l in A_cell_]
        if A_rules: # we found a parse.
            A_tuples.extend(A_rules)

    return A_tuples

class ValiantParser(ValiantRecognizer):
    def extract_tree(self, table, sym, text):
        length = len(table)
        possible_breaks = find_breaks(table, sym, self.nonterminal_productions)
        if not possible_breaks: return [sym, [(text, [])]]
        c_j, (A_j, B_j) = random.choice(possible_breaks)

        l_table = [[table[i][j] for j in range(c_j+1)]
                   for i in range(c_j+1)]

        r_table = [[table[i][j] for j in range(c_j, length)]
                   for i in range(c_j, length)]

        l = self.extract_tree(l_table, A_j, text[0:c_j])

        r = self.extract_tree(r_table, B_j, text[c_j:])
        return [sym, [l, r]]

# ### Parse
# Adding the extract tree

class ValiantParser(ValiantParser):
    def parse_on(self, text, start_symbol):
        length = len(text)
        table = self.init_table(text, length)
        my_A = self.parse_1(text, length, table)
        my_P = self.nonterminal_productions
        ntable = self.transitive_closure(my_A, my_P, length)
        if start_symbol not in ntable[0][-1]: return []
        return [self.extract_tree(ntable, start_symbol, text)]

