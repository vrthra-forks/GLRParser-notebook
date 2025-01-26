import copy
import time
from graphviz import Digraph

import cProfile
profiler = cProfile.Profile()
profiler.enable()




class GSSNode:
    def __init__(self, state, label_count):
        self.count = label_count
        self.state = state  # Parser state
        self.successor = []  # List of edges to successor nodes

    def add_link(self, successor, link):
        """Add an edge to a predecessor node."""
        self.successor.append((successor, link))

    def __repr__(self):
        repr = f"GSSNode(v{self.count}) - State: {self.state} - Children:"
        for child in self.successor:
            repr += f"\n        ~ GSSNode(v{child[0].count}) - Link({child[1].label})"

        return repr


class GSS:
    def __init__(self):
        self.label_count = 0
        self.nodes = {}  # Map v_number -> GSSNode


    def create_node(self, state):
        new_node = GSSNode(state, self.label_count)
        self.nodes[self.label_count] = new_node
        self.label_count += 1
        return new_node
    
    # def __repr__(self):
    #     repr = f"GSSTree:"
    #     for node in self.nodes.values():
    #         repr += f"\n - {node}"
    #     return repr

    # def dfs(self, node, depth):
    #     print(f"DEPTH {depth} {node.state}")
    #     if depth == 0:
    #         return {node}

    #     reachable = set()
    #     for successor, link in node.successor:
    #         reachable |= self.dfs(successor, depth - 1)
    #     return reachable

    # def find_node_path_length(self, start, length):
    #     # Find all nodes reachable from `start` with a path of a specific length.
    #     return self.dfs(start, length)
    

    # def path_exists(self, start, end, length):
    #     # Check if a path of a specific length exists between `start` and `end`.
    #     reachable_nodes = self.find_node_path_length(start, length)
    #     return end in reachable_nodes

    # def dfs_through_link(self, node, depth, through_link):
    #     if depth == 0:
    #         if through_link == True:
    #             return {node}
    #         return set()


    #     reachable = set()
    #     for successor, link in node.successor_edges:
    #         if link == through_link:
    #             through_link = True
    #         reachable |= self.dfs_through_z(successor, depth - 1, through_link)
    #     return reachable

    # def find_node_through_link(self, start, length, through_link):
    #     # Find all nodes reachable from `start` with a path of a specific length.
    #     return self.dfs(start, length, through_link)
    
    def find_paths_link_length_m(self, v, m):
        def dfs_link(current_node, path):
            # If the path length reaches m, add to results
            if len(path) == m:
                paths.add(tuple(path + [current_node]))
                return
            
            # Recur for all neighbors
            for node, link in current_node.successor:
                dfs_link(node, path + [link])

        paths = set()
        dfs_link(v, [])  # Start DFS with the initial vertex
        return paths
        # paths = set()
        # stack = [(v, [])]  # (current_node, current_path)
        # while stack:
        #     current_node, path_links = stack.pop()
        #     if len(path_links) == m:
        #         paths.add(tuple(path_links + [current_node]))
        #         continue
        #     for successor, link in current_node.successor:
        #         stack.append((successor, path_links + [link]))
        # return paths


class SPPFNode:
    def __init__(self, label, start_position=None):
        self.label = label #list of lable
        self.start_position = start_position
        self.children = []
        self.root_candidate = True


    def add_child(self, child):
        if child not in self.children:
            self.children.append(child)


    def remove_all_children(self):
        self.children = []


    def check_exist_children_sequence(self, A):
        if not self.children:
            return False
        
        if any(isinstance(child, PackingNode) for child in self.children):
            for child in self.children:
                for i in range(len(child.edges) - len(A) + 1):
                    if child.edges[i:i + len(A)] == A:
                        return True
                    
        else:
            for i in range(len(self.children) - len(A) + 1):
                if self.children[i:i + len(A)] == A:
                    return True
        return False

    def __repr__(self):
        return f"SPPFNode({self.label}, {self.start_position})"
    

class PackingNode:
    def __init__(self):
        self.edges = []

    def add_edge(self, node):
        self.edges.append(node)

    def __repr__(self):
        return f"PackingNode({self.edges})"


# class SPPF:
#     def __init__(self):
#         self.nodes = []
    
#     def create_node(self, label, start_position):
#         new_node = SPPFNode(label, start_position)
#         self.nodes.append(new_node)
#         return new_node


def compute_nullable_parts(grammar):
    nullable = set()
    productions = {nt: list(rules) for nt, rules in grammar.items()}

    # Step 1: Compute nullable non-terminals using fixed-point iteration
    changed = True
    while changed:
        changed = False
        for nt, rules in productions.items():
            for rule in rules:
                if all(sym == "epsilon" for sym in rule) and nt not in nullable:
                    nullable.add(nt)
                    changed = True

    
    return nullable



def build_epsilon_sppf(grammar):
    """
    Builds epsilon-SPPF trees for non-trivial nullable suffixes of grammar rules,
    with keys as integers.

    Args:
        grammar (dict): Grammar rules as a dictionary.

    Returns:
        epsilon_sppf (dict): Maps numeric keys to \(\epsilon\)-SPPF root nodes.
    """
    nullable = compute_nullable_parts(grammar)
    epsilon_sppf = {}
    epsilon_sppf[0] = SPPFNode(("ε"))
    node_counter = 1  # Unique counter for keys

    # Step 1: Create epsilon-SPPF trees for nullable non-terminals
    for nt in nullable:
        node = SPPFNode(tuple(nt))
        node.add_child(epsilon_sppf[0])
        epsilon_sppf[node_counter] = node
        node_counter += 1

    # Map single nullable symbols to their assigned numeric keys
    count_map = len(nullable)
    nullable_key_map = {nt: key for key, nt in enumerate(nullable, 1)}
    # print(nullable_key_map)

    # Step 2: Build epsilon-SPPF trees for non-trivial nullable suffixes
    changes = True
    while changes:
        changes = False
        for nt, rules in grammar.items():

            for rule in rules:
                # Collect nullable suffixes
                nullable_suffix = []
                for sym in reversed(rule):
                    if sym in nullable:
                        nullable_suffix.insert(0, sym)
                        # Only process non-trivial nullable suffixes (length > 1)
                        if len(nullable_suffix) > 1:
                            suffix_key = tuple(nullable_suffix)

                            existed = False
                            for node in epsilon_sppf.values():
                                if suffix_key == node.label:
                                    existed = True
                                    break

                            if not existed:
                                # Build an \(\epsilon\)-SPPF tree for this suffix
                                root = SPPFNode((suffix_key))
                                for part in nullable_suffix:
                                    root.add_child(epsilon_sppf[nullable_key_map[part]])
                                epsilon_sppf[node_counter] = root

                                nullable |= set(suffix_key)
                                node_counter += 1
                                changes = True
                        
                        if len(nullable_suffix) == len(rule):
                            suffix_key = tuple(nt)

                            existed = False
                            for node in epsilon_sppf.values():
                                if suffix_key == node.label:
                                    existed = True
                                    break

                            if not existed:
                                # Build an \(\epsilon\)-SPPF tree for this suffix
                                nullable |= set(suffix_key)
                                root = SPPFNode((suffix_key))
                                nullable_key_map[nt] = count_map
                                count_map += 1

                                for node in epsilon_sppf.values():
                                    if nullable_suffix == list(node.label):       
                                        root.add_child(node)

                                epsilon_sppf[node_counter] = root
                                node_counter += 1
                                changes = True
                    else:
                        break  # Stop if a non-nullable symbol is found

    return epsilon_sppf


def function_I(epsilon_sppf, A, alpha, nullable_string):
    if len(alpha) == 0:
        for key in epsilon_sppf.keys():
            node = epsilon_sppf[key]
            if list(A) == list(node.label):
                return key
    else:
        if len(nullable_string) == 0:
            return 0
        for key in epsilon_sppf.keys():
            node = epsilon_sppf[key]
            if list(nullable_string) == list(node.label):
                return key


class RNParseTableConstructer:
    def __init__(self, input_grammar, start):
        """
        Initialize the LRParser with a given grammar.

        Args:
            input_grammar (dict): A dictionary defining the context-free grammar (CFG).
        """
        # Initialize parameters of the CFG
        self.grammar = {}
        self.start = start
        self.terminals = []
        self.non_terminals = []
        self.dot = "·"
        self.formattingGrammar(input_grammar)

        self.epsilon_sppf = build_epsilon_sppf(input_grammar)
        self.gss = GSS()

        self.first_table = {}
        self.in_progress = set()     # this variable is used to avoid left recursive when calculating first
        self.calculateFirstTable()
        
        self.augmented_rules = []  # Format: [(lhs, [rhs], lookahead)]
        self.state_dict = {}       # States: (format: state_count: [[rule1], [rule2], ...])
        self.state_map= {}         # Transitions: {(state, symbol): new_state}
        self.state_count = 0
        self.addDot()
        self.generateStates()

        self.parse_table = []
        self.createParseTable()


    def formattingGrammar(self, input_grammar):
        """
        Processes the input grammar into an internal representation for the parser.

        This method reformats the provided input grammar into a format suitable 
        for parsing and initializes the grammar rules, start symbol, non-terminals, 
        and terminals. The first rule in the input grammar is augmented to create 
        a new start rule.

        Args:
            input_grammar (dict): The input grammar represented as a dictionary 
                where keys are non-terminals and values are lists of production rules.

        Attributes Modified:
            self.grammar (dict)
            self.start (str)
            self.non_terminals (list)
            self.terminals (list)
        """
        # Process the input grammar into a dictionary with each rule have the format of
        # key: rulenumber (int) 
        # value: [lhs (str), rhs (list of symbol)]
        count = 0
        for key in input_grammar.keys():
            # Augment the first rule
            if count == 0:
                self.start = f"{key}'"
                self.grammar[0] = (self.start, [key])
                count += 1

            # Process each rule into the format above
            for rule in input_grammar[key]:
                if rule == ["epsilon"]:
                    self.grammar[count] = (key, [])
                else:
                    self.grammar[count] = (key, rule)
                count += 1

        # Detecting terminals and non-terminals symbols if it was not given
        if len(self.terminals) == 0 and len(self.non_terminals) == 0:
            for key in self.grammar.keys():
                lhs, rhs = self.grammar[key]
                if lhs not in self.non_terminals:
                    self.non_terminals.append(lhs)
            for key in self.grammar.keys():
                lhs, rhs = self.grammar[key]
                for sym in rhs:
                    if sym not in self.terminals and sym not in self.non_terminals:
                        if sym != "epsilon":
                            self.terminals.append(sym)


    def addDot(self):
        """
        Adding a dot (·) (tracker of process of parsing) at the start of each production's RHS.
        """
        for key in self.grammar.keys():
            lhs, rhs = self.grammar[key]
            new_rhs = [self.dot] + rhs
            self.augmented_rules.append((lhs, new_rhs, "$"))

    def calculateFirstTable(self):
        """
        Compute the FIRST table for the grammar.
        """
        for key in self.grammar.keys():
            rule = self.grammar[key]
            lhs, rhs = rule

            if lhs not in self.first_table:
                self.first_table[lhs] = self.first(lhs)
            else:
                self.first_table[lhs] != self.first(lhs)

    def generateStates(self):
        """
        Generate all states for the parser, starting with the initial state.
        """
        # generate and calculate the closure of the initial state I_0
        first_state = self.augmented_rules[0]
        closure_rules = self.findClosure([first_state])
        complete_state = self.add_lookahead([first_state], closure_rules)
        self.state_dict[0] = complete_state

        # generate states until no more state is able to be generated
        prev_len = -1
        state_completed_GOTO = []
        while prev_len != len(self.state_dict):
            prev_len = len(self.state_dict)
            for state in list(self.state_dict.keys()):
                if state not in state_completed_GOTO:
                    self.computeGOTO(state)
                    state_completed_GOTO.append(state)

    
    def computeGOTO(self, state):
        """
        Check and manage states that need to compute GOTO transitions

        Args:
            state (int): The state number.
        """
        generate_new_state_for = []
        for rule in self.state_dict[state]:
            # if the rule ends with dot (can't shift anymore) => skip
            if rule[1][-1] == self.dot:
                continue

            dot_ind = rule[1].index(self.dot)
            next_sym = rule[1][dot_ind+1]

            if next_sym not in generate_new_state_for:
                generate_new_state_for.append(next_sym)

        for sym in generate_new_state_for:
            self.GOTO(state, sym)

    
    def GOTO(self, state, sym):
        """
        Compute the GOTO transitions for a given state.

        Args:
            state (int): The current state.
            sym (str): The grammar symbol.
        """
        new_state = []
        for rule in self.state_dict[state]:
            lhs, rhs, lookahead = rule
            # if the rule ends with dot (can't shift anymore) => skip
            if rhs[-1] == self.dot:
                continue

            dot_ind = rhs.index(self.dot)
            next_sym = rhs[dot_ind+1]

            # shift operation from the previous state of rule on that
            if next_sym == sym:
                # swap dot with next_sym
                new_rhs = copy.copy(rhs)
                new_rhs[dot_ind], new_rhs[dot_ind + 1] = new_rhs[dot_ind + 1], new_rhs[dot_ind]
                new_state.append((lhs, new_rhs, lookahead))


        closure_rules = self.findClosure(copy.copy(new_state))
        complete_state = self.add_lookahead(new_state, closure_rules)


        # check if state exist
        state_exists = -1
        for state_num in self.state_dict:

            if self.state_dict[state_num] == complete_state:
                state_exists = state_num
                break
     
        # stateMap is a mapping of GOTO with
        # its output states
        if state_exists == -1:
            self.state_count += 1
            self.state_dict[self.state_count] = complete_state
            self.state_map[(state, sym)] = self.state_count
        else:
            self.state_map[(state, sym)] = state_exists


    def first_str(self, string):
        res = set()
        for char in string:
            if char in self.terminals or char == "$":
                first_set = set([char])
            else:
                first_set = self.first_table[char]
            res |= first_set
            if "epsilon" not in first_set:
                break

        if "epsilon" in res:
            res.remove("epsilon")
        return res
            
    
    def first(self, sym):
        # rule for terminals
        if sym in self.terminals or sym == "$":
            return set([sym])
            
        # rule for epsilon
        elif sym == "epsilon":
            return set(["epsilon"])
    

        # rule for non-terminal
        else:
            if sym in self.in_progress:
                return set()  # prevent infinite recursion
            # mark this non-terminal as being processed
            self.in_progress.add(sym)


            res = set()
            for key in self.grammar.keys():
                lhs, rhs = self.grammar[key]
                if sym == lhs:
                    if rhs == []:
                        res.add("epsilon")
                    for s in rhs:
                        first_s = self.first(s)
                        res |= first_s

                        if "epsilon" not in first_s:
                            if "epsilon" in res:
                                res.remove("epsilon")
                            break
            self.in_progress.remove(sym)  # finished processing this non-terminal
            return res
            

    def findClosure(self, closure_rules):
        original_state = copy.copy(closure_rules)

        follow = {}

        for nt in self.non_terminals:
            follow[nt] = set()

        prev_len = -1
        while prev_len != len(closure_rules):
            prev_len = len(closure_rules)
            for lhs, rhs, lookahead in closure_rules:
                if rhs[-1] == self.dot:
                    continue
                    
                dot_ind = rhs.index(self.dot)
                next_sym = rhs[dot_ind+1]
    
                # if next_sym is non_terminal then continue adding augmented rule with that nonterminals as lhs
                # new lookahead is FIRST of the string after that nonterminal + old lookahead
                if next_sym in self.non_terminals:
                    for i, augmented_rule in enumerate(self.augmented_rules):
                        if augmented_rule[0] == next_sym:
                            if augmented_rule in original_state:
                                if augmented_rule in closure_rules:
                                    continue
                                closure_rules.append(augmented_rule)
                            # if a new create item for the closure -> need to calculate new lookahead
                            else:
                                new_nt = rhs[dot_ind+1]
                                if new_nt not in self.non_terminals:
                                    continue

                                if dot_ind + 2 < len(rhs):
                                    follow[new_nt] |= self.first_str(rhs[dot_ind+2:] + [lookahead])
                                else:
                                    follow[new_nt] |= set([lookahead])
                                for new_lookahead in follow[new_nt]:
                                    if (augmented_rule[0], augmented_rule[1], new_lookahead) in closure_rules:
                                        continue
                                    closure_rules.append((augmented_rule[0], augmented_rule[1], new_lookahead))

        return closure_rules
    
    def add_lookahead(self, orignal_state, closure_rules):
        follow = {}

        for lhs, rhs, lookahead in closure_rules:
            follow[lhs] = set()




        for nt in self.non_terminals:
            for lhs, rhs, lookahead in closure_rules:
                if rhs[-1] == self.dot:
                    continue
                if nt == lhs:
                    dot_ind = rhs.index(self.dot)
                    new_nt = rhs[dot_ind+1]
                    if new_nt not in self.non_terminals:
                        continue

                    if dot_ind + 2 < len(rhs):
                        follow[new_nt] |= self.first_str(rhs[dot_ind+2:] + [lookahead])

                    else:
                        follow[new_nt] |= set([lookahead])

        
        complete_state = []
        for lhs, rhs, lookahead in closure_rules:
            if (lhs, rhs, lookahead) in orignal_state:
                complete_state.append((lhs, rhs, lookahead))
            else:
                for new_lookahead in follow[lhs]:
                    if (lhs, rhs, new_lookahead) not in complete_state:
                        complete_state.append((lhs, rhs, new_lookahead))
        return complete_state
    

    def createParseTable(self):
        """
        Create the parsing table for the SLR(1) parser.
        """
        rows = list(self.state_dict.keys())
        cols = self.terminals + ["$"] + self.non_terminals

        # create empty table
        temp_row = []
        for i in range(len(cols)):
            temp_row.append([])
        for i in range(len(rows)):
            self.parse_table.append(copy.deepcopy(temp_row))

        # add shift and goto entries to table
        for entry in self.state_map.keys():
            state = entry[0]
            sym = entry[1]

            row_ind = rows.index(state)
            col_ind = cols.index(sym)

            if sym in self.terminals or sym in self.non_terminals:
                if ("p", self.state_map[entry]) not in self.parse_table[row_ind][col_ind]:
                    self.parse_table[row_ind][col_ind].append(("p", self.state_map[entry]))


        # add reduce to table
        for state in self.state_dict.keys():
            for lhs, rhs, lookahead in self.state_dict[state]:
                # if the rule is a handle -> add reduce correspondingly
                if rhs[-1] == self.dot:
                    copy_rhs = copy.copy(rhs)
                    copy_rhs.remove(self.dot)

                    for rule_num in self.grammar.keys():
                        if self.grammar[rule_num][0] == lhs and self.grammar[rule_num][1] == copy_rhs:
                            row_ind = rows.index(state)
                            if rule_num == 0:
                                col_ind = cols.index("$")
                                self.parse_table[row_ind][col_ind].append(("acc"))
                            else:
                                f = function_I(self.epsilon_sppf, lhs, copy_rhs, "")
                                col_ind = cols.index(lookahead)
                                if ("r", (lhs, len(copy_rhs), f)) not in self.parse_table[row_ind][col_ind]:
                                    self.parse_table[row_ind][col_ind].append(("r", (lhs, len(copy_rhs), f)))
                
                # if the part after dot is nullable, then also add reduce
                else:
                    dot_ind = rhs.index(self.dot)
                    for key in self.epsilon_sppf.keys():
                        node = self.epsilon_sppf[key]
                        # print(rhs[dot_ind+1:], list(node.label))
                        if rhs[dot_ind+1:] == list(node.label):
                            copy_rhs = copy.copy(rhs)
                            copy_rhs.remove(self.dot)


                            for rule_num in self.grammar.keys():
                                if self.grammar[rule_num][0] == lhs and self.grammar[rule_num][1] == copy_rhs:
                                    row_ind = rows.index(state)
                                    if rule_num == 0:
                                        col_ind = cols.index("$")
                                        self.parse_table[row_ind][col_ind].append(("acc"))
                                    else:
                                        alpha = rhs[:dot_ind]
                                        nullable_string = rhs[dot_ind+1:]
                                        f = function_I(self.epsilon_sppf, lhs, alpha, nullable_string)
                                        col_ind = cols.index(lookahead)
                                        if ("r", (lhs, len(alpha), f)) not in self.parse_table[row_ind][col_ind]:
                                            print(row_ind, lookahead, ("r", (lhs, len(alpha), f)))
                                            self.parse_table[row_ind][col_ind].append(("r", (lhs, len(alpha), f)))
                            break

                    ### if the rest if the string is nullable -> add reduce


    	# printing table
        print("\nParsing table:\n")
        frmt = "{:>12}" * len(cols)
        print(" ", frmt.format(*cols), "\n")
        ptr = 0
        j = 0
        for y in self.parse_table:
            # frmt1 = "{:>8}"
            print(f"{{:>3}}".format('I'+str(j)), end="")
            for e in y:
                list_opp = []
                for opp in e:
                    word = ""
                    word += opp[0]
                    if len(opp) > 0:
                        if type(opp[1]) is int:
                            word += str(opp[1])
                        else:
                            for s in opp[1]:
                                word += str(s)
                    list_opp.append(word)
                print(f"{{:>12}}".format("/".join(list_opp)), end="")
            print()
            j += 1

        # print("-------------------------------------------------------------------")
        # for y in self.parse_table:
        #     for e in y:
        #         if e:
        #             print(e, end="  ")
        # print("\n")

    # def printResultAndGoto(self):
    #     print("\nStates Generated:\n")
    #     for st in self.state_dict:
    #         print(f"State = I{st}")
    #         self.printResult(self.state_dict[st])
    #         print()

    #     print("\nResult of GOTO computation:\n")
    #     self.printAllGOTO(self.state_map)


    # def printResult(self, rules):
    #     for rule in rules:
    #         print(f"{rule[0]} -> {' '.join(rule[1])} , {rule[2]}")

    # def printAllGOTO(self, diction):
    #     for itr in diction:
    #         print(f"GOTO ( I{itr[0]} , {itr[1]} ) = I{self.state_map[itr]}")

    

class RNGLRParser():
    def __init__(self, grammar, non_terminals, terminals, start, parse_table, epsilon_sppf, start_state=0, accept_state=1): 
        self.grammar = grammar
        self.non_terminals = non_terminals
        self.terminals = terminals
        self.symbols = self.terminals + ["$"] + self.non_terminals
        self.start = start

        self.parse_table = self.load_parse_table(parse_table)
        self.epsilon_sppf = epsilon_sppf

        self.start_state = start_state
        self.accept_state = accept_state

        self.gss = GSS()
        self.sppf = []
        self.sppf_root = None

        self.U = {}
        self.R = {}
        self.Q = []
        self.N = []

        self.a = []
        self.result = False


        self.count_viz = 0


    def load_parse_table(self, parse_table):
        parse_table_dict = {}
        header = self.terminals + ["$"] + self.non_terminals

        state = 0
        for row in parse_table:
            for col, value in enumerate(row):
                if value:
                    parse_table_dict[(state, header[col])] = value
            state += 1
        return parse_table


    def parse(self, input_string):
        """

        """
        # if isinstance(input_string, str):
        #     input_string = list(input_string)
        if len(input_string) == 0:
            operations = self.parse_table[self.start_state][self.symbols.index("$")]
            for operation in operations:
                if operation == ("acc"):
                    self.result = True

        else:
            n = len(input_string)
            v0 = self.gss.create_node(state=self.start_state)
            for i in range(n+2):
                self.U[i] = []
                self.R[i] = []
            self.U[0] = [v0]
            self.Q = []
            self.a = input_string + ["$"]


            operations = self.parse_table[self.start_state][self.symbols.index(self.a[0])]
            for operation in operations:
                if operation[0] == "p":
                    self.Q.append((v0, int(operation[1])))
                elif operation[0] == "r":
                    X, m, f = operation[1]
                    if m == 0:
                        self.R[0].append((v0, X, 0, f, self.epsilon_sppf[0]))  # self.epsilon_sppf[0] is epsilon node
            
            for i in range(n+1):
                while True:

                    self.N = []
                    while self.R[i]:
                        self.reducer(i)
                    self.shifter(i)

                    if not self.R[i]:
                        break

            for u in self.U[n]:
                if u.state == self.accept_state:
                    # print("\n")
                    # print(self.start, v0.state)

                    for node in self.sppf:
                        # print(node.label, node.start_position)
                        if node.label == (self.start.strip("\'")) and node.start_position == v0.state:
                            if node.root_candidate:
                                self.sppf_root = node


                    self.result = True

        return self.result
    
    def visualize_sppf(self, filename="sppf_graph"):
        """
        Visualizes the SPPF structure with Graphviz, showing:
        - SPPF nodes (ovals) with their labels and start positions
        - Packing nodes (rectangles) for ambiguous parses
        - Connections between all node types
        """
        from graphviz import Digraph

        dot = Digraph()
        dot.attr(rankdir='LR')  # Left-to-right layout for parse trees
        processed = set()

        # Create nodes with different styles for SPPF vs Packing nodes
        for node in self.sppf:
            # print(node, str(id(node)))
            node_id = str(id(node))
            
            # SPPF Node styling
            label = ', '.join(node.label) if node.label else 'ε'
            if node.start_position is not None:
                label += f'\nStart: {node.start_position}'
            dot.node(node_id, label=label, shape='oval', style='filled', 
                    fillcolor='#E0E0E0' if node.label != ('ε',) else '#FFE0B2')

        # Create edges and handle packing nodes
        packing_nodes = set()
        for node in self.sppf:
            print("***", node, node.children)
            node_id = str(id(node))
            for child in node.children:
                if isinstance(child, SPPFNode):
                    print(child, str(id(child)))

                    # Direct SPPF node connection
                    dot.edge(node_id, str(id(child)))
                elif isinstance(child, PackingNode):
                    # Packing node connection
                    packing_id = f"pack_{id(child)}"
                    if packing_id not in packing_nodes:
                        dot.node(packing_id, label="PackingNode", shape='rectangle', 
                                style='filled', fillcolor='#BBDEFB')
                        packing_nodes.add(packing_id)
                    
                    # Connect parent to packing node
                    dot.edge(node_id, packing_id)
                    
                    # Connect packing node to its children
                    for edge_node in child.edges:
                        print(edge_node, str(id(edge_node)))
                        print(edge_node.children)

                        dot.edge(packing_id, str(id(edge_node)))

        # # Add legend
        # with dot.subgraph(name='cluster_legend') as legend:
        #     legend.attr(label='Legend', style='dashed')
        #     legend.node('legend_spff', 'SPPF Node\n(label, start pos)', shape='oval', 
        #             fillcolor='#E0E0E0', style='filled')
        #     legend.node('legend_pack', 'Ambiguity Point', shape='rectangle',
        #             fillcolor='#BBDEFB', style='filled')
        #     legend.node('legend_eps', 'ε Node', shape='oval', 
        #             fillcolor='#FFE0B2', style='filled')
        #     legend.attr(rank='same')

        # Render and save
        dot.render(filename, format='png', cleanup=True)
        print(f"SPPF visualization saved to {filename}.png")

    def reducer(self, i):
        v, X, m, f, y = self.R[i].pop(0)

        if m == 0:
            all_path = self.gss.find_paths_link_length_m(v, 0)
            # next_sym_ind = i

        else:
            all_path = self.gss.find_paths_link_length_m(v, m-1)
            # next_sym_ind = i+1


        if m != 0:
            w_m = y

        for path_link in all_path:
            u = path_link[-1]
            list_w = []
            for link in reversed(path_link[:-1]):
                list_w.append(link)

            if m != 0:
                list_w.append(w_m)

            k = u.state
            operations = self.parse_table[k][self.symbols.index(X)]
            for operation in operations:
                if operation[0] == "p":
                    l = int(operation[1])

            if m == 0:
                z = self.epsilon_sppf[f]
                self.add_node_to_sppf(z)

            else:
                z_exists = False
                c = self.find_U_i_with_node(u)
                # print("FINDING Z")
                # for node in self.epsilon_sppf.values():
                #     print(node.label, node.start_position)       

                for node in self.N:
                    if node.label == (X) and node.start_position == c:
                        z = node
                        z_exists = True

                if not z_exists:
                    z = SPPFNode(X, c)
                    self.sppf.append(z)    
                    self.N.append(z)

            # if m == 0:
            w = self.find_node_in_U_i_with_label(i, l)
            # else:
            #     w = self.find_node_in_U_i_with_label(i+1, l)

            if w:
                if not self.exist_edge_from_w_to_u(w, u):
                    w.add_link(u, z)
                    if m != 0:
                        operations = self.parse_table[l][self.symbols.index(self.a[i])]
                        for operation in operations:
                            if operation[0] == "r":
                                B, t, f_next = operation[1]
                                if t != 0:
                                    self.R[i].append((u, B, t, f_next, z))

            else:
                w = self.gss.create_node(l)
                # if m == 0:
                self.U[i].append(w)
                # else:
                #     self.U[i+1].append(w)
                w.add_link(u, z)

                operations = self.parse_table[l][self.symbols.index(self.a[i])]
                for operation in operations:
                    if operation[0] == "p":
                        self.Q.append((w, int(operation[1])))                    
                    elif operation[0] == "r":
                        B, t, f_next = operation[1]
                        if t == 0:
                            self.R[i].append((w, B, t, f_next, self.epsilon_sppf[0]))  # self.epsilon_sppf[0] is epsilon node

                if m != 0:
                    operations = self.parse_table[l][self.symbols.index(self.a[i])]
                    for operation in operations:
                        if operation[0] == "r":
                            B, t, f_next = operation[1]
                            if t != 0:
                                self.R[i].append((u, B, t, f_next, z))

            if m != 0:
                self.add_children(z, list_w, f)



    
    def shifter(self, i):
        Q_prime = []

        z_exists = False
        for node in self.sppf:
            if node.label == (self.a[i]) and self.start == i:
                z = node
                z_exists = True

        if not z_exists:
            z = SPPFNode([self.a[i]], i)
            self.sppf.append(z)

        while self.Q:
            v, k = self.Q.pop()

            w = None
            for node in self.U[i+1]:
                if node.state == k:
                    w = node
            
            if w:
                w.add_link(v, z)

                operations = self.parse_table[k][self.symbols.index(self.a[i+1])]
                for operation in operations:
                    if operation[0] == "r":
                        B, t, f = operation[1]
                        if t != 0:
                            self.R[i+1].append((v, B, t, f, z))

            else:
                w = self.gss.create_node(k)
                w.add_link(v, z)
                self.U[i+1].append(w)

                operations = self.parse_table[k][self.symbols.index(self.a[i+1])]
                for operation in operations:
                    if operation[0] == "p":
                        Q_prime.append((w, int(operation[1])))
                    elif operation[0] == "r":
                        B, t, f = operation[1]
                        if t == 0:
                            self.R[i+1].append((w, B, t, f, self.epsilon_sppf[0]))  # self.epsilon_sppf[0] is epsilon node
                        else:
                            self.R[i+1].append((v, B, t, f, z))  # self.epsilon_sppf[0] is epsilon node


        self.Q = Q_prime.copy()




    def add_children(self, y, list_w, f):
        if f == 0:
            A = list_w
        else:
            A = list_w
            A.append(self.epsilon_sppf[f])

        if not y.children:
            for v in A:
                if v not in y.children:
                    y.add_child(v)
                    v.root_candidate = False

                if v not in self.sppf:
                    self.sppf.append(v)

        elif not y.check_exist_children_sequence(A):
            if not any(isinstance(child, PackingNode) for child in y.children):
                z = PackingNode()
                for child in y.children:
                    z.add_edge(child)
                    child.root_candidate = False

                y.remove_all_children()
                y.add_child(z)
            
            t = PackingNode()
            y.add_child(t)

            for v in A:
                t.add_edge(v)
                v.root_candidate = False

                # if v not in self.sppf:
                self.sppf.append(v)


    def find_node_in_U_i_with_label(self, i, l):
        for node in self.U[i]:
            if node.state == l:
                return node
    
    def exist_edge_from_w_to_u(self, w, u):
        for successor, link in w.successor:
            if successor == u:
                return True
        return False
    
    def find_U_i_with_node(self, node):
        for i in self.U.keys():
            if node in self.U[i]:
                return i
            
    def add_node_to_sppf(self, new_node):
        for node in self.sppf:
            if new_node.label == node.label and new_node.start_position == node.start_position:
                return node
        else:
            self.sppf.append(new_node)
            for child in new_node.children:
                self.add_node_to_sppf(child)
            

    


# grammar = {
#     "S": [["E"]],
#     "E": [["E", "+", "E"], ["E", "*", "E"], ["id"]]
# }
# start = "S"
# grammar = {
#         "S": [["a", "S", "B", "B"]],
#         "B": [["b"], ["epsilon"]]
# }

# start = "S"

# grammar = {
#     "E": [["E", "+", "T"], ["T"]],
#     "T": [["T", "*", "F"], ["F"]],
#     "F": [["(", "E", ")"], ["id"]]
# }
# start = "E"
# # Test the Parser
# t = RNParseTableConstructer(grammar, start)
# parser = RNGLRParser(t.grammar, t.non_terminals, t.terminals, t.start, t.parse_table, t.epsilon_sppf)


# print(t.epsilon_sppf)
# input_string = ["id", "+", "id", "*", "id"]
# parser.parse(input_string)

# parser.visualize_sppf(filename="my_parse_tree")
# t.printResultAndGoto()



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

t = RNParseTableConstructer(grammar, start)
parser = RNGLRParser(t.grammar, t.non_terminals, t.terminals, t.start, t.parse_table, t.epsilon_sppf)

for path in k_paths(grammar, 5):
    if path[0] in start: 
        tree = path_to_tree(path, grammar)
        for i in range(1):
            t = tree_fill(grammar, tree)
            s = collapse(t)

            parser.parse(list(s))

profiler.disable()
profiler.print_stats(sort="time")