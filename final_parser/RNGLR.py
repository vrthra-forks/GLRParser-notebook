import copy
import os
import csv
# from graphviz import Digraph
# from utility_parser.rnglr_utility import GSSNode, GSS, SPPFNode, PackingNode, function_I, build_epsilon_sppf, EnhancedExtractor, format_parsetree

import cProfile
profiler = cProfile.Profile()
profiler.enable()




class RNParseTableConstructer:
    def __init__(self, input_grammar, start):
        """
        Setting up the parameters for the construction of RN parse table

        Args:
            input_grammar (dict): A dictionary defining the context-free grammar (CFG).
            start (str): The start symbol of the grammar.
        """
        # Initialize parameters of the CFG
        self.grammar = {}
        self.start = start
        self.terminals = []
        self.non_terminals = []
        self.dot = "·"

        self.format_grammar(input_grammar)
        self.epsilon_sppf = build_epsilon_sppf(input_grammar)  # Builds epsilon SPPF of the grammar 
        self.gss = GSS()  # Graph-structured stack
        
        self.first_table = {}
        self.in_progress = set()  # Used to avoid left recursion when calculating FIRST sets
        self.calculate_first_table()
        
        self.augmented_rules = []  # Format: [(lhs, [rhs], lookahead)]
        self.state_dict = {}  # Rules in each state. Format - {state_count: [[rule1], [rule2], ...]}
        self.state_map = {}  # Transition between states. Format - {(state, symbol): new_state}
        self.state_count = 0
        
        self.add_dot()
        self.generate_states()
        
        self.parse_table = []
        self.create_parse_table()


    def formattingGrammar(self, input_grammar):
        """
        Processes the input grammar into an internal representation for the parser.

        This method reformats the provided input grammar into a format suitable 
        for parsing and initializes the grammar rules, start symbol, non-terminals, 
        and terminals. The first rule in the input grammar is augmented to create 
        a new start rule.

        Args:
            input_grammar (dict): A dictionary defining the context-free grammar (CFG).

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

        # calculate the closure of that state
        closure_rules = self.findClosure(copy.copy(new_state))
        # add lookahead accordingly to each rule in that state
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
        """
        Compute the FIRST set of a given string.

        Args:
            string (str): The given string
        """
        res = set()
        for char in string:
            if char in self.terminals or char == "$":
                first_set = set([char])
            else:
                first_set = self.first_table[char]
            res |= first_set

            # if the current symbol's first set is nullable, then the first set of the string
            # need to include the first set of the next symbol
            if "epsilon" not in first_set:
                break

        if "epsilon" in res:
            res.remove("epsilon")
        return res
            
    
    def first(self, sym):
        """
        Compute the FIRST set of a given symbol.

        Args:
            sym (str): The given symbol
        """
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
        """
        Compute the closure set of set of rules.

        Args:
            closure_rules (str): The given set of rules.
        """
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
        """
        Add new valid lookahead symbol to the set of closure rules given.

        Args:
            closure_rules (str): The given set of rules.
        """
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


                    # lookahead set is the follow set of the remainng part of the rule after the non_terminals after dot 
                    if dot_ind + 2 < len(rhs):
                        follow[new_nt] |= self.first_str(rhs[dot_ind+2:] + [lookahead])

                    else:
                        follow[new_nt] |= set([lookahead])

        
        complete_state = []
        for lhs, rhs, lookahead in closure_rules:
            # if the closure rules exist in the original state - state before calculating closure
            # then we don't need to add new lookahead
            if (lhs, rhs, lookahead) in orignal_state:
                complete_state.append((lhs, rhs, lookahead))

            # else we add new lookahead to the rule using the lookahead set calculated above
            else:
                for new_lookahead in follow[lhs]:
                    if (lhs, rhs, new_lookahead) not in complete_state:
                        complete_state.append((lhs, rhs, new_lookahead))
        
        return complete_state
    

    def createParseTable(self):
        """
        Finally, assemble the parsing RN table
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
                        if ''.join(rhs[dot_ind+1:]) == node.label:
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
                                            self.parse_table[row_ind][col_ind].append(("r", (lhs, len(alpha), f)))
                            break



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


    def printResultAndGoto(self):
        print("\nStates Generated:\n")
        for st in self.state_dict:
            print(f"State = I{st}")
            self.printResult(self.state_dict[st])
            print()

        print("\nResult of GOTO computation:\n")
        self.printAllGOTO(self.state_map)


    def printResult(self, rules):
        for rule in rules:
            print(f"{rule[0]} -> {' '.join(rule[1])} , {rule[2]}")

    def printAllGOTO(self, diction):
        for itr in diction:
            print(f"GOTO ( I{itr[0]} , {itr[1]} ) = I{self.state_map[itr]}")

    def export_to_csv(self, filepath):
        """
        Export parsing table to csv file

        Args:
            filepath (string): path of the csv file that user want to write to

        """
        rows = list(self.state_dict.keys())
        cols = self.terminals + ["$"] + self.non_terminals

        # Create directories if they don't exist
        if not os.path.exists(os.path.dirname(filepath)):
            os.makedirs(os.path.dirname(filepath)) 

        # saving the parse table to a csv file
        with open(filepath, "w") as file:
            file.write("state,"+",".join(cols)+"\n")
            j = 0
            for i, y in enumerate(self.parse_table):
                list_opp = [str(i)]
                for e in y:
                    entry = ""
                    count = 0
                    for opp in e:
                        if opp == 'acc':
                            entry += 'acc'
                        else:
                            entry += opp[0] + "."
                            if len(opp) > 0:
                                # p format ('p', 4)
                                if type(opp[1]) is int:
                                    entry += str(opp[1]) + "."
                                # r format ('r' ('E', 3, 0))
                                else:
                                    for s in opp[1]:
                                        entry += str(s) + "."
                        if count < len(e) - 1:
                            entry += "/"
                        count += 1
                    list_opp.append(entry)

                file.write(",".join(list_opp) + "\n")
                j += 1

    

class RNGLRParser():
    def __init__(self, start, filepath, input_grammar, start_state=0, accept_state=1): 
        # Initialize parameters of the CFG
        self.grammar = {}
        self.start = start
        self.terminals = []
        self.non_terminals = []


        self.formattingGrammar(input_grammar)
        self.symbols = self.terminals + ["$"] + self.non_terminals

        
        self.parse_table = self.load_parse_table(filepath)
        self.epsilon_sppf = build_epsilon_sppf(input_grammar)   # Builds epsilon SPPF of the grammar 

        self.start_state = start_state
        self.accept_state = accept_state

        self.gss = GSS() # Graph-structured stack
        self.sppf = {}  # Share Packed Parse Forest   
        self.sppf_root = None

        self.U = {}
        self.reverse_U = {} # hash table to quickly find frontier in U of a node
        self.R = {}
        self.Q = []
        self.N = {}

        self.a = []
        self.result = False



    def parse_entry_csv(self, entry):
        if not entry:  # Empty entry
            return []
        elif '/' in entry:  # Multiple entries
            return [self.parse_entry_csv(e)[0] for e in entry.split('/')]
        elif entry == 'acc':
            return ['acc']
        elif entry.startswith('p'):  # 'p' entry
            e = entry.split(".")
            return [('p', int(e[1]))]
        elif entry.startswith('r'):  # 'r' entry
            e = entry.split(".")
            return [('r', (e[1], int(e[2]), int(e[3])))]
        else:
            return entry  # Default case (header values, etc.)
        
    def parse_table_from_csv(self, filepath):
        """
        Read RN parse table from csv file and return it in list format

        Args:
            filepath (string): Filepath of the csv file

        """
        result = [] 
        with open(filepath, 'r') as file:
            lines = file.read().splitlines()

            for line in lines[1:]:  # Skip first row
                row = line.split(",")  # Manually split by comma
                parsed_row = [self.parse_entry_csv(entry) for entry in row[1:]]  # Skip first entry of each row
                result.append(parsed_row)

        return result

    def load_parse_table(self, filepath):
        """
        Convert RN table in list format to dictionary format
        Format: Key - (Current state, Next symbol)
                Value - List of operations

        Args:
            filepath (string): Filepath of the csv file

        """
        parse_table = self.parse_table_from_csv(filepath)
        parse_table_dict = {}
        header = self.terminals + ["$"] + self.non_terminals

        state = 0
        for row in parse_table:
            for col, value in enumerate(row):
                if value:
                    parse_table_dict[(state, header[col])] = value
            state += 1
        return parse_table

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

    def parse(self, input_string):
        """
        Parse function (reference to pseudocode by Generalised LR parsing algorithms - Giorgios Robert Economopoulos)
        """
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
            self.reverse_U[v0.count] = 0
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

                    self.N = {}
                    while self.R[i]:
                        self.reducer(i)
                    self.shifter(i)

                    if not self.R[i]:
                        break
            for u in self.U[n]:
                if u.state == self.accept_state:
                    self.result = True
                    self.sppf_root = self.sppf.get((self.start.strip("\'"), v0.state))
        return self.sppf_root, self.result
    

    def reducer(self, i):
        """
        Reducer function (reference to pseudocode by Generalised LR parsing algorithms - Giorgios Robert Economopoulos)
        """
        v, X, m, f, y = self.R[i].pop(0)

        # Case m = 0: nullable non-terminal
        if m == 0:
            all_path = self.gss.find_paths_link_length_m(v, 0)
        else:
            all_path = self.gss.find_paths_link_length_m(v, m-1)

        # for all possible path from v that have length = m - which is reducable
        for path_link in all_path:
            # u is the last node of the path
            u = path_link[-1]

            # list_w will be the list of the link connectin v to u
            list_w = []
            for link in reversed(path_link[:-1]):
                list_w.append(link)

            if m != 0:
                list_w.append(y)

            k = u.state
            operations = self.parse_table[k][self.symbols.index(X)]
            for operation in operations:
                if operation[0] == "p":
                    l = int(operation[1])

            # if nullable non-terminal, then simply add that non-terminal from epsilon sppf to the tree sppf
            if m == 0:
                z = self.epsilon_sppf[f]
                self.add_node_to_sppf(z)

            # if not nullable non-terminal rule, then create new sppf node accordingly
            else:
                c = self.find_U_i_with_node(u)
                z = self.N.get((X, c))

                if not z:
                    z = SPPFNode(X, c)
                    self.sppf[(X, c)] = z
                    self.N[(X, c)] = z

            w = self.find_node_in_U_i_with_label(i, l)
            # if w already exist in the Ui frontier then just need to add link
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

            # else w not exist in the Ui frontier then create new node and add link
            else:
                w = self.gss.create_node(l)
                self.U[i].append(w)
                self.reverse_U[w.count] = i
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
        """
        Shifter function (reference to pseudocode by Generalised LR parsing algorithms - Giorgios Robert Economopoulos)
        """
        Q_prime = []

        z = self.sppf.get((self.a[i], i))

        if not z:
            z = SPPFNode(self.a[i], i)
            self.sppf[(self.a[i], i)] = z

        while self.Q:
            v, k = self.Q.pop()

            w = None
            for node in self.U[i+1]:
                if node.state == k:
                    w = node
            
            # if the node to be shifted exist, then just need to add new link to it
            if w:
                w.add_link(v, z)

                operations = self.parse_table[k][self.symbols.index(self.a[i+1])]
                for operation in operations:
                    if operation[0] == "r":
                        B, t, f = operation[1]
                        if t != 0:
                            self.R[i+1].append((v, B, t, f, z))

            # if the node to be shifted doesn't exist, then create new node andadd new link to it
            else:
                w = self.gss.create_node(k)
                w.add_link(v, z)
                self.U[i+1].append(w)
                self.reverse_U[w.count] = i+1


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
        """
        Add_chidlren function (reference to pseudocode by Generalised LR parsing algorithms - Giorgios Robert Economopoulos)
        """
        if f == 0:
            A = list_w
        else:
            A = list_w
            A.append(self.epsilon_sppf[f])

        # if y doesn't have any children then add them and mark them as unable to be root candidate and existed in sppf
        if not y.children:
            for v in A:
                if v not in y.children:
                    y.add_child(v)
                    v.root_candidate = False

                if not self.sppf.get((v.label, v.start_position)):
                    self.sppf[(v.label, v.start_position)] = v

        # if y has any children, check if the children sequence exist or not
        # if not exist, then create a new PackingNode for the new sequence of children
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

                if not self.sppf.get((v.label, v.start_position)):
                    self.sppf[(v.label, v.start_position)] = v


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
        return self.reverse_U[node.count]

    def add_node_to_sppf(self, new_node):
        node = self.sppf.get((new_node.label, new_node.start_position))
        if not node:
            self.sppf[new_node.label, new_node.start_position] = new_node
            for child in new_node.children:
                self.add_node_to_sppf(child)
        return node
            
class GSSNode:
    '''
    GSSNode, including the count of the node in the GSS Tree
    Each node's successor is a tuple of the successor node, and the link between it
    In this program, the link between nodes is an edge, represented by a SPPF Node
    '''
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
    '''
    GSS Tree of multiple GSS node, storing the label count to uniquely identify each node when required
    '''
    def __init__(self):
        self.label_count = 0
        self.nodes = {}  # Map v_number -> GSSNode


    def create_node(self, state):
        new_node = GSSNode(state, self.label_count)
        self.nodes[self.label_count] = new_node
        self.label_count += 1
        return new_node
    
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


class SPPFNode:
    '''
    SPPFNode include start position and its children
    Node's children is a list of other SPPFNode
    '''
    def __init__(self, label, start_position=None,):
        self.label = label
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
    epsilon_sppf[0] = SPPFNode("ε")
    node_counter = 1  # Unique counter for keys

    # Step 1: Create epsilon-SPPF trees for nullable non-terminals
    for nt in nullable:
        node = SPPFNode(nt)
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
                                if ''.join(suffix_key) == node.label:
                                    existed = True
                                    break

                            if not existed:
                                # Build an \(\epsilon\)-SPPF tree for this suffix
                                root = SPPFNode(''.join(suffix_key))
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
                                if ''.join(suffix_key) == node.label:
                                    existed = True
                                    break

                            if not existed:
                                # Build an \(\epsilon\)-SPPF tree for this suffix
                                nullable |= set(suffix_key)
                                root = SPPFNode(''.join(suffix_key))
                                nullable_key_map[nt] = count_map
                                count_map += 1

                                for node in epsilon_sppf.values():
                                    if ''.join(nullable_suffix) == node.label:       
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
            if A == node.label:
                return key
    else:
        if len(nullable_string) == 0:
            return 0
        for key in epsilon_sppf.keys():
            node = epsilon_sppf[key]
            if ''.join(nullable_string) == node.label:
                return key
            
            
class ChoiceNode:
    def __init__(self, parent, total):
        self._p, self._chosen = parent, 0
        self._total, self.next = total, None

    def __str__(self):
        return '(%s/%s %s)' % (str(self._chosen),
                               str(self._total), str(self.next))

    def __repr__(self): return repr((self._chosen, self._total))

    def chosen(self): return self._chosen

    def finished(self):
        return self._chosen >= self._total
    
    def increment(self):
        # as soon as we increment, next becomes invalid
        self.next = None
        self._chosen += 1
        if self.finished():
            if self._p is None: return None
            return self._p.increment()
        return self
    

class EnhancedExtractor:
    def __init__(self, forest):
        self.my_forest = forest
        self.choices = ChoiceNode(None, 1)

    def choose_path(self, arr_len, choices):
        if choices.next is not None:
            if choices.next.finished():
                return None, choices.next
        else:
            choices.next = ChoiceNode(choices, arr_len)
        next_choice = choices.next.chosen()
        return next_choice, choices.next
    
    def extract_a_node(self, forest_node, seen, choices):
        if isinstance(forest_node, SPPFNode):
            if not forest_node.children:
                return (forest_node.label, []), choices
            
            packing_node_children = isinstance(forest_node.children[0], PackingNode)

            # PackingNode child
            if packing_node_children:

                child_ind, new_choices = self.choose_path(len(forest_node.children), choices)
                
                # out of choice
                if child_ind is None:
                    return None, new_choices 
                if str(id(forest_node.children[child_ind])) in seen:
                    return None, new_choices
                
                n, newer_choices = self.extract_a_node(forest_node.children[child_ind], 
                                                       seen | {str(id(forest_node.children[child_ind]))}, 
                                                       new_choices)
            
                return (forest_node.label, n), newer_choices
            
            # SPPFNode child
            list_n = []
            for child in forest_node.children:
                n, newer_choices = self.extract_a_node(
                        child, seen | {str(id(child))}, choices)
            
                if n is None: return None, newer_choices
                list_n.append(n)

            return (forest_node.label, list_n), newer_choices


        elif isinstance(forest_node, PackingNode):
            cur_child_ind, new_choices = self.choose_path(len(forest_node.edges), choices)

            # out of choice
            if cur_child_ind is None:
                return None, new_choices
            if str(id(forest_node.edges[cur_child_ind])) in seen:
                return None, new_choices 

            packing_node_children = isinstance(forest_node.edges[0], PackingNode)

            # PackingNode child
            if packing_node_children:

                child_ind, new_choices = self.choose_path(len(forest_node.edges), choices)
                
                # out of choice
                if child_ind is None:
                    return None, new_choices
                if str(id(forest_node.edges[child_ind])) in seen:
                    return None, new_choices

                
                n, newer_choices = self.extract_a_node(forest_node.edges[child_ind], 
                                                       seen | {str(id(forest_node.edges[child_ind]))}, 
                                                       choices)
            
                return n, newer_choices
            
            # SPPFNode child
            list_n = []
            for child in forest_node.edges:
                n, newer_choices = self.extract_a_node(
                        child, seen | {str(id(child))}, choices)
            
                if n is None: return None, newer_choices
                list_n.append(n)

            return list_n, newer_choices
        
    def extract_a_tree(self):
        choices = self.choices
        while not self.choices.finished():
            parse_tree, choices = self.extract_a_node(
                    self.my_forest,
                    set(), self.choices)
            choices.increment()
            if parse_tree is not None:
                return parse_tree
        return None
    


class O:
    def __init__(self, **keys): self.__dict__.update(keys)

OPTIONS   = O(V='│', H='─', L='└', J = '├')

def format_node(node):
    key = node[0]
    if key and (key[0], key[-1]) ==  ('<', '>'): return key
    return repr(key)

def get_children(node):
    return node[1]

def display_tree(node, format_node=format_node, get_children=get_children,
                 options=OPTIONS):
    print(format_node(node))
    for line in format_tree(node, format_node, get_children, options):
        print(line)

def format_tree(node, format_node, get_children, options, prefix=''):
    children = get_children(node)
    if not children: return
    *children, last_child = children
    for child in children:
        next_prefix = prefix + options.V + '   '
        yield from format_child(child, next_prefix, format_node, get_children,
                                options, prefix, False)
    last_prefix = prefix + '    '
    yield from format_child(last_child, last_prefix, format_node, get_children,
                            options, prefix, True)

def format_child(child, next_prefix, format_node, get_children, options,
                 prefix, last):
    sep = (options.L if last else options.J)
    yield prefix + sep + options.H + ' ' + format_node(child)
    yield from format_tree(child, format_node, get_children, options, next_prefix)

format_parsetree = display_tree


# grammar = {
#     "S": [["S", "S"], ["a"], ["epsilon"]]
# }
# start = "S"

# grammar = {
#     "S": [["E"]],
#     "E": [["E", "+", "E"], ["E", "*", "E"], ["a"]]
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

# grammar = {
#     "<E>": [
#             ["<E>", "+", "<T>"],       # Rule 1: E → E + T
#             ["<T>"]                  # Rule 2: E → T
#             ],        
#     "<T>": [
#             ["<T>", "*", "<F>"],       # Rule 3: T → T * F
#             ["<F>"]                  # Rule 4: T → F
#             ],           
#     "<F>": [
#             ["(", "<E>", ")"],       # Rule 5: F → ( E )
#             ["a"]                  # Rule 6: F → a
#             ]
# }

# start = "<E>"


# grammar = {
#                 "S": [["A"]],
#                 "A": [["B"]],
#                 "B": [["C"]],
#                 "C": [[]]
#             }
# start = "S"
# Test the Parser
grammar = {
    "S": [["S", "+", "S"], ["a"]]
}
start = "S"
t = RNParseTableConstructer(grammar, start)
export_filepath = "tables/test.csv"
t.export_to_csv(export_filepath)
# print(t.parse_table)
t.printResultAndGoto()
# parser = RNGLRParser(start, export_filepath, grammar)
# print(parser.parse_table_from_csv("tables/test.csv"))
# input_string = list("a+a*a")

# root_node, res = parser.parse(input_string)
# print("Correct String:", res)

# ee = EnhancedExtractor(root_node)
# while True:
#     t = ee.extract_a_tree()
#     import simplefuzzer as fuzzer
#     if t is None: break
#     assert fuzzer.tree_to_string(t) == "".join(input_string)
