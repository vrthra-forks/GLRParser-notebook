import copy

class SLRParser:
    """
    An implementation of SLR(1) parser. This parser constructs parsing tables
    and processes context-free grammars using a bottom-up approach with
    first and follow set to determine valid lookahead tokens
    """
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
        
        self.first_table = {}
        self.follow_table = {}
        self.in_progress = set()     # this variable is used to avoid left recursive when calculating first
        self.calculateFirstTable()
        self.calculateFollowTable()
        
        self.augmented_rules = []    # format of rule: [rhs, [<lhs symbol>, <lhs symbol>, ...]
        self.state_map = {}          # store rules of a state (format: state_count: [[rule1], [rule2], ...])
        self.state_dict = {}         # store which state go to which state
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
                if self.start == "":
                    self.start = f"{key}'"
                else:
                    self.start = f"{self.start}'"
                self.grammar[0] = (self.start, [key])
                count += 1

            # Process each rule into the format above
            for rule in input_grammar[key]:
                if rule == ["epsilon"]:
                    rule = []
                self.grammar[count] = (key, rule)
                count += 1

        # Detecting terminals and non-terminals symbols if it was not given
        if len(self.terminals) == 0 and len(self.non_terminals) == 0:
            for key in self.grammar.keys():
                lhs, rhs = self.grammar[key]
                if lhs not in self.non_terminals and lhs not in self.terminals:
                    self.non_terminals.append(lhs)
            for key in self.grammar.keys():
                lhs, rhs = self.grammar[key]
                for sym in rhs:
                    if sym not in self.non_terminals and sym not in self.terminals:
                        # if sym != "epsilon":
                        self.terminals.append(sym)


    def addDot(self):
        """
        Adding a dot (·) (tracker of process of parsing) at the start of each production's RHS.
        """
        for key in self.grammar.keys():
            lhs, rhs = self.grammar[key]
            new_rhs = [self.dot]
            for elem in rhs:
                new_rhs.append(elem)
            self.augmented_rules.append([lhs, new_rhs])

    def generateStates(self):
        """
        Generate all states for the parser, starting with the initial state.
        """
        # generate and calculate the closure of the initial state I_0
        first_state = []
        for rule in self.augmented_rules:
            if rule[0] == self.start:
                first_state.append(rule)
        closure_rules = self.findClosure(first_state)
        self.state_dict[0] = closure_rules

        # generate states until no more state is able to be generated
        prev_len = -1
        state_completed_GOTO = []
        while prev_len != len(self.state_dict):
            prev_len = len(self.state_dict)

            keys = list(self.state_dict.keys())
            for state in keys:
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
            # if the rule ends with dot (can't shift anymore) => skip
            if rule[1][-1] == self.dot:
                continue

            dot_ind = rule[1].index(self.dot)
            next_sym = rule[1][dot_ind+1]

            # shift operation from the previous state of rule on that
            if next_sym == sym:
                # swap dot with next_sym
                shifted_rule = copy.deepcopy(rule)
                shifted_rule[1][dot_ind] = shifted_rule[1][dot_ind + 1]
                shifted_rule[1][dot_ind + 1] = self.dot
                new_state.append(shifted_rule)

        closure_rules = self.findClosure(new_state)

        # check if state exist
        state_exists = -1
        for state_num in self.state_dict:
            if self.state_dict[state_num] == new_state:
                state_exists = state_num
                break
     
        # stateMap is a mapping of GOTO with
        # its output states
        if state_exists == -1:
            self.state_count += 1
            self.state_dict[self.state_count] = closure_rules
            self.state_map[(state, sym)] = self.state_count
        else:
            self.state_map[(state, sym)] = state_exists
            

    def findClosure(self, closure_rules):
        """
        Generate the closure for a rules.

        Args:
            closure_rules (list): A list of rules for which the closure is to be computed.

        Returns:
            list: The closure of the input rules.
        """

        # generate closure for the rules in new_state
        # generate until can't generate anymore
        # start with the closure of the initial state
        prev_len = -1
        while prev_len != len(closure_rules):
            prev_len = len(closure_rules)
            for rule in closure_rules:
                if rule[1][-1] == self.dot:
                    continue
                    
                dot_ind = rule[1].index(self.dot)
                next_sym = rule[1][dot_ind+1]
    
                # if next_sym is non_terminal then continue adding rule with that nonterminals as lhs
                if next_sym in self.non_terminals:
                    for augmented_rule in self.augmented_rules:
                        if augmented_rule[0] == next_sym and augmented_rule not in closure_rules:
                            closure_rules.append(augmented_rule)
        return closure_rules

        
    def calculateFirstTable(self):
        """
        Compute the FIRST table for the grammar.
        """
        for key in self.grammar.keys():
            rule = self.grammar[key]
            lhs, rhs = rule

            if lhs not in self.first_table:
                self.first_table[lhs] = list(elem for elem in self.first(rule))
            else:
                res = self.first(rule)
                for elem in res:
                    if elem not in self.first_table[lhs]:
                        self.first_table[lhs].append(elem)

    
    def calculateFollowTable(self):
        """
        Compute the FOLLOW table for the grammar.
        """
        for nt in self.non_terminals:
            self.follow_table[nt] = self.follow(nt)

    
    def first(self, rule):
        """
        Compute the FIRST set for a given rule.

        Args:
            rule (tuple): A tuple (LHS, RHS) representing a grammar rule.

        Returns:
            list: The FIRST set for the rule.
        """
        lhs, rhs = rule

        if rhs == []:
            return []
        
        if lhs in self.in_progress:
            return []  # prevent infinite recursion
        
        # mark this non-terminal as being processed
        self.in_progress.add(lhs)
        
        # rule for terminals
        if rhs[0] in self.terminals:
            return [rhs[0]]
            
        # rule for epsilon
        elif rhs[0] == "epsilon":
            return []
            
        # rule for non-terminal
        else:
            res = []
            for key in self.grammar.keys():
                if rhs[0] == self.grammar[key][0]:
                    for elem in self.first(self.grammar[key]):
                        res.append(elem) 

            if "epsilon" in res:
                res.remove("epsilon")
                
            self.in_progress.remove(lhs)  # finished processing this non-terminal
            return res

    
    def follow(self, nt, visited=None):
        """
        Compute the FOLLOW set for a non-terminal.

        Args:
            nt (str): The non-terminal symbol.
            visited (set): A set of visited non-terminals to prevent infinite recursion.

        Returns:
            list: The FOLLOW set for the non-terminal.
        """
        if visited is None:
            visited = set()
    
        if nt in visited:
            return []

        visited.add(nt)
        res = set()

        # for start symbol return $
        if nt == self.start:
            res.add("$")

        for key in self.grammar.keys():
            lhs, rhs = self.grammar[key]
            
            for i, symbol in enumerate(rhs):
                if symbol == nt:
                    rhs = rhs[i + 1:]

                    # rule 2: there is a symbol after nt
                    if len(rhs) != 0:
                        # if the symbol after nt is also a non-terminal:
                        #   - calculate its first (remove epsilon) and add to res
                        #   - if its first contain epsilon, then continue checking the next symbol
                        # else the symbol after nt is a terminal:
                        #   - then add it to res
                        for sym in rhs:
                            if sym in self.terminals:
                                res.add(sym)
                                break
                            elif sym in self.first_table:
                                first_sym = self.first_table[sym]
                                res.update(set(first_sym))
    
                                if "epsilon" in first_sym:
                                    res.remove("epsilon")
                                else:
                                    break

                    # rule 3: there is no symbol after nt -> FOLLOW(lhs) ⊆ FOLLOW(nt)
                    if len(rhs) == 0:  
                        if lhs != nt:
                            res.update(self.follow(lhs, visited))
                            
        visited.remove(nt)
        return list(res)

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

            if sym == "epsilon":
                continue

            row_ind = rows.index(state)
            col_ind = cols.index(sym)

            if sym in self.terminals:
                self.parse_table[row_ind][col_ind].append(f"S{self.state_map[entry]}")
            elif sym in self.non_terminals:
                self.parse_table[row_ind][col_ind].append(f"G{self.state_map[entry]}")

        # add reduce to table
        for state in self.state_dict.keys():
            for rule in self.state_dict[state]:
                # if the rule is a handle -> add reduce correspondingly
                if rule[1][-1] == self.dot:
                    copy_rhs = copy.deepcopy(rule[1])
                    copy_rhs.remove(self.dot)

                    # add entry R_rule_num (Reduce -> rule_num) to entry (state, follow(rhs)) in parse table
                    for rule_num in self.grammar.keys():
                        if self.grammar[rule_num][0] == rule[0] and self.grammar[rule_num][1] == copy_rhs:
                            for follow in self.follow_table[rule[0]]:
                                row_ind = rows.index(state)
                                col_ind = cols.index(follow)
                                if rule_num == 0:
                                    self.parse_table[row_ind][col_ind].append("Accept")
                                else:
                                    self.parse_table[row_ind][col_ind].append(f"R{rule_num}")

    	# printing table
        print("\nParsing table:\n")
        frmt = "{:>8}" * len(cols)
        print(" ", frmt.format(*cols), "\n")
        ptr = 0
        j = 0
        for y in self.parse_table:
            # frmt1 = "{:>8}"
            print(f"{{:>3}}".format('I'+str(j)), end="")
            for e in y:
                print(f"{{:>8}}".format("/".join(e)), end="")
            print()
            j += 1

        # saving the parse table to a csv file
        file = open("rules/parse_tables/parsetable1.csv", "w")
        file.write("state,"+",".join(cols)+"\n")
        j = 0
        for y in self.parse_table:
            line = ""
            line += f"I{j}"
            for e in y:
                line += "," + "/".join(e)
            file.write(line + "\n")
            j += 1
        file.close()

    def parse(self, input_string):
        """
        Parses the given input string using the constructed SLR parse table.

        Args:
            input_string (list): The input string represented as a list of symbols 
                (terminals) to be parsed. The end of the input is marked by "$".

        Returns:
            bool: True if the input string is successfully parsed and reaches 
                the "Accept" state; False otherwise.

        Notes: This method handles conflicts by always selecting the first operation 
        in a conflicting cell in the parse table.
        """
        self.printResultAndGoto()
        rows = list(self.state_dict.keys())
        cols = self.terminals + ["$"] + self.non_terminals
        
        # appends "$" to indicate the end of input.
        ls_input = input_string + ["$"]
        current_char = ls_input[0]
        ls_output = []
        stack = [0]
        while True:
            if current_char not in cols:
                return False
            
            row_ind = rows.index(stack[-1])
            col_ind = cols.index(current_char)
            
            operation = self.parse_table[row_ind][col_ind]
            
            if operation == []:
                return False
                
            else:
                operation = operation[0] # just get the first operation in conflict cell
                if operation[0] == "R":
                    rule_num = int(operation[1:])
                    current_char = self.grammar[rule_num][0]
                    
                    # pop stack equal to number of char on rhs of reduce rule
                    stack_pop_count = len(self.grammar[rule_num][1])
                    stack = stack[:-stack_pop_count]

                    ls_output.append(rule_num)
                
                # goto operation
                elif operation[0] == "G":
                    stack.append(int(operation[1:]))
                    current_char = ls_input[0]  
                    
                # shift operation
                elif operation[0] == "S":
                    stack.append(int(operation[1:]))
                    ls_input.pop(0) 
                    current_char = ls_input[0]      

                # accept reached
                elif operation == "Accept":
                    return True
                
    def printResultAndGoto(self):
        print("\nStates Generated: \n")
        for st in self.state_dict:
            print(f"State = I{st}")
            self.printResult(self.state_dict[st])
            print()# print goto states
        print("\nStates Generated: \n")
        for st in self.state_dict:
            print(f"State = I{st}")
            self.printResult(self.state_dict[st])
            print()
        print("Result of GOTO computation:\n")
        self.printAllGOTO(self.state_map)


    def printResult(self, rules):
        for rule in rules:
            print(f"{rule[0]} ->",
                    f" {' '.join(rule[1])}")

    def printAllGOTO(self, diction):
        for itr in diction:
            print(f"GOTO ( I{itr[0]} ,"
                    f" {itr[1]} ) = I{self.state_map[itr]}")
   

class GSSNode:
    def __init__(self, is_state, state, symbol):
        self.is_state = is_state
        self.state = state  # Parser state
        self.symbol = symbol  # Grammar symbol
        self.predecessor_edges = []  # List of edges to predecessor nodes
        self.successor_edges = []  # List of edges to successor  nodes

    def add_predecessor(self, predecessor):
        """Add an edge to a predecessor node."""
        self.predecessor_edges.append(predecessor)

    def add_successor(self, successor):
        """Add an edge to a predecessor node."""
        self.successor_edges.append(successor)


class GSS:
    def __init__(self):
        self.current_v = 0
        self.nodes = {}  # Map v_number -> GSSNode

    def create_node(self, is_state, state=-1, symbol=""):
        self.current_v += 1
        self.nodes[self.current_v] = GSSNode(is_state, state, symbol)
        return self.nodes[self.current_v]

    def add_edge(self, from_node, to_node):
        # successor of v = there is an edge from v to this node 
        from_node.add_successor(to_node)
        to_node.add_predecessor(from_node)

    def dfs(self, node, depth):
        # print(f"DEPTH {depth} {node.state}")
        if depth == 0:
            return {node}

        reachable = set()
        for successor in node.successor_edges:
            reachable |= self.dfs(successor, depth - 1)
        return reachable

    def find_node_path_length(self, start, length):
        # Find all nodes reachable from `start` with a path of a specific length.
        return self.dfs(start, length)

    def path_exists(self, start, end, length):
        # Check if a path of a specific length exists between `start` and `end`.
        reachable_nodes = self.find_node_path_length(start, length)
        return end in reachable_nodes


class GLRParser():
    def __init__(self, grammar, non_terminals, terminals, parse_table): 
        self.grammar = grammar
        self.non_terminals = non_terminals
        self.terminals = terminals
        self.symbols = self.terminals + ["$"] + self.non_terminals
        self.parse_table = self.load_parse_table(parse_table)
        print(self.parse_table)

        self.gss = GSS()
        self.root_node = self.gss.create_node(True, state=0)  # Initial state
        self.input_string = []
        self.r = False
        self.U = {0: {0: [self.root_node]}}
        self.R = []
        self.Re = []
        self.Q = []
        self.A = []

        self.j = 0

    def load_parse_table(self, parse_table):
        # print(1)
        # print(parse_table)

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
        """Main parsing loop."""
        self.input_string = input_string
        self.input_string.append("$")

        i = 0
        # print(self.input_string)
        while i < len(self.input_string):
            # print("### ITERATION", i)
            if i not in self.U.keys():
                break
            self.parseword(i, input_string)
            i += 1

        if self.r == True:
            print("Input accepted!")
        else:
            print("Input not accepted!")
        return self.r


    def parseword(self, i, input_string):
        self.j = 0

        self.A = copy.copy(self.U[i][self.j])
        self.R = []
        self.Re = []
        self.Q = []

        while True:
            # print("A - ", self.A)
            # print("R - ", self.R)
            # print("Re - ", self.Re)
            # print("Q - ", self.Q)
            if len(self.A) != 0:
                self.actor(i, input_string)
            elif len(self.R) != 0:
                self.reducer(i, input_string)
            elif len(self.Re) != 0:
                self.e_reducer(i, input_string)

            if len(self.R) == 0 and len(self.Re) == 0 and len(self.A) == 0:
                # print("NO NODE IN ANY QUEUE")
                break

        self.shifter(i, input_string)



    def actor(self, i, input_string):
        v = self.A.pop(0)
            
        current_state = v.state
        symbol = input_string[i]
        col_ind = self.symbols.index(symbol)
        # print(self.parse_table)

        # print(current_state, symbol)
        if self.parse_table[current_state][col_ind]:
        # if (current_state, symbol) in self.parse_table:
            operations = self.parse_table[current_state][col_ind]
            # print("### OPERATIONS")    
            # print(operations)
            for operation in operations:
                # print(operation)
                if len(operation) == 0:
                    return
                
                if operation == 'Accept':
                    # print(10000000000000000)
                    self.r = True
                    # print("A - ", self.A)
                    # print("R - ", self.R)
                    # print("Re - ", self.Re)
                    # print("Q - ", self.Q)                    
                elif operation[0] == "S":
                    self.Q.append((v, int(operation[1:])))
                elif operation[0] == "R":
                    # print(f"############### {self.grammar[int(operation[1:])][1]}")
                    # if not epsilon reduction:
                    if self.grammar[int(operation[1:])][1] != []:
                        # for all x such that x SUCCESSORS(v), add [v, x, p] to R.
                        # print("NODE V:", v.state, v.symbol)
                        for x in v.successor_edges:
                            # print(x.state, x.symbol)
                            self.R.append([v, x, int(operation[1:])])
                            # print("A - ", self.A)
                            # print("R - ", self.R)

                    else:
                        self.Re.append([v, int(operation[1:])])

    
    def reducer(self, i, input_string):
        # print("### REDUCER\n", self.R)
        (v, x, p) = self.R.pop(0)
        N = self.grammar[int(p)][0]
        # print(x.state, x.symbol)
        # print(x.successor_edges)
        # for all w such that there exists a path of length 2|p|-1 from x to w do
        len_rhs_reduce = len(self.grammar[p][1])
        # print(self.grammar[p])
        all_w = self.gss.find_node_path_length(x, 2*len_rhs_reduce-1)
        for w in all_w:
            # print("LIST W", w.state)
            # print("N", N)
            # operation = self.parse_table(w.state, N)
            col_ind = self.symbols.index(N)
            # print(w.state, col_ind)
            for operation in self.parse_table[w.state][col_ind]:
                # print(operation)
                if len(operation) == 0:
                    return
                elif operation[0] == "G":
                    s = int(operation[1:])
                # else:
                #     return
             

            # if there exists u such that u in U_ij and STATE(u) = s then
            need_create_reduce = False
            for u in self.U[i][self.j]:
                if u.state == s:
                    need_create_reduce = True
                    break
                    
            # if there exists u such that u in U_ij and STATE(u) = s then
            if need_create_reduce:
                # if there already exists a path of length 2 from u to w then
                if self.gss.path_exists(u, w, 2):
                    continue
                else:
                    # if u in A
                    # for all q such that reduce q in ACTION(STATE(u),ai+1)
                    # add (u,z,q) to R.
                    z = self.gss.create_node(False, symbol=N)
                    self.gss.add_edge(u, z)
                    self.gss.add_edge(z, w)

                    if u not in self.A:
                        col_ind = self.symbols.index(input_string[i])
                        for operation in self.parse_table[u.state][col_ind]:
                        # for operation in self.parse_table(u.state, input_string[i]):
                            if operation[0] == "R":
                                self.R.append((u, z, int(operation[1:])))

            else:
                u = self.gss.create_node(True, state=s)
                z = self.gss.create_node(False, symbol=N)

                self.gss.add_edge(u, z)
                self.gss.add_edge(z, w)

                self.A.append(u)
                self.U[i][self.j].append(u)
                        
                    
    
    def e_reducer(self, i, input_string):
        if i not in self.U.keys():
            self.U[i] = {}
        self.U[i][self.j+1] = []

        # print("### REDUCER epsilon\n", self.Re)
        for v, p in self.Re:
            N = self.grammar[int(p)][0]
            # for all w such that there exists a path of length 2|p| from v to w do
            len_rhs_reduce = len(self.grammar[p][1])
            # print(self.grammar[p])
            all_w = self.gss.find_node_path_length(v, 2*len_rhs_reduce)
            for w in all_w:
                # print("LIST W", w.state)
                # print("N", N)
                # operation = self.parse_table(w.state, N)
                col_ind = self.symbols.index(N)

                # print(v.state, N)
                # s = GOTO(v.state, N)
                for operation in self.parse_table[v.state][col_ind]:
                    # print(operation)
                    if len(operation) == 0:
                        return
                    elif operation[0] == "G":
                        s = int(operation[1:])
                

                # if there exists w such that w in U_ij+1 and STATE(u) = s then
                need_create_reduce = False
                for w in self.U[i][self.j+1]:
                    if w.state == s:
                        need_create_reduce = True
                        break
                        
                # if there exists u such that u in U_ij+1 and STATE(u) = s then
                if need_create_reduce:
                    x = self.gss.create_node(False, symbol=N)
                    self.gss.add_edge(w, x)
                    self.gss.add_edge(x, v)

                else:
                    w = self.gss.create_node(True, state=s)
                    x = self.gss.create_node(False, symbol=N)
                    self.gss.add_edge(w, x)
                    self.gss.add_edge(x, v)
                    self.U[i][self.j+1].append(w)
                    # print("(((((())))))", w.state)

        self.Re = []
        self.A = copy.copy(self.U[i][self.j+1])
        self.j += 1
        # print("A - ", self.A)
        # print("R - ", self.R)
        # print("Re - ", self.Re)
        # print("Q - ", self.Q)   



    def shifter(self, i, input_string):
        # print("### SHIFTER")
        # print(self.Q)
        all_s = list(set([s for v, s in self.Q]))
        # print(all_s)
        for state in all_s:
            # new state node after shift
            w = self.gss.create_node(True, state=state)

            # add w to U_i+1
            if i+1 not in self.U.keys():
                self.U[i+1] = {}
                self.U[i+1][0] = []
            self.U[i+1][0].append(w)

            # add edge between w and v in <v,s> with the s above
            all_v = list(set([v for v, s in self.Q if s == state]))
            for v in all_v:
                x = self.gss.create_node(False, symbol=input_string[i])
                # print(x.symbol)
                self.gss.add_edge(w, x)
                self.gss.add_edge(x, v)
                # print(x.successor_edges[0].state)
                # print(w.state)




from collections import deque

class GrammarExpander:
    def __init__(self, grammar, terminals, start):
        self.grammar = grammar
        self.terminals = terminals
        self.start_symbol = start

    def is_fully_expanded(self, symbols):
        return all(symbol in self.terminals for symbol in symbols)

    def get_productions_for(self, symbol):
        return [prod for lhs, prod in self.grammar.values() if lhs == symbol]

    def expand_grammar(self, max_strings, max_depth):
        queue = deque([([self.start_symbol], 0)])  # (current list of symbols, current depth)
        seen_strings = set()  # To avoid duplicates
        results = set()  # Store unique results (only fully terminal strings)
        
        while queue and len(results) < max_strings:
            current_string, depth = queue.popleft()
            
            # If the current string is fully expanded, store it as a result
            if self.is_fully_expanded(current_string):
                result_string = ''.join(current_string)  # Convert list of symbols back to string
                if result_string not in results:
                    results.add(result_string)
            elif depth < max_depth:
                # Find the first non-terminal to expand
                for i, symbol in enumerate(current_string):
                    if symbol not in self.terminals:
                        # Get productions for this non-terminal
                        productions = self.get_productions_for(symbol)
                        for production in productions:
                            # Replace part of the list with the production
                            new_string = current_string[:i] + production + current_string[i+1:]
                            if tuple(new_string) not in seen_strings:
                                queue.append((new_string, depth + 1))
                                seen_strings.add(tuple(new_string))  # Store the tuple to avoid duplicate lists
                        break  # Only expand one non-terminal at a time
        
        return list(results)
    

# Example 1 Grammar and Tables
grammar = {
    "S": [
            ["a", "S", "B"],       # Rule 1: S → a S B
            ["b"]                  # Rule 2: E → b
            ],        
    "B": [
            ["epsilon"]            # Rule 3: B → epsilon
            ]
}

start = "S"

p = SLRParser(grammar, start)
parser = GLRParser(p.grammar, p.non_terminals, p.terminals, p.parse_table)
expander1 = GrammarExpander(p.grammar, p.terminals, p.start)

num_string = 100
valid_strings = expander1.expand_grammar(max_strings=num_string, max_depth=100)

# Test the parser
for i, s in enumerate(valid_strings):
    print(s)
    res = parser.parse(list(s))
    assert res == True, f"Fail test: {s}"


# # Example 1 Grammar and Tables
# grammar = {
#     "S": [
#             ["a", "S", "B"],       # Rule 1: S → a S B
#             ["b"]                  # Rule 2: E → b
#             ],        
#     "B": [
#             ["epsilon"]            # Rule 3: B → epsilon
#             ]
# }

# start = "E"

# # Test the Parser
# p = SLRParser(grammar, start)
# p.printResultAndGoto()
# parser = GLRParser(p.grammar, p.non_terminals, p.terminals, p.parse_table)
# input_string = list("aaaaaaaab")
# parser.parse(input_string)
