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
    def __init__(self, label, start_position=None, end_position=None):
        self.label = label
        self.start_position = start_position
        self.end_postion = end_position
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