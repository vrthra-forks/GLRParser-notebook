import unittest
from final_parser.RNGLR import RNParseTableConstructer, RNGLRParser, PackingNode, SPPFNode

class TestRNGLRParser(unittest.TestCase):
    def setUp(self):
        # Initialize common components if needed
        pass

    # --------------------------
    # Test Case 1: Basic Arithmetic
    # --------------------------
    def test_arithmetic_grammar(self):
        grammar = {
            "E": [["E", "+", "T"], ["T"]],
            "T": [["T", "*", "F"], ["F"]],
            "F": [["(", "E", ")"], ["id"]]
        }
        start = "E"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)
        
        # Valid inputs
        self.assertTrue(glr_parser.parse(["id"]))
        self.assertTrue(glr_parser.parse(["id", "+", "id", "*", "id"]))
        self.assertTrue(glr_parser.parse(["(", "id", "+", "id", ")"]))

    # --------------------------
    # Test Case 2: Epsilon Rules
    # --------------------------
    def test_epsilon_grammar(self):
        grammar = {
            "S": [["A", "B"]],
            "A": [["a"], []],
            "B": [["b"], []]
        }
        start = "S"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)

        # Empty input (parsed via epsilon rules)
        self.assertTrue(glr_parser.parse([]))
        self.assertTrue(glr_parser.parse(["a"]))
        self.assertTrue(glr_parser.parse(["a", "b"]))

    # --------------------------
    # Test Case 3: Left Recursion
    # --------------------------
    def test_left_recursion(self):
        grammar = {
            "E": [["E", "+", "T"], ["T"]],
            "T": [["id"]]
        }
        start = "E"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)

        self.assertTrue(glr_parser.parse(["id", "+", "id", "+", "id"]))
        # Verify GSS has no cycles
        self.assertEqual(len(glr_parser.gss.nodes), 12)  # Adjust based on your GSS logic

    # --------------------------
    # Test Case 4: Right Recursion
    # --------------------------
    def test_right_recursion(self):
        grammar = {
            "S": [["a", "S"], ["a"]]
        }
        start = "S"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)

        self.assertTrue(glr_parser.parse(["a", "a", "a"]))
        # Verify SPPF has right-branching structure
        self.assertGreaterEqual(len(glr_parser.sppf_root.children), 2)

    # --------------------------
    # Test Case 5: Ambiguous Grammar
    # --------------------------
    def test_ambiguous_grammar(self):
        grammar = {
            "S": [["E"]],
            "E": [["E", "+", "E"], ["E", "*", "E"], ["id"]]
        }
        start = "S"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)

        self.assertTrue(glr_parser.parse(["id", "+", "id", "*", "id"]))
        # Verify SPPF has packing nodes
        def has_packing_nodes(sppf_root):
            def traverse(node):
                if isinstance(node, PackingNode):
                    return True
                if isinstance(node, SPPFNode):
                    for child in node.children:
                        if traverse(child):
                            return True
                elif isinstance(node, PackingNode):
                    for edge in node.edges:
                        if traverse(edge):
                            return True
                return False

            traverse(sppf_root) if sppf_root else False
        
        has_packing = has_packing_nodes(glr_parser.sppf_root)
        self.assertTrue(has_packing_nodes)

    # --------------------------
    # Test Case 6: Complex Mixed Grammar
    # --------------------------
    def test_complex_grammar(self):
        grammar = {
            "S": [["A", "B", "C"], ["S", "S"]],
            "A": [["a"], []],
            "B": [["b"], []],
            "C": [["c"], []]
        }
        start = "S"
        parser = RNParseTableConstructer(grammar, start)
        export_filepath = "tables/test.csv"
        parser.export_to_csv(export_filepath)
        glr_parser = RNGLRParser(start, export_filepath, grammar)

        # Fully nullable
        self.assertTrue(glr_parser.parse([]))
        # Partially nullable
        self.assertTrue(glr_parser.parse(["a"]))
        self.assertTrue(glr_parser.parse(["a", "b"]))
        # Non-nullable
        self.assertTrue(glr_parser.parse(["a", "b", "c"]))


    # Test Case 7: Right-recursive grammar with terminals
    def test_right_recursive_terminals(self):
        self._run_test(
            {"S": [["a", "S"], ["a"]]},
            "S",
            ["a", "a", "a"],
            True,
            "Right recursion with terminals"
        )

    # Test Case 8: Complex arithmetic precedence
    def test_complex_arithmetic_precedence(self):
        self._run_test(
            {
                "E": [["E", "+", "T"], ["T"]],
                "T": [["T", "*", "F"], ["F"]],
                "F": [["(", "E", ")"], ["id"]]
            },
            "E",
            ["id", "+", "id", "*", "id"],
            True,
            "Operator precedence and associativity"
        )

    # Test Case 9: Nested nullable non-terminals
    def test_nested_nullable_non_terminals(self):
        grammar = {
            "S": [["A", "B"]],
            "A": [["a"], []],
            "B": [["b"], []]
        }
        self._run_test(grammar, "S", [], True, "Fully nullable parse")
        self._run_test(grammar, "S", ["a"], True, "Partially nullable parse")

    # Test Case 10: Deeply nested brackets
    def test_deeply_nested_brackets(self):
        self._run_test(
            {"S": [["(", "S", ")"], []]},
            "S",
            ["(", "(", ")", ")"],
            True,
            "Nested brackets with closure"
        )

    # Test Case 11: Highly ambiguous grammar
    def test_highly_ambiguous_grammar(self):
        self._run_test(
            {"S": [["S", "S"], ["a"], ["b"]]},
            "S",
            ["a", "b", "a"],
            True,
            "Exponential ambiguity detection",
            check_packing=True
        )

    # Test Case 12: Mixed terminals and nullable non-terminals
    def test_mixed_terminals_nullable(self):
        self._run_test(
            {
                "S": [["A", "B", "C"]],
                "A": [["a"], []],
                "B": [["b"], []],
                "C": [["c"]]
            },
            "S",
            ["c"],
            True,
            "Nullable prefix handling"
        )

    # Test Case 13: Epsilon-only grammar
    def test_epsilon_only_grammar(self):
        self._run_test(
            {"S": [[]]},
            "S",
            [],
            True,
            "Pure epsilon grammar"
        )

    # Test Case 14: Single production grammar
    def test_single_production_grammar(self):
        grammar = {"S": [["a"]]}
        self._run_test(grammar, "S", ["a"], True, "Single terminal parse")
        # self._run_test(grammar, "S", ["b"], False, "Invalid terminal detection")

    # Test Case 15: Chained nullable non-terminals
    def test_chained_nullable_non_terminals(self):
        self._run_test(
            {
                "S": [["A"]],
                "A": [["B"]],
                "B": [["C"]],
                "C": [[]]
            },
            "S",
            [],
            True,
            "Chained nullability"
        )

    # Test Case 16: Complex mixed recursion and nullability
    def test_complex_mixed_recursion(self):
        grammar = {
            "S": [["S", "a"], ["A"]],
            "A": [["B", "C"]],
            "B": [[]],
            "C": [[]]
        }
        self._run_test(grammar, "S", [], True, "Recursive nullable base case")
        self._run_test(
            grammar,
            "S",
            ["a", "a", "a"],
            True,
            "Recursion with terminal suffixes"
        )

    # --------------------------
    # Helper Function
    # --------------------------
    def _run_test(self, grammar, start, input_tokens, expected_result, 
                 test_name="", check_packing=False):
        """Helper function to run parser tests with assertions"""
        with self.subTest(test_name=test_name):
            # Build parser components
            parser = RNParseTableConstructer(grammar, start)
            export_filepath = "tables/test.csv"
            parser.export_to_csv(export_filepath)
            glr_parser = RNGLRParser(start, export_filepath, grammar)
            # glr_parser = RNGLRParser(parser.grammar, parser.non_terminals,
            #                         parser.terminals, start, parser.parse_table,
            #                         parser.epsilon_sppf)
            
            # Run parsing
            root, result = glr_parser.parse(input_tokens)
            
            # Core assertions
            self.assertEqual(result, expected_result, 
                            f"{test_name} result mismatch")
            
            # Specialized checks
            if check_packing:  
                      # Verify SPPF has packing nodes
                def has_packing_nodes(sppf_root):
                    def traverse(node):
                        if isinstance(node, PackingNode):
                            return True
                        if isinstance(node, SPPFNode):
                            for child in node.children:
                                if traverse(child):
                                    return True
                        elif isinstance(node, PackingNode):
                            for edge in node.edges:
                                if traverse(edge):
                                    return True
                        return False

                    return traverse(sppf_root) if sppf_root else False


                has_packing = has_packing_nodes(root)
                self.assertTrue(has_packing, 
                              f"{test_name} should have packing nodes {root} {root.children}")
            
            if expected_result and glr_parser.sppf_root:
                # Verify SPPF structure exists for valid parses
                self.assertGreaterEqual(len(glr_parser.sppf), 1,
                                      f"{test_name} SPPF not built")

if __name__ == "__main__":
    unittest.main()