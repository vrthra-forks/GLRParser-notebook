import final_parser.CYK as cyk

def test2():
    grammar = {
        "<E>": [["<E>", "+", "<T>"], ["<T>"]],        
        "<T>": [["<T>", "*", "<F>"], ["<F>"]],           
        "<F>": [["(", "<E>", ")"], ["a"]]
    }
    start = "<E>"
    s = "a+a*a"
    cyk_parser = cyk.CYKParser(grammar)
    cyk_result = cyk_parser.parse_on(s, start)
    for t in cyk_result:
        pass

test2()