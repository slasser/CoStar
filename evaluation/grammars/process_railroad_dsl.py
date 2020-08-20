import json, os, re, sys
from railroad import *

def ocaml_list_repr(xs):
    """Convert a list of strings to a string repr of a valid OCaml list"""
    return "[{}]".format("; ".join(xs))

def ocaml_tup_repr(x, y):
    return "({}, {})".format(x, y)

def ocaml_string_repr(x):
    return "\"{}\"".format(x)

def get_rhss(diag):
    "Extract the Sequence nodes that represent production right-hand sides"""
    assert isinstance(diag, Diagram)
    choice = diag.items[2]
    assert isinstance(choice, Choice)
    seqs = choice.items
    for seq in seqs:
        print seq
        assert isinstance(seq, Sequence)
    return seqs

def eltstr(elt):
    """Helper function for debugging"""
    if isinstance(elt,   Choice):
        return "Choice"
    elif isinstance(elt, Sequence):
        return "Sequence"
    elif isinstance(elt, OneOrMore):
        return "OneOrMore"
    elif isinstance(elt, Terminal):

        return "Terminal"
    elif isinstance(elt, NonTerminal):
        return "NonTerminal"
    elif isinstance(elt, Skip):
        return "Skip"
    else:
        raise ValueError("unrecognized element type: " + str(elt))

def str_of_terminal_name(n):
    pattern = re.compile(r"'(.*)'$")
    mo = pattern.match(n)
    if mo:
        return "Lit_{}".format(mo.group(1))
    else:
        return n
    
def str_of_rhs_elt(elt):
    """Get a string representation of an EBNF right-hand side element"""
    if isinstance(elt, Choice):
        items = elt.items
        if len(items) == 2 and isinstance(items[0], Skip):
            if isinstance(items[1], OneOrMore) :
                return "ZeroOrMore (" + str_of_rhs_elt(items[1].item) + ")"
            else:
                return "Optional ("   + str_of_rhs_elt(items[1])      + ")"
        else:
            return "Choice " + ocaml_list_repr(map(str_of_rhs_elt, elt.items))
    elif isinstance(elt, Sequence):
        return "Sequence " + ocaml_list_repr(map(str_of_rhs_elt, elt.items))
    elif isinstance(elt, OneOrMore):
        return "OneOrMore (" + str_of_rhs_elt(elt.item) + ")"
    elif isinstance(elt, Terminal):
        return "Terminal " + json.dumps(str_of_terminal_name(elt.text))
    elif isinstance(elt, NonTerminal):
        return "NonTerminal " + json.dumps(elt.text)
    else:
        raise ValueError("unrecognized element type: " + str(elt))

def str_of_rhs(seq):
    """Get a string representation of an EBNF right-hand side"""
    return ocaml_list_repr(map(str_of_rhs_elt, seq.items))

def str_of_production(lhs, rhs):
    """Get a string representation of an EBNF production"""
    return "({}, {})".format(json.dumps(lhs), str_of_rhs(rhs))

def get_ocaml_productions(dsl_file):
    """Read a .py file in which each line represents an ANTLR rule
       ---i.e., a (string, railroad diagram) tuple---
       and convert each tuple to a string repr of an OCaml tuple 
       that represents the same rule
    """
    prods = []
    with open(dsl_file, "r") as fh:
        for line in fh:
            lhs, diag = eval(line)
            print lhs
            rhss = get_rhss(diag)
            for rhs in rhss:
                prods.append(str_of_production(lhs, rhs))
        return prods

def get_ocaml_tuple_list(dsl_file, grammar_name):
    """Read a .py file in which each line represents an ANTLR rule
       ---i.e., a (string, railroad diagram) tuple---
       and returns a string repr of an OCaml tuple list definition
    """
    prods = get_ocaml_productions(dsl_file)
    return "let rules = \n[ " + "\n; ".join(prods) + "\n]"

def convert_all_files(pydir, ocamldir):
    """Convert each Python representation of an ANTLR grammar in indir
    to an equivalent OCaml representation in outdir"""
    if not os.path.exists(ocamldir):
        os.mkdir(ocamldir)
    for dsl_file in os.listdir(pydir):
        grammar_name = dsl_file.replace(".py", "")
        rules = get_ocaml_tuple_list(pydir + "/" + dsl_file, grammar_name)
        outfile = grammar_name + ".ml"
        with open(ocamldir + "/" + outfile, "w") as fh:
            fh.write(rules)

def convert(py_path, ml_dir):
    grammar_name = os.path.basename(py_path).replace(".py", "")
    rules = get_ocaml_tuple_list(py_path, grammar_name)
    ml_path = ml_dir + "/" + grammar_name + ".ml"
    with open(ml_path, "w") as fh:
        fh.write(rules)

template = """
  open Normalize_rules

  let coq_dir = Sys.argv(1)

  let ebnf_grammars = {}

  let f ((g, nm) : ebnf_grammar * string) : unit =
    write_coq_grammar_file g nm (Sys.argv(1) ^ "/" ^ nm ^ ".v")

  List.iter f ebnf_grammars
"""

"""
def make_ocaml_to_coq_script(ocamldir):
    grammar_names = [s.replace(".ml", "") for s in os.listdir(ocamldir)]
    tuples = ["({},{})".format(n, json.dumps(n)) for n in grammar_names]
    script_contents = template.format(ocaml_list_repr(tuples))
    with open("ocaml_grammars_to_coq.ml", "w") as fh:
        fh.write(script_contents)
""" 
if __name__ == "__main__":
    py_path, ml_dir = sys.argv[1:3]
    convert(py_path, ml_dir)
