import json, os, sys
from railroad import *

def ocaml_list_repr(xs):
    """Convert a list of strings to a string repr of a valid OCaml list"""
    return "[{}]".format("; ".join(xs))

def get_rhss(diag):
    "Extract the Sequence nodes that represent production right-hand sides"""
    assert isinstance(diag, Diagram)
    choice = diag.items[2]
    assert isinstance(choice, Choice)
    seqs = choice.items
    for seq in seqs:
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
        return "Terminal " + json.dumps(elt.text)
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
            rhss = get_rhss(diag)
            for rhs in rhss:
                prods.append(str_of_production(lhs, rhs))
        return prods

def get_ocaml_tuple_list(dsl_file):
    """Read a .py file in which each line represents an ANTLR rule
       ---i.e., a (string, railroad diagram) tuple---
       and returns a string repr of an OCaml tuple list definition
    """
    prods = get_ocaml_productions(dsl_file)
    return "let rules = [\n\n" + ";\n\n".join(prods) + "\n\n]"

def convert_all_files(indir, outdir):
    """Convert each Python representation of an ANTLR grammar in indir
    to an equivalent OCaml representation in outdir"""
    if not os.path.exists(outdir):
        os.mkdir(outdir)
    for dsl_file in os.listdir(indir):
        rules = get_ocaml_tuple_list(indir + "/" + dsl_file)
        outfile = dsl_file.replace(".py", ".ml")
        with open(outdir + "/" + outfile, "w") as fh:
            fh.write(rules)

if __name__ == "__main__":
    convert_all_files(sys.argv[1], sys.argv[2])

            


