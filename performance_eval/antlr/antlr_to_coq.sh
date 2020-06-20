ANTLR_DIR=antlr4_grammars
PY_DIR=python_ebnf_grammars
OCAML_DIR=ocaml_ebnf_grammars
COQ_DIR=coq_grammars

# Create directories for different grammar representations
for dir in $PY_DIR $OCAML_DIR $COQ_DIR; do
    mkdir -p $dir
done

javac -cp .:rrd-antlr4-0.1.2.jar GrammarConverter.java

GRAMMARS="Json XMLParser"

for G in $GRAMMARS ; do
    # Convert ANTLR4 grammar to a Python object representation
    java  -cp .:rrd-antlr4-0.1.2.jar GrammarConverter ${ANTLR_DIR}/${G}.g4 $PY_DIR
    # Convert Python grammar to an OCaml representation
    python process_railroad_dsl.py $PY_DIR/${G}.py $OCAML_DIR
    # Convert OCaml EBNF grammar to a Coq BNF grammar
    COQ_FNAME=${COQ_DIR}/${G}.v
    echo "#require \"str\"                                       ;;
          #require \"yojson\"                                    ;;
          #use \"normalize_rules.ml\"                            ;;
          #use \"${OCAML_DIR}/${G}.ml\"                          ;;
          write_coq_grammar_file rules \"${G}\" \"${COQ_FNAME}\" ;;" | utop
done
