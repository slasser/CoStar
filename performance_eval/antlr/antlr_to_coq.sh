# Convert ANTLR4 grammars to a Python object representation
javac -cp .:rrd-antlr4-0.1.2.jar GrammarConverter.java
java  -cp .:rrd-antlr4-0.1.2.jar GrammarConverter antlr4_grammars $1

# Convert Python grammars to an OCaml representation
python process_railroad_dsl.py $1 $2




