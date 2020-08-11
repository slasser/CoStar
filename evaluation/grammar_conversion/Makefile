# directories for each stage of the "ANTLR to OCaml" pipeline
ANTLR_EBNF  := antlr4_grammars
PYTHON_EBNF := python_ebnf_grammars
OCAML_EBNF  := ocaml_ebnf_grammars
COQ_BNF     := coq_bnf_grammars
OCAML_BNF   := ocaml_bnf_grammars

RRDANTLR4_OUTPUT := output

GRAMMARS    := Json

all: .depend

GrammarConverter.class:
	javac -cp .:rrd-antlr4-0.1.2.jar GrammarConverter.java

$(PYTHON_EBNF): GrammarConverter.class
	mkdir -p $(PYTHON_EBNF)
	$(foreach G, $(GRAMMARS), \
            java -cp .:rrd-antlr4-0.1.2.jar GrammarConverter $(ANTLR_EBNF)/$(G).g4 $(PYTHON_EBNF); )
	rm -r $(RRDANTLR4_OUTPUT)

$(OCAML_EBNF): $(PYTHON_EBNF)
	mkdir -p $(OCAML_EBNF)
	$(foreach G, $(GRAMMARS), \
	    python process_railroad_dsl.py $(PYTHON_EBNF)/$(G).py $(OCAML_EBNF); )

$(COQ_BNF): $(OCAML_EBNF)
	mkdir -p $(COQ_BNF)
	$(foreach G, $(GRAMMARS), \
	    @echo "#require \"str\"                                            ;; \n \
                   #require \"yojson\"                                         ;; \n \
                   #use \"normalize_rules.ml\"                                 ;; \n \
                   #use \"$(OCAML_EBNF)/$(G).ml\"                              ;; \n \
	           write_coq_grammar_file rules \"$(G)\" \"$(COQ_BNF)/$(G).v\" ;;" | utop; )

$(OCAML_BNF): $(COQ_BNF)
	mkdir -p $(OCAML_BNF)
	coqc -Q ../../parser GallStar $(COQ_BNF)/*.v
	@echo "Require Extraction.\nRequire Import $(GRAMMARS).\nSeparate Extraction $(GRAMMARS)." \
	> $(COQ_BNF)/ExtractGrammars.v
	cd $(COQ_BNF) && coqc -Q ../../../parser GallStar ExtractGrammars.v
	mv $(COQ_BNF)/*.ml $(COQ_BNF)/*.mli $(OCAML_BNF)

.depend: $(OCAML_BNF)
	ocamldep $(OCAML_BNF)/*.mli $(OCAML_BNF)/*.ml run_eval.ml > .depend

include .depend

clean:
	rm -f  GrammarConverter.class
	rm -rf $(PYTHON_EBNF)
	rm -rf $(OCAML_EBNF)
	rm -rf $(COQ_BNF)
	rm -rf $(OCAML_BNF)

.PHONY: all clean
