all: run_eval.exe

# CONVERT ANTLR GRAMMARS INTO OCAML DATA STRUCTURES

# Directory where the "ANTLR to OCaml" grammar conversion pipeline runs
GRAMMARS := grammars
# directories for each stage of the pipeline
ANTLR_EBNF  := antlr4_grammars
PYTHON_EBNF := python_ebnf_grammars
OCAML_EBNF  := ocaml_ebnf_grammars
COQ_BNF     := coq_bnf_grammars
OCAML_BNF   := ocaml_bnf_grammars
# Unused directory that rrd-antlr4 creates -- we can safely remove it
RRDANTLR4_OUTPUT := output

GRAMMAR_NAMES := Json

$(GRAMMARS)/GrammarConverter.class:
	cd $(GRAMMARS) && javac -cp ../resources/rrd-antlr4-0.1.2.jar GrammarConverter.java

$(GRAMMARS)/$(PYTHON_EBNF): $(GRAMMARS)/GrammarConverter.class
	cd $(GRAMMARS) \
	&& mkdir -p $(PYTHON_EBNF) \
        && for G in $(GRAMMAR_NAMES); do \
             java -cp .:../resources/rrd-antlr4-0.1.2.jar GrammarConverter $(ANTLR_EBNF)/$${G}.g4 $(PYTHON_EBNF); \
           done \
        && rm -rf $(RRDANTLR4_OUTPUT)

$(GRAMMARS)/$(OCAML_EBNF): $(GRAMMARS)/$(PYTHON_EBNF)
	mkdir -p $(GRAMMARS)/$(OCAML_EBNF)
	cd $(GRAMMARS) \
        && for G in $(GRAMMAR_NAMES); do    \
	     python process_railroad_dsl.py $(PYTHON_EBNF)/$${G}.py $(OCAML_EBNF); \
           done

$(GRAMMARS)/$(COQ_BNF): $(GRAMMARS)/$(OCAML_EBNF)
	mkdir -p $(GRAMMARS)/$(COQ_BNF)
	cd $(GRAMMARS) && \
        for G in $(GRAMMAR_NAMES); do    \
          echo "#require \"str\"                                              ;; \n       \
                #require \"yojson\"                                           ;; \n       \
                #use \"normalize_rules.ml\"                                   ;; \n       \
                #use \"$(OCAML_EBNF)/$${G}.ml\"                               ;; \n       \
                write_coq_grammar_file rules \"$${G}\" \"$(COQ_BNF)/$${G}.v\" ;;" | utop; \
        done

$(GRAMMARS)/$(OCAML_BNF): $(GRAMMARS)/$(COQ_BNF)
	mkdir -p $(GRAMMARS)/$(OCAML_BNF)
	cd $(GRAMMARS)/$(COQ_BNF)  && \
        for VFILE in *.v; do coqc -Q ../../../parser GallStar $${VFILE}; done && \
	echo "Require Extraction.\nRequire Import $(GRAMMAR_NAMES).\nExtraction Blacklist List String.\nSeparate Extraction $(GRAMMAR_NAMES)." > ExtractGrammars.v && \
	coqc -Q ../../../parser GallStar ExtractGrammars.v && \
	mv *.ml *.mli ../$(OCAML_BNF)

# BUILD THE EVALUATION SCRIPT

BENCHMARKING := benchmarking

run_eval.exe: $(GRAMMARS)/$(OCAML_BNF) $(BENCHMARKING)/run_eval.ml
	cp $(GRAMMARS)/$(OCAML_BNF)/* $(BENCHMARKING)
	cd $(BENCHMARKING) \
        && dune build --profile release run_eval.exe \
        && cp -f _build/default/run_eval.exe ..

# TOKENIZE TEST DATA

DATA      := data
RAW       := raw
TOKENIZED := tokenized

JSON_CITIES := json_cities
JSON_NOBEL  := json_nobel

$(DATA)/TokenizeTestData.class: $(DATA)/TokenizeTestData.java
	cd $(DATA) \
        && javac -cp ../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar TokenizeTestData.java

$(DATA)/$(TOKENIZED)/$(JSON_CITIES): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(JSON_CITIES)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(JSON_CITIES) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR_EBNF)/Json.g4 $(RAW)/$(JSON_CITIES) $(TOKENIZED)/$(JSON_CITIES)

benchmark_json_cities: run_eval.exe $(DATA)/$(TOKENIZED)/$(JSON_CITIES)
	./run_eval.exe json $(DATA)/$(TOKENIZED)/$(JSON_CITIES)

$(DATA)/$(TOKENIZED)/$(JSON_NOBEL): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(JSON_NOBEL)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(JSON_NOBEL) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR_EBNF)/Json.g4 $(RAW)/$(JSON_NOBEL) $(TOKENIZED)/$(JSON_NOBEL)

benchmark_json_nobel: run_eval.exe $(DATA)/$(TOKENIZED)/$(JSON_NOBEL)
	./run_eval.exe json $(DATA)/$(TOKENIZED)/$(JSON_NOBEL)

# RUN BENCHMARKS



clean:
	rm -f  $(GRAMMARS)/GrammarConverter.class
	rm -rf $(GRAMMARS)/$(PYTHON_EBNF)
	rm -rf $(GRAMMARS)/$(OCAML_EBNF)
	rm -rf $(GRAMMARS)/$(COQ_BNF)
	rm -rf $(GRAMMARS)/$(OCAML_BNF)
	rm -rf $(BENCHMARKING)/_build
	find   $(BENCHMARKING) -type f -not -name "dune" -not -name "run_eval.ml" -delete
	rm -f  run_eval.exe
	rm -f  $(DATA)/TokenizeTestData.class
	rm -rf $(DATA)/$(TOKENIZED)

.PHONY: all clean benchmark_json_cities benchmark_json_nobel
