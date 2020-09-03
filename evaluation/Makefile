all: run_eval.exe

# CONVERT ANTLR GRAMMARS INTO OCAML DATA STRUCTURES

# Directory where the "ANTLR to OCaml" grammar conversion pipeline runs
GRAMMARS := grammars
# directories for each stage of the pipeline
ANTLR4      := antlr4
SEXP        := sexp
COQ_BNF     := coq_bnf
OCAML_BNF   := ocaml_bnf

GRAMMAR_NAMES := Lua Json Dot Erlang

$(GRAMMARS)/normalize_rules.exe: $(GRAMMARS)/normalize_rules.ml
	cd $(GRAMMARS) && dune build --profile release normalize_rules.exe \
                       && cp -f _build/default/normalize_rules.exe .

$(GRAMMARS)/$(COQ_BNF): $(GRAMMARS)/normalize_rules.exe $(GRAMMARS)/$(SEXP)
	mkdir -p $(GRAMMARS)/$(COQ_BNF)
	cd $(GRAMMARS)                                                   \
	&& for G in $(GRAMMAR_NAMES); do                                 \
             ./normalize_rules.exe $(SEXP)/$${G}.sxp $(COQ_BNF)/$${G}.v; \
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

run_eval.exe: $(GRAMMARS)/$(OCAML_BNF) $(BENCHMARKING)
	cp $(GRAMMARS)/$(OCAML_BNF)/* $(BENCHMARKING)
	cd $(BENCHMARKING) \
        && dune build --profile release run_eval.exe \
        && cp -f _build/default/run_eval.exe ..

# TOKENIZE TEST DATA

DATA      := data
RAW       := raw
TOKENIZED := tokenized

$(DATA)/TokenizeTestData.class: $(DATA)/TokenizeTestData.java
	cd $(DATA) \
        && javac -cp ../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar TokenizeTestData.java

# Tokenize JSON data sets

JSON_CITIES := json_cities
JSON_NOBEL  := json_nobel

$(DATA)/$(TOKENIZED)/$(JSON_CITIES): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(JSON_CITIES)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(JSON_CITIES) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Json.g4 $(RAW)/$(JSON_CITIES) $(TOKENIZED)/$(JSON_CITIES)

$(DATA)/$(TOKENIZED)/$(JSON_NOBEL): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(JSON_NOBEL)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(JSON_NOBEL) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Json.g4 $(RAW)/$(JSON_NOBEL) $(TOKENIZED)/$(JSON_NOBEL)

# Tokenize DOT data from Terence Parr

DOT := dot

$(DATA)/$(TOKENIZED)/$(DOT): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(DOT)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(DOT) \
        && java -Xmx6g -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Dot.g4 $(RAW)/$(DOT) $(TOKENIZED)/$(DOT)

# Tokenize Erlang data from Terence Parr

ERLANG := erlang

$(DATA)/$(TOKENIZED)/$(ERLANG): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(ERLANG)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(ERLANG) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Erlang.g4 $(RAW)/$(ERLANG) $(TOKENIZED)/$(ERLANG)

ERLANG_MINIMAL := erlang_minimal

$(DATA)/$(TOKENIZED)/$(ERLANG_MINIMAL): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(ERLANG_MINIMAL)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(ERLANG_MINIMAL) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Erlang.g4 $(RAW)/$(ERLANG_MINIMAL) $(TOKENIZED)/$(ERLANG_MINIMAL)

# Tokenize C data from Terence Parr

C_PYTHON := c_python

$(DATA)/$(TOKENIZED)/$(C_PYTHON): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(C_PYTHON)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(C_PYTHON) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/C.g4 $(RAW)/$(C_PYTHON) $(TOKENIZED)/$(C_PYTHON)

# Tokenize Lua data from Terence Parr

LUA := lua

$(DATA)/$(TOKENIZED)/$(LUA): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(LUA)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(LUA) \
        && java -cp .:../resources/antlr-4.8-complete.jar:../resources/json-20200518.jar \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Lua.g4 $(RAW)/$(LUA) $(TOKENIZED)/$(LUA)

# RUN BENCHMARKS AND PLOT RESULTS

RESULTS := results

bench-json-cities: run_eval.exe $(DATA)/$(TOKENIZED)/$(JSON_CITIES) $(RESULTS)/plot.py
	./run_eval.exe -json $(DATA)/$(TOKENIZED)/$(JSON_CITIES) $(RESULTS)/$(JSON_CITIES).json
	cd $(RESULTS) && python plot.py $(JSON_CITIES).json $(JSON_CITIES).eps

bench-json-nobel: run_eval.exe $(DATA)/$(TOKENIZED)/$(JSON_NOBEL)
	./run_eval.exe -json $(DATA)/$(TOKENIZED)/$(JSON_NOBEL) $(RESULTS)/$(JSON_NOBEL).json
	cd $(RESULTS) && python plot.py $(JSON_NOBEL).json $(JSON_NOBEL).eps

bench-dot: run_eval.exe $(DATA)/$(TOKENIZED)/$(DOT)
	./run_eval.exe -dot $(DATA)/$(TOKENIZED)/$(DOT) $(RESULTS)/$(DOT).json
	cd $(RESULTS) && python plot.py $(DOT).json $(DOT).eps

bench-erlang: run_eval.exe $(DATA)/$(TOKENIZED)/$(ERLANG)
	./run_eval.exe -erlang $(DATA)/$(TOKENIZED)/$(ERLANG) $(RESULTS)/$(ERLANG).json
	cd $(RESULTS) && python plot.py $(ERLANG).json $(ERLANG).eps

bench-erlang-minimal: run_eval.exe $(DATA)/$(TOKENIZED)/$(ERLANG_MINIMAL)
	./run_eval.exe -erlang $(DATA)/$(TOKENIZED)/$(ERLANG_MINIMAL) $(RESULTS)/$(ERLANG_MINIMAL).json
	cd $(RESULTS) && python plot.py $(ERLANG_MINIMAL).json $(ERLANG_MINIMAL).eps

bench-c-python: run_eval.exe $(DATA)/$(TOKENIZED)/$(C_PYTHON) $(RESULTS)/plot.py
	./run_eval.exe -c $(DATA)/$(TOKENIZED)/$(C_PYTHON) $(RESULTS)/$(C_PYTHON).json
	cd $(RESULTS) && python plot.py $(C_PYTHON).json $(C_PYTHON).eps

bench-lua: run_eval.exe $(DATA)/$(TOKENIZED)/$(LUA) $(RESULTS)/plot.py
	./run_eval.exe -lua $(DATA)/$(TOKENIZED)/$(LUA) $(RESULTS)/$(LUA).json
	cd $(RESULTS) && python plot.py $(LUA).json $(LUA).eps

clean:
	rm -f  $(GRAMMARS)/GrammarConverter.class
	rm -rf $(GRAMMARS)/_build
	rm -f  $(GRAMMARS)/normalize_rules.exe
	rm -rf $(GRAMMARS)/$(COQ_BNF)
	rm -rf $(GRAMMARS)/$(OCAML_BNF)
	rm -rf $(BENCHMARKING)/_build
	find   $(BENCHMARKING) -type f -not -name "dune" -not -name "run_eval.ml" -delete
	rm -f  run_eval.exe
	rm -f  $(DATA)/TokenizeTestData.class
	rm -rf $(DATA)/$(TOKENIZED)
	find   $(RESULTS) -type f -not -name "plot.py" -delete

.PHONY: all clean bench-c-python bench-json-cities bench-json-nobel bench-dot bench-erlang