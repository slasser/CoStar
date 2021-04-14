all: run_eval.exe

# Change this to the location of your ANTLR JAR
ANTLR_JAR     := /usr/local/lib/antlr-4.8-complete.jar

# Change this to the location of your JSON-Java JAR
JSON_JAVA_JAR := /usr/local/lib/json-20200518.jar

# CONVERT ANTLR GRAMMARS INTO OCAML DATA STRUCTURES

GRAMMARS := grammars

ANTLR4      := antlr4
SEXP        := sexp
COQ_BNF     := coq_bnf
OCAML_BNF   := ocaml_bnf

GRAMMAR_NAMES := Python3 Json Dot Xml

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
        for VFILE in *.v; do coqc -Q ../../../parser CoStar $${VFILE}; done && \
	echo "Require Extraction.\nRequire Import $(GRAMMAR_NAMES).\nExtraction Blacklist List String.\nSeparate Extraction $(GRAMMAR_NAMES)." > ExtractGrammars.v && \
	coqc -Q ../../../parser CoStar ExtractGrammars.v && \
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

$(DATA)/Python3Lexer.java $(DATA)/Python3Parser.java: $(GRAMMARS)/$(ANTLR4)/Python3.g4
	cp $(GRAMMARS)/$(ANTLR4)/Python3.g4 $(DATA) \
        && cd $(DATA) \
        && java -jar $(ANTLR_JAR) Python3.g4

$(DATA)/TokenizeTestData.class: $(DATA)/Python3Lexer.java $(DATA)/Python3Parser.java $(DATA)/TokenizeTestData.java
	cd $(DATA) \
        && javac -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) TokenizeTestData.java

# Tokenize JSON data

JSON_NOBEL  := json-nobel

$(DATA)/$(TOKENIZED)/$(JSON_NOBEL): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(JSON_NOBEL)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(JSON_NOBEL) \
        && java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Json.g4 $(RAW)/$(JSON_NOBEL) $(TOKENIZED)/$(JSON_NOBEL)

# Tokenize XML PLoS data

XML_PLOS := xml-plos

$(DATA)/$(TOKENIZED)/$(XML_PLOS): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(XML_PLOS)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(XML_PLOS) \
        && java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/XMLLexer.g4 $(RAW)/$(XML_PLOS) $(TOKENIZED)/$(XML_PLOS)

# Tokenize DOT data

DOT := dot

$(DATA)/$(TOKENIZED)/$(DOT): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(DOT)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(DOT) \
        && java -Xmx6g -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           TokenizeTestData ../$(GRAMMARS)/$(ANTLR4)/Dot.g4 $(RAW)/$(DOT) $(TOKENIZED)/$(DOT)

# Tokenize Python3 data

PYTHON3 := python3

$(DATA)/$(TOKENIZED)/$(PYTHON3): $(DATA)/TokenizeTestData.class $(DATA)/$(RAW)/$(PYTHON3)
	cd $(DATA) \
        && mkdir -p $(TOKENIZED)/$(PYTHON3) \
        && java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR)\
           TokenizeTestData python3 $(RAW)/$(PYTHON3) $(TOKENIZED)/$(PYTHON3)

# RUN COSTAR BENCHMARKS AND PLOT RESULTS

RESULTS := results

JSON_COSTAR_PARSER   := json__costar-parser
XML_COSTAR_PARSER    := xml__costar-parser
DOT_COSTAR_PARSER    := dot__costar-parser
PYTHON_COSTAR_PARSER := python__costar-parser

bench-costar-json: run_eval.exe $(DATA)/$(TOKENIZED)/$(JSON_NOBEL)
	ulimit -s unlimited  \
        &&  ./run_eval.exe -json $(DATA)/$(TOKENIZED)/$(JSON_NOBEL) $(RESULTS)/$(JSON_COSTAR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(JSON_COSTAR_PARSER).json $(JSON_COSTAR_PARSER).eps

bench-costar-xml: run_eval.exe $(DATA)/$(TOKENIZED)/$(XML_PLOS) $(RESULTS)/plot.py
	ulimit -s unlimited  \
	&& ./run_eval.exe -xml $(DATA)/$(TOKENIZED)/$(XML_PLOS) $(RESULTS)/$(XML_COSTAR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(XML_COSTAR_PARSER).json $(XML_COSTAR_PARSER).eps

bench-costar-dot: run_eval.exe $(DATA)/$(TOKENIZED)/$(DOT)
	ulimit -s unlimited \
	&& ./run_eval.exe -dot $(DATA)/$(TOKENIZED)/$(DOT) $(RESULTS)/$(DOT_COSTAR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(DOT_COSTAR_PARSER).json $(DOT_COSTAR_PARSER).eps

bench-costar-python: run_eval.exe $(DATA)/$(TOKENIZED)/$(PYTHON3) $(RESULTS)/plot.py
	ulimit -s unlimited \
	&& ./run_eval.exe -python3 $(DATA)/$(TOKENIZED)/$(PYTHON3) $(RESULTS)/$(PYTHON_COSTAR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(PYTHON_COSTAR_PARSER).json $(PYTHON_COSTAR_PARSER).eps

# Benchmark ANTLR lexers and parser interpreters

ANTLR_BASELINE := antlr_baseline

$(ANTLR_BASELINE)/BenchmarkANTLR.class : $(ANTLR_BASELINE)/BenchmarkANTLR.class $(ANTLR_BASELINE)/JSON.g4 $(ANTLR_BASELINE)/XMLLexer.g4 $(ANTLR_BASELINE)/XMLParser.g4 $(ANTLR_BASELINE)/DOT.g4 $(ANTLR_BASELINE)/Python3.g4
	cd $(ANTLR_BASELINE) \
        && java -jar $(ANTLR_JAR) JSON.g4 \
        && java -jar $(ANTLR_JAR) XMLLexer.g4 XMLParser.g4 \
        && java -jar $(ANTLR_JAR) DOT.g4 \
        && java -jar $(ANTLR_JAR) Python3.g4 \
	&& javac -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) *.java

JSON_ANTLR_LEXER    := json__antlr-lexer
JSON_ANTLR_PARSER   := json__antlr-parser

XML_ANTLR_LEXER     := xml__antlr-lexer
XML_ANTLR_PARSER    := xml__antlr-parser

DOT_ANTLR_LEXER     := dot__antlr-lexer
DOT_ANTLR_PARSER    := dot__antlr-parser

PYTHON_ANTLR_LEXER  := python__antlr-lexer
PYTHON_ANTLR_PARSER := python__antlr-parser

bench-json-antlr-lexer : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                         $(ANTLR_BASELINE)/$(DATA)/$(JSON_NOBEL)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR json lexer $(DATA)/$(JSON_NOBEL) ../$(RESULTS)/$(JSON_ANTLR_LEXER).json
	cd $(RESULTS) && python3.7 plot.py $(JSON_ANTLR_LEXER).json $(JSON_ANTLR_LEXER).eps

bench-json-antlr-parser : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                          $(ANTLR_BASELINE)/$(DATA)/$(JSON_NOBEL)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR json parser $(DATA)/$(JSON_NOBEL) ../$(RESULTS)/$(JSON_ANTLR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(JSON_ANTLR_PARSER).json $(JSON_ANTLR_PARSER).eps

bench-xml-antlr-lexer : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                        $(ANTLR_BASELINE)/$(DATA)/$(XML_PLOS)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR xml lexer $(DATA)/$(XML_PLOS) ../$(RESULTS)/$(XML_ANTLR_LEXER).json
	cd $(RESULTS) && python3.7 plot.py $(XML_ANTLR_LEXER).json $(XML_ANTLR_LEXER).eps

bench-xml-antlr-parser : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                         $(ANTLR_BASELINE)/$(DATA)/$(XML_PLOS)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR xml parser $(DATA)/$(XML_PLOS) ../$(RESULTS)/$(XML_ANTLR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(XML_ANTLR_PARSER).json $(XML_ANTLR_PARSER).eps

bench-dot-antlr-lexer : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                        $(ANTLR_BASELINE)/$(DATA)/$(DOT)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR dot lexer $(DATA)/$(DOT) ../$(RESULTS)/$(DOT_ANTLR_LEXER).json
	cd $(RESULTS) && python3.7 plot.py $(DOT_ANTLR_LEXER).json $(DOT_ANTLR_LEXER).eps

bench-dot-antlr-parser : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                         $(ANTLR_BASELINE)/$(DATA)/$(DOT)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR dot parser $(DATA)/$(DOT) ../$(RESULTS)/$(DOT_ANTLR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(DOT_ANTLR_PARSER).json $(DOT_ANTLR_PARSER).eps

bench-python-antlr-lexer : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                           $(ANTLR_BASELINE)/$(DATA)/$(PYTHON3)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR python lexer $(DATA)/$(PYTHON3) ../$(RESULTS)/$(PYTHON_ANTLR_LEXER).json
	cd $(RESULTS) && python3.7 plot.py $(PYTHON_ANTLR_LEXER).json $(PYTHON_ANTLR_LEXER).eps

bench-python-antlr-parser : $(ANTLR_BASELINE)/BenchmarkANTLR.class \
                            $(ANTLR_BASELINE)/$(DATA)/$(PYTHON3)
	cd $(ANTLR_BASELINE) \
	&& java -cp .:$(ANTLR_JAR):$(JSON_JAVA_JAR) \
           BenchmarkANTLR python parser $(DATA)/$(PYTHON3) ../$(RESULTS)/$(PYTHON_ANTLR_PARSER).json
	cd $(RESULTS) && python3.7 plot.py $(PYTHON_ANTLR_PARSER).json $(PYTHON_ANTLR_PARSER).eps

clean:
	rm -f  $(GRAMMARS)/GrammarConverter.class
	rm -rf $(GRAMMARS)/_build
	rm -f  $(GRAMMARS)/normalize_rules.exe
	rm -rf $(GRAMMARS)/$(COQ_BNF)
	rm -rf $(GRAMMARS)/$(OCAML_BNF)
	rm -rf $(BENCHMARKING)/_build
	find   $(BENCHMARKING) -type f -not -name "dune" -not -name "run_eval.ml" -delete
	rm -f  run_eval.exe
	rm -f  $(DATA)/Python3*
	rm -f  $(DATA)/TokenizeTestData.class
	rm -rf $(DATA)/$(TOKENIZED)
	find   $(RESULTS) -type f -not -name "plot.py" -delete

.PHONY: all clean bench-json-nobel bench-xml-plos bench-dot bench-python3
