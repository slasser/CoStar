all: parser # evaluation

parser:
	$(MAKE) -f CoqMakefile
	mv *.mli *.ml Evaluation

evaluation:
	cd Evaluation && dune build --profile release runEval.exe 

clean:
	$(MAKE) -f CoqMakefile clean
#	$(MAKE) -C evaluation clean

# Run "make" to build the parser and the evaluation framework
# before running these benchmarks

bench-json-nobel:
	$(MAKE) -C evaluation bench-json-nobel

bench-xml-plos:
	$(MAKE) -C evaluation bench-xml-plos

bench-dot:
	$(MAKE) -C evaluation bench-dot

bench-python3:
	$(MAKE) -C evaluation bench-python3

.PHONY: all parser evaluation clean
