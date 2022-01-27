all: parser # evaluation
.PHONY: all

parser: CoqMakefile
	$(MAKE) -f CoqMakefile
	mv *.mli *.ml Evaluation/Benchmarking/Extracted
.PHONY: parser

evaluation:
	cd Evaluation/Benchmarking && dune build --profile release runEval.exe
.PHONY: evaluation

clean:
	$(MAKE) -f CoqMakefile clean
	rm Evaluation/Benchmarking/Extracted/*
#	$(MAKE) -C evaluation clean
.PHONY: clean

CoqMakefile: _CoqProject
	coq_makefile -Q ~/projects/Verbatim Verbatim -f _CoqProject -o CoqMakefile

# Run "make" to build the parser and the evaluation framework
# before running these benchmarks

bench-ppm:
	Evaluation/Benchmarking/_build/default/runEval.exe -ppm Evaluation/Data/PPM 10 Evaluation/Results/ppm_results.json
	python3.7 Evaluation/Results/plot.py Evaluation/Results/ppm_results.json Evaluation/Results/ppm_results.pdf

bench-json-nobel:
	$(MAKE) -C evaluation bench-json-nobel

bench-xml-plos:
	$(MAKE) -C evaluation bench-xml-plos

bench-dot:
	$(MAKE) -C evaluation bench-dot

bench-python3:
	$(MAKE) -C evaluation bench-python3
