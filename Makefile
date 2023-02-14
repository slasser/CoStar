all: parser evaluation
.PHONY: all

parser: CoqMakefile
	$(MAKE) -f CoqMakefile
	mkdir -p Evaluation/Benchmarking/Extracted
	mv *.mli *.ml Evaluation/Benchmarking/Extracted
.PHONY: parser

evaluation:
	cd Evaluation/Benchmarking && dune build --profile release runEval.exe
.PHONY: evaluation

clean:
	$(MAKE) -f CoqMakefile clean
	cd Evaluation/Benchmarking && dune clean
	find Evaluation/Benchmarking/Extracted -type f -not -name "README" -delete
	cd Evaluation/Results && rm -f *.json *.eps *.pdf
.PHONY: clean

# Replace ~/clones/Verbatim with the path to Verbatim on your system
CoqMakefile: _CoqProject
	coq_makefile -Q ~/clones/Verbatim Verbatim -f _CoqProject -o CoqMakefile

# Run "make" to build the parser and the evaluation framework
# before running these benchmarks

bench-ppm:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -ppm Evaluation/Data/PPM/Instances 10 Evaluation/Results/ppm_results.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/ppm_results.json Evaluation/Results/ppm_results.pdf

bench-ppm-small:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -ppm Evaluation/Data/PPM/SmallInstances 10 Evaluation/Results/ppm_results_small.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/ppm_results_small.json Evaluation/Results/ppm_results_small.pdf

bench-json:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -json Evaluation/Data/JSON/Instances 10 Evaluation/Results/json_results.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/json_results.json Evaluation/Results/json_results.pdf

bench-json-small:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -json Evaluation/Data/JSON/SmallInstances 10 Evaluation/Results/json_results_small.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/json_results_small.json Evaluation/Results/json_results_small.pdf

bench-newick:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -newick Evaluation/Data/Newick/Instances 10 Evaluation/Results/newick_results.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/newick_results.json Evaluation/Results/newick_results.pdf

bench-newick-small:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -newick Evaluation/Data/Newick/SmallInstances 10 Evaluation/Results/newick_results_small.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/newick_results_small.json Evaluation/Results/newick_results_small.pdf

bench-xml:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -xml Evaluation/Data/XML/Instances 10 Evaluation/Results/xml_results.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/xml_results.json Evaluation/Results/xml_results.pdf

bench-xml-small:
	ulimit -s unlimited \
	&& Evaluation/Benchmarking/_build/default/runEval.exe -xml Evaluation/Data/XML/SmallInstances 10 Evaluation/Results/xml_results_small.json
	python3.8 Evaluation/Results/plot.py Evaluation/Results/xml_results_small.json Evaluation/Results/xml_results_small.pdf
