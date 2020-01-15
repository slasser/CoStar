To run the benchmark:

evaluate the ExtractJsonParser.v file, e.g., in Proof General (extracts the parser code to OCaml)

`./build.sh` (compiles the parser and test code)

`./run_eval.native <data_directory> <number_of_trials_per_data_file> <benchmark_stats_file>`

example: `./run_eval.native data 10 results.json`


`python plot.py <benchmark_stats_file> <plot_file>`

example: `python plot.py results.json results.eps`
