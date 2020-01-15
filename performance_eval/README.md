To run the benchmark:

1. evaluate the ExtractJsonParser.v file, e.g., in Proof General (extracts the parser code to OCaml)

2. `./build.sh` (compiles the parser and test code)


3. `./run_eval.native <data_directory> <number_of_trials_per_data_file> <benchmark_stats_file>`

    * example: `./run_eval.native data 10 results.json`


4. `python plot.py <benchmark_stats_file> <plot_file>`

    * example: `python plot.py results.json results.eps`
