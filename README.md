# CoStar
A parser based on the ALL(*) algorithm, implemented and verified with Coq.

### Building the Project

(All shell commands are run from the project root.)

To build the parser and the evaluation framework:

```
make
```

To clean:

```
make clean
```

(Building the parser takes ~3 minutes; building the evaluation framework takes ~5 minutes.)

### Running the Benchmarks

To run an experiment:

```
make bench-<benchmark_name>
```

Example:

```
make bench-json-nobel
```

The command above tokenizes the json-nobel data set (if it hasn't been tokenized already), uses a CoStar JSON parser to parse the data, and creates a plot of input size vs. parse time called json-nobel.eps in evaluation/results.

Benchmark options:

- ```json-nobel``` : Nobel Prize historical data in JSON format
- ```xml-plos```   : PLoS journal articles with XML annotations
- ```dot```        : DOT data from the ANTLR 4 performance evaluation
- ```python3```    : files from the Python 3.6.12 standard library

### Parser Dependencies

(Version numbers are for versions used during development/testing; other versions might work, too.)

* Coq 8.11.2

* CoLoR 1.7.0 (Coq Library on Rewriting and Termination)

  * Installation:

    ```
        opam repo add coq-released https://coq.inria.fr/opam/released
        opam update
        opam install --jobs=$n coq-color
    ```

  * License: CeCILL (French free software license, GPL-compatible)



