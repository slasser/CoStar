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

The command above tokenizes the json-nobel data set (if it hasn't been tokenized already), uses a CoStar JSON parser to parse the data, and creates a plot of input size vs. parse time called json-nobel.eps in `evaluation/results`.

Benchmark options:

- ```json-nobel``` : Nobel Prize historical data in JSON format
- ```xml-plos```   : PLoS journal articles with XML annotations
- ```dot```        : DOT data from the ANTLR 4 performance evaluation
- ```python3```    : files from the Python 3.6.12 standard library

### Parser Dependencies

(Version numbers are for versions used during development/testing; other versions might work, too.)

* Coq 8.11.2

* [CoLoR 1.7.0](http://color.inria.fr/) (Coq Library on Rewriting and Termination)

  * Installation:

    ```
        opam repo add coq-released https://coq.inria.fr/opam/released
        opam update
        opam install --jobs=$n coq-color
    ```

  * License: CeCILL (French free software license, GPL-compatible)

### Evaluation Framework Dependencies

* OCaml 4.11.1+flambda

* Dune 2.7.1

* Core_kernel 0.14.0 (OCaml library)

* Yojson 1.7.0 (OCaml library)

* Java 8 (e.g., openjdk 1.8.0_275)

* [ANTLR 4.8](https://www.antlr.org)

  * The JAR is available at [https://www.antlr.org/download](https://www.antlr.org/download).

* [JSON-Java](https://github.com/stleary/JSON-java) (Java library for reading and writing JSON data)

  * The JAR is available at the link above.
  * Note: the evaluation framework assumes that the ANTLR and JSON-Java JARs are located in `/usr/local/lib`. You can set a different location by editing `evaluation/Makefile`.

* Python 3.7.9

* numpy (Python library)

* matplotlib (Python library)

* statsmodels (Python library)



