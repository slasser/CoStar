# CoStar
A parser based on the ALL(*) algorithm, implemented and verified with Coq.

### Parser Dependencies

(Version numbers are for versions used during development/testing; other versions might work, too. Installation instructions have been tested on a machine running the Ubuntu 16.04 OS.)

* OCaml 4.11.1+flambda
  ```
  opam switch create 4.11.1+flambda
  eval $(opam env)
  ```

* Coq 8.11.2

  ```
  opam install coq.8.11.2
  ```

* [CoLoR 1.7.0](http://color.inria.fr/) (Coq Library on Rewriting and Termination)

  ```
  opam repo add coq-released https://coq.inria.fr/opam/released
  opam update
  opam install coq-color
  ```

  License: CeCILL (French free software license, GPL-compatible)

### Evaluation Framework Dependencies

* OCaml libraries: Dune 2.7.1, Core_kernel 0.14.0, Yojson 1.7.0
  ```
  opam install dune.2.7.1 core_kernel.v0.14.0 yojson.1.7.0
  ```

* Java 8 (e.g., openjdk 1.8.0_275)
  ```
  sudo apt-get install openjdk-8-jdk
  ```

* [ANTLR 4.8](https://www.antlr.org)
  ```
  cd /usr/local/lib
  sudo curl -O https://www.antlr.org/download/antlr-4.8-complete.jar
  ```

* [JSON-Java](https://github.com/stleary/JSON-java) (Java library for reading and writing JSON data)
  * The JAR is available at the link above.
  * Note: the evaluation framework assumes that the ANTLR and JSON-Java JARs are located in `/usr/local/lib`. You can set a different location by editing `evaluation/Makefile`.

* Python 3.7.9
  ```
  sudo apt-get install python3.7
  ```

* Python libraries: numpy, matplotlib, statsmodels
  ```
  pip3 install numpy matplotlib statsmodels
  ```

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



