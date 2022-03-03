# CoStar++
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
  opam install coq-color.1.7.0
  ```

  License: CeCILL (French free software license, GPL-compatible)

### Evaluation Framework Dependencies

* OCaml libraries: Dune 2.7.1, Core_kernel 0.14.0, Yojson 1.7.0
  ```
  opam install dune.2.7.1 core_kernel.v0.14.0 yojson.1.7.0
  ```

* Python 3.7
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

### Running the Benchmarks

To run an experiment:

```
make bench-<benchmark_name>
```

Example:

```
make bench-json
```

The command above uses a CoStar JSON parser to parse the data, and creates a plot of input size vs. parse time called json-nobel.pdf in `Evaluation/Results`.

Benchmark options:

- ```json```
- ```json-small```
- ```ppm```
- ```ppm-small```
- ```newick```
- ```newick-small```
- ```xml```
- ```xml-small```



