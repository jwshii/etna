# Using Etna with Coq

Etna provides an interface for Coq, currently focusing on [QuickChick](https://github.com/QuickChick/QuickChick).

This documentation aims to provide;

1. A description of Coq specific parts of Etna
2. A description of how Etna interacts with QuickChick and Coq
3. A lightweight introduction to running Etna with Coq workloads

Etna has mainly two subdirectories,
`bench-suite` and `bench-tool`. Benchtool
defines the Python backend of Etna for
interfacing with different workloads and
languages.

The relevant part of Benchtool for Coq is
`Coq.py`, which defines the current Coq interface. Each language interface defines
the necessary idioms and mechanisms for
building, running, and gathering the results
of the workloads. Interested reader is
encouraged to start with three interface
functions used in the experiments,
`_preprocess`, `_build`, `_run_trial`.

`bench-suite/Coq` consists of four workloads,
BinarySearchTree, RedBlack, IFC, and STLC.
It also has a cleanup script called `remove.sh`
for removing all auto-generated files.

Workloads use a set of common idioms to
allow seamless interfacing with Etna.

Each workload has;

1. **A Src directory** with the implementation and the specification.
2. **A Methods directory** with the generators.
3. **A Runners directory** with the `runner` files. Runners are auto-generated from generator files by extraction tests using a comment-based preprocessing mechanism. They allow Etna to extract property-tests to OCaml for compiling and running.
4. **A _CoqProject file** that defines the project files. Etna dynamically preprocesses this file to add the runners as they are generated.

The Etna pipeline for Coq (for QuickChick) goes as follows;

1. **Preprocessing:** For all methods, create their corresponding runner files and modify `_CoqProject`.
2. **Build Part 1:** Using the standart `coq_makefile`, run `make` on the project, creating the corresponding `.ml` files for each runner.
3. **Build Part 2:** Compile each `<runner>.ml` into a separate executable.
4. **Run Trials:** Run each executable with the given number of trials, collect the results.
5. **Analysis:** Apply any type of analysis on the generated results.

## Running Coq Workloads With Etna

There are several example experiment scripts within `experiments/coq-experiments`
directory. The experiments used in the paper are inside the `exp5.1` directory,
while rest of the experiments demonstrate running each workload separately.

You can easily run these experiments at the root directory level.

For example, to run BinarySearchTree workload, you can run the command below.

`python experiments/coq-experiments/BST.py`

`<workload>_exp_cfg.json` files allow bypassing boring property/mutant pairs,
allowing you to run only experiments where a mutant is falsifying a property.

## Creating a New Coq Workload with Etna

To create a new workload, start by creating `Methods`, `Runners`
and `Src` directories as well as a `_CoqProject` file. Once you have your
generators in the `Methods` directory, and your implementation in the `Src` directory,
you should be easily able to run your new workload.

In time, we will add scripts for auto-generating these workloads/experiments as well as
easier ways of migrating existing Coq codebases.



