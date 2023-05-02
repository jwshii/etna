(TODO: These instructions have not been updated for Coq.)

# What is where?

- `bench-suite` is the benchmark suite, with one subdirectory per language.
- `bench-tool` is the benchmark tool, written in Python.

# How do I install?

1. Clone this repository.

    Haskell (including `stack`) and Python 3.10.5 (including `pip`) are required.

2. Run `make install`.

    This installs the Python tool.

# How do I run?

Experiment scripts are stored in the `experiments` directory. 
To check that the installation worked, try running

```
python3 experiments/haskell-experiments/One.py
```

# How do I add?


To add support for a new language `L`, add a new file in `bench-tool/benchtool` named `L.py`.
See `Haskell.py` as an example. 

The tool assumes the following directory structure: 

```
Haskell                  -- config.path: top-level directory for the language
│
└─── common              -- config.ignore: directory for shared code
│
│
└─── BST                 -- one directory per benchmark
│   │
│   │   Impl.hs          -- config.impl: file containing all mutants
│   │   Spec.hs          -- arbitrary other files without mutants
│   │
│   └─── methods         -- config.methods: directory with one file per method
│           QuickCheck.hs        
│           SmallCheck.hs 
...   
```

For the Python code, we use the `yapf` formatter and `mypy` typing hints.  
See `Haskell2.md` for how to add a new workload.
