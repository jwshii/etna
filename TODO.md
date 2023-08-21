# estimated time per type of task

- (on the ground): < 15 minutes
- (low hanging): < 1 hour
- (in a tree): a few hours
- (open ended): unknown

# Python:

- `Mutant.py`:

  - (low hanging) (bug):
    ignore commented out mutants
  - (in a tree):
    parse across multiple files
  - (in a tree):
    parse non-contiguous mutants

- `BenchTool.py`:

  - (open ended):
    make workload structure less rigid, e.g.
    automatically detect which files contain what
  - (open ended):
    consistent logging across languages
    (which may trigger a re-thinking of the interface)

- `Haskell.py`:

  - (in a tree):
    reduce compilation overhead, e.g.
    prevent files that are not used from being compiled

- `Coq.py`:

  - (low hanging):
    reduce repetitive code
  - (in a tree):
    terminate process without resorting to `pkill`

- `experiments/`:

  - (open ended):
    better abstractions —
    reduce repetitive code across similar experiments

- `Analysis.py`:

  - (open ended):
    this file was hobbled together — instead, want
    more principled collection of useful functions

- `tasks.py`:

  - (in a tree):
    make this a lot less clunky

- miscellaneous:

  - (low hanging):
    better error message when result {folder, file} is empty
  - (in a tree):
    more graceful representation of timeouts
  - (open ended) (bug):
    currently, can start/stop at the task-level
    also want to be able to do that at the trial-level
  - (open ended):
    add support for collecting other kinds of data, e.g.
    statistics in lines 264–265 of paper
  - (open ended):
    mode for testing whether strategy is behaving as expected

# Haskell:

- `etna-lib/`:

  - (on the ground):
    inconsistent argument order between `QuickCheck` and other framework
  - (on the ground):
    rename `Strategy` to `Framework`
  - (low hanging) (bug):
    fix mkStrategies to support one-argument properties
  - (in a tree):
    add support for discards
  - (in a tree):
    add back support for `hedgehog`
  - (in a tree):
    allow some properties to not be implemented by some strategies
    (this might have been fixed, not sure)

- miscellaneous:

  - (on the ground):
    add back `template.hsfiles` for creating a new workload
  - (on the ground):
    rename `Term` to `Expr` in FSUB to be consistent with STLC
    (and change variable names accordingly)
  - (in a tree):
    separate mode for collecting number of tests for
    strategies that don't explicitly compute discards
  - (open ended):
    add shrinking into the mix
