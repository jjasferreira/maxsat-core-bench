# maxsat-core-bench

A Python implementation of the MSU3 algorithm for solving MaxSAT problems. This tool supports two core extraction methods: assumption-based (standard) and proof-based (using DRAT-trim).

## Prerequisites

### Python dependencies
The solver requires `python-sat` (PySAT). Install it via pip:
```bash
pip install python-sat
```

### External tools (proof-based mode)
If you intend to use the `--proof` flag, you must have the DRAT-trim binary in the same directory as the script.

1. [Clone](https://github.com/marijnheule/drat-trim) or [download](https://www.cs.utexas.edu/~marijn/drat-trim/) `drat-trim`, and build it.
2. Ensure it is executable: `chmod +x drat-trim`, and in the same directory as the script.

## Usage
Run the solver by providing a WCNF formula file:
```bash
python script.py -f path/to/formula.wcnf
```

### Command line arguments

| Argument          | Description |
| ------------------| ----------- |
| `-c`, `--core`    | Print extracted UNSAT cores analysis |
| `-f`, `--file`    | **Required** path to the input WCNF formula |
| `-p`, `--proof`   | Use proof-based extraction (DRAT-trim) instead of assumption-based (default) |
| `-s`, `--solver`  | SAT solver to use - e.g., g3 (default), cadical |
| `-t`, `--time`    | Track and print total execution time |
| `-v`, `--verbose` | Enable verbose output for debugging |