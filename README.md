Assignments realized for course CSC_51051_EP - Computational logic: From Artificial Intelligence to Zero bugs (Logique Informatique: de l'Intelligence Artificielle à l'Absence d'erreurs)

## TD1: Typing a simple programming language

- Definition of a toy functional language with basic arithmetic operations, if-else branching and pair manipulation.

- Formulation of type inference rules and implementation of type inference algorithms.

- Formulation of reduction rules and implmentation of reduction algorithms.

- (TODO) Addition of functions. This would require augmenting the current language with:

    - Hindley-Milner type inference algorithm and typing environment during type inference.
    
    - Program value, function closure and environment during reduction.

## TD2: Satisfiability of boolean formulas

- Implementation of various sat solvers using brute force and DPLL algorithm.

- Integration of MOM (for Maximum number of Occurrences in the Minimum length) and Jeroslow-Wang heuristics.

- Implementation of a parser of DIMACS CNF format formulas and test on examples.

- Encoding of a sudoku problem into propositional logic formulas.

- Implementation of a sudoku solver based on sat solver.

- Implementation of a CNF-conversion algorithm. 

## TD3: The lambda-calculus

- Implementation of alpha-, beta-, and eta- equivalence over lambda calculus.

- Definition of different untyped lambda-terms, including booleans, conditional branches, Church natural numbers, operations and predicates over natural numbers, pairs and the Y combinator.

- Implementation of De Bruijn indices and lambda-term operations over that.
