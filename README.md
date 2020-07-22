
# First Order Logic Separators

This repository contains code to generate a first order formula which separates a set of positive and negative first order models over some given signature.

**This branch represents the version available in the [artifact](https://doi.org/10.1145/3395650) of the PLDI20 paper. The artifact includes the correct version of all dependencies, including python, z3, and cvc4.**

## Citation

    @inproceedings{10.1145/3385412.3386018,
    author = {Koenig, Jason R. and Padon, Oded and Immerman, Neil and Aiken, Alex},
    title = {First-Order Quantified Separators},
    year = {2020},
    isbn = {9781450376136},
    publisher = {Association for Computing Machinery},
    address = {New York, NY, USA},
    url = {https://doi.org/10.1145/3385412.3386018},
    doi = {10.1145/3385412.3386018},
    booktitle = {Proceedings of the 41st ACM SIGPLAN Conference on Programming Language Design and Implementation},
    pages = {703–717},
    numpages = {15},
    keywords = {first-order logic, invariant inference},
    location = {London, UK},
    series = {PLDI 2020}
    }

## Requirements

This code requires `python3.7` with `z3py` installed.

## Example Commands

- `python3.7 -m separators --separate problems/every_edge_triangle.fol`
- `python3.7 -m separators conjectures/toy_lock_invar11.fol`
- `python3.7 -m separators --logic=universal conjectures/toy_lock_invar7.fol`

## File format
The `.fol` file format is an s-expr based format for representing FO signatures, models, and formula. An example file (`problems/example.fol`) is:

```
; Signature
(sort A)
(function f A A) ; last sort is return value. Must have at least 1 argument sort
(relation p A)
(constant a A)

(axiom (p a)) ; more than one axiom allowed.

(conjecture (= (f a) a))

; Models. After model, there must be a label, list of elements w/sorts, and then all facts
(model + ((e0 A) (e1 A))
  ; Facts of model must be (predicate ELEMS), (= CONST ELEM), or (= (FUNC ELEMS) ELEM)
  ; Omitted predicates are false. All constant and function values for all arguments must be specified.
  (p e0)
  (= a e0)
  (= (f e0) e0)
  (= (f e1) e0)
)

(model - ((e0 A) (e1 A))
  (p e0)
  (= a e0)
  (= (f e0) e1)
  (= (f e1) e0)
)
```

The file consists of a series of commands: sort, function, relation, constant, axiom, conjecture, and model. The first four define the components of the signature for the file, and must appear before any axioms, conjectures, or models. Comments are semicolon to end of line.

Axioms are formula which must be true for all models. Conjectures should be true for positive models and false for negative models. Axioms, conjectures, and models are all optional, but some may be required for some commands. For example, `separate.py` requires models, but ignores conjectures, while `learn.py` ignores models and requires a conjecture.

Formula may have quantifiers. An axiom `forall x:Node. forall y:Node. (~(edge(x, y)) | edge(y, x))` is written:

```
(axiom (forall x Node (forall y Node
          (or (not (edge x y)) (edge y x))
        )))
```

## Source Files

- `learn.py`: given a signature and a conjecture, runs `Separator.separate()` and generates models until enough positive and negative models exist so that the separator gives a formula equivalent to the conjecture.
- `logic.py`: defines logic objects like `Model`s, `Formula`s and `Signature`s.
- `separate.py`: given a set of positive and negative models, infer a formula which separates them via a `Separator` object.
- `experiments/run_experiment.py`: runs `learn.py` on all of the examples in a `benchmark.json` file, and produces a `results.json` file.

## Data files

- `problems/`: contains a few simple separation problems, created by hand. These are only suitable for debugging.
- `conjectures/`: contains conjectures suitable for the learning process. The root level contains toy lock invariants, which are the simplest real-world tests of the learning process.
- `conjectures/extracted/`, `conjectures/mypyvy/`: contains conjectures extracted from a number of correct Ivy and mypyvy protocols. These are suitable as a development test set.

## License

This code in `separators/` is copyright 2020 Stanford University, and is available under the Apache 2.0 License (`LICENSE.txt`). Some other data and file(s) in this distribution are under copyright by other author(s).
