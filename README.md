
# First Order Quantified Separators

This repository contains code to generate a first order formula which separates a set of positive and negative first order models over some given signature.

**Note: See the [pldi20-artifact](https://github.com/jrkoenig/folseparators/tree/pldi20-artifact) branch for a version which matches our PLDI20 paper.**

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
    keywords = {invariant inference, first-order logic},
    location = {London, UK},
    series = {PLDI 2020}
    }

## Requirements

This code requires `python3` with `z3py` installed. Additionally, if CVC4 is used then `cvc4` must be on the path.

## Example Command

`python3 -m separators conjectures/toy_lock_simple.fol`

Sample output:

```
...
prefix A x_1_0:node E x_0_0:epoch A x_1_1:node matrix (~le(x_0_0, ep(x_1_1)) | ~locked(zero, x_1_1) | x_1_0 = x_1_1)
expanded nodes: 200/350
prefix A x_0_0:epoch E x_1_0:node A x_1_1:node matrix (~locked(x_0_0, x_1_1) | x_1_0 = x_1_1)
Optimize checking if there is a formula of size <= 1 (lower 0 upper 2)
Couldn't solve problem
Learned new possible formula:  forall E:epoch. exists N1:node. forall N2:node. (~locked(E, N2) | N1 = N2)
Checking formula
formula matches!
forall E:epoch. exists N1:node. forall N2:node. (~locked(E, N2) | N1 = N2)
{"success":true,"total_time":1.3309106826782227,"separation_time":1.1731467247009277,"counterexample_time":0.15776395797729492,"matrix_time":0.0,"model_count":6,"formula":"forall E:epoch. exists N1:node. forall N2:node. (~locked(E, N2) | N1 = N2)","formula_quantifiers":3,"error":"","sep_algo":"hybrid","action":"learn"}
```

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
- `separate.py`: given a set of postive and negative models, infer a formula which separates them via a `Separator` object.
- `experiments/run_experiment.py`: runs `learn.py` on all of the examples in a `extracted.json` file, and produces a `results.json` file

## Data files

- `problems/`: contains a few simple seperation problems, created by hand. These are only suitable for debugging.
- `conjectures/`: contains conjectures suitable for the learning process. The root level contains toy lock invariants, which are the simplest real-world tests of the learning process.
- `conjectures/extracted/`: contains conjectures extracted from a number of correct ivy protocols. These are suitable as a development test set.

## License

This code in `separators/` is copyright 2020 Stanford University, and is available under the Apache 2.0 License (`LICENSE.txt`). Some other data and file(s) in this distribution are under copyright by other author(s).
