
# First Order Logic Separators

This repository contains code to generate a first order formula which separates a set of positive and negative first order models over some given signature.

## Requirements

This code requires `python3` with `z3py` installed.

## Example Commands

- `python3 separate.py problems/every_edge_triangle.fol`
- `python3 check.py problems/toy_lock_simple.fol`
- `python3 learn.py conjectures/toy_lock_invar11.fol`

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

- `check.py`: determine whether all of the models in a file satisfy all the axioms. Implicitly also checks that the file parses correctly.
- `interpret.py`: performs semantic analysis of the parse result via `interpret()`. Produces `Model`s, `Formula`s and `Signature`s.
- `learn.py`: given a signature and a conjecture, runs `separate()` and generates models until enough positive and negative models exist so that the separator gives a formula equivalent to the conjecture.
- `logic.py`: defines logic objects like `Model`s, `Formula`s and `Signature`s.
- `matrix.py`: generates the matrix of a formula given the satisfying formula and FO-types via `infer_matrix()`.
- `parse.py`: parses a s-expr file into lists of lists and atoms via `parse()`. Performs both lexing and parsing but does not check well-formedness of the resulting parse tree or build logic objects.
- `separate.py`: given a set of postive and negative models, infer a formula which separates them via `separate()`.

## License

This code is copyrighted Stanford University and is not for public distribution.