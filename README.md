# Equational Proof Checker
## Requirements

`Haskell` + `stack`

## Installation

Clone this repo and then run the following command inside it:
```
stack install
```
## Running
```
EquationalProofChecker-exe filename [options]
```

#### Options:
- -debug - Run selected proof step-by-step
- -help - Print short manual

## Supported tactics

- `reflexivity`.
- `symmetry`.
- `transitivity t`.
- `congruence`.
- `rewrite [left | right] eq [with x := t, ...]`.
- `apply eq`.

## Example
See `examples` directory for more examples.
```
Theory Combinators (S/0, K/0, ap/2)
{
  K : ap(ap(K, x), y) = x,
  S : ap(ap(ap(S, x), y), z) = ap(ap(x, z), ap(y, z))
}

Theorem I : ap(ap(ap(S,K), K), x) = x
Proof {
  rewrite -> S.
  apply K.
}
```