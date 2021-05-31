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

## Example

```
Theory Monoid (op/2, 1/0)
{
  NeutralRight : op(n, 1) = n,
  NeutralLeft : op(1, n) = n,
  Assoc : op(n, op(m, k)) = op(op(n, m), k)
}

Theorem OneInTheMiddle : op(x, op(1, y)) = op(x, y)
Proof {
  rewrite -> NeutralLeft.
  reflexivity.
}
```