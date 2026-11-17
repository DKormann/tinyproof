# Tinyproof

A small, inspectable dependent-type and proof checker in TypeScript, inspired by Bend/BendTT. The goal is to keep the implementation tiny enough to audit yourself.

## Usage

Install [Bun](https://bun.sh), then check a proof file:

```sh
./tinycheck example.proof
```

The checker loads the definitions in `base.ts` before checking your file. It prints checked definitions and exits with a nonzero status on failure.

For example, a `.proof` file can contain:

```text
identity = ( (x: Nat) : Nat => x )
zero : Nat = ( identity(Zero) )
```

Run the acceptance and rejection tests with:

```sh
bun test.ts
```

## Repository

- `compiler.ts` — core terms, reduction, equality, checking, and the surface-language compiler.
- `base.ts` — shared definitions and proofs, including naturals and equality.
- `tinycheck` — executable command-line checker.
- `test.ts` — examples that must compile or be rejected.
- `example.proof` — a minimal input file.
- `docs/history.md` — history of the implementation experiments.

## Features

- Higher-order abstract syntax (HOAS) for binders.
- Dependent functions and algebraic data types.
- Dependent pattern matching.
- `Type` and `Data` universes, with erased arguments marked `-`.
- Affinity checks for live, non-`Data` values.
- Structural recursion checking.
- Equality and reflexivity expressed in the surface language rather than special AST nodes.

Not supported yet: compile-time arguments, mutual recursion, and macros.
