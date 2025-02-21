# superfluid

A functional language with dependent types and customisable type representations

# Installing

Requirements: `stack`.

```
git clone https://github.com/superfluid-lang/superfluid.git
stack build
```

Then run `stack run -- -h` to see the available options.

# A tour of Superfluid

Superfluid is a dependently typed language, similar to Idris, Agda, Coq and Lean.
It is meant as a tool for experimenting with efficient compilation of dependent types.

A brief overview of its features:

- Dependent function types `(a : A) -> B`.
- Implicit function types `[a : A] -> B`.
- Instance function types, which are automatically resolved `[[Monad M]] -> A -> M A`.
- Access to the universe `Type`, with `Type : Type` (no universe levels).
- Quantitative type theory with 1, 0, \omega.
- Whitespace, insensitive; grouping is done with braces `{}`.
- Typed holes with `?foo`.

## Basic syntax

Each file consists of a series of definitions.

Each definition is either:

- a function definition

    ```
    def or : Bool -> Bool -> Bool {
      \a b => case a {
        true => true,
        false => b,
      }
    }
    ```

    Function definitions support general recursion.

- a data definition

    ```
    data Bool : Type {
      true : Bool,
      false : Bool
    }
    ```

- or a primitive (postulate)

    ```
    prim conjure : (0 A : Type) -> A
    ```

  Primitives need to have definitions accessible with the same name (but camel
  case) in the output JavaScript file.

Every file has access to the contents of `bootstrap/prelude.sf`.

Functions (anonymous lambdas) are written as
```
\x f => f x
```
This would be of type `A -> (A -> B) -> B`.

Both function arguments and function type arguments can be stacked like:

```
def id : (A : Type) (a : A) -> A {
  \A a => a
}
```

Superfluid supports Rust-style let blocks using braces:
```
{
  let x = 1;
  let y = add x 1;
  let z = mul x y;
  (z, y)
}
```

This would be of type `(Nat, Nat)`.

Pattern matching can be done using the `case` keyword:
```
case x {
  true => true,
  false => false,
}
```

Nested and dependent pattern matching is not supported yet, but can be emulated
using explicit motives and equality transports.

An explicit motive can be provided using `to`:

```
def snd : [A : Type, B : A -> Type] -> (p : Sigma A B) -> B (fst p) {
  \[_] [B] p => case p to (\p => B (fst p)) {
    (a, b) => b
  }
}
```

## Inductive families

Superfluid supports inductive families, such as

```
data Bool : Type {
  true : Bool,
  false : Bool
}

data Sigma (A : Type, B : A -> Type) : Type {
  pair : (a : A) -> B a -> Sigma A B
}

data Equal [A : Type] : A -> A -> Type {
  refl : [x : A] -> Equal x x
}
```

Equality is not special; it is just an inductive family.

## Quantities

Superfluid supports quantities (`0`, `1`, `*` for omega), such as

```
data Subset (A : Type) (B : A -> Type) : Type {
  element : (a : A) -> (0 _ : B a) -> Subset A B
}
```

Quantities can be added in all binders, including lets:

```
(0 a : A) -> B
let 1 a = b
[* a : A] -> B
[[0 _ : Monad M]] -> Q
```

A usage check is run after typechecking to ensure that variables with quantity
`0` are not used in a runtime context, and with `1` are not used more than once
(technically the `1` quantity is affine, not linear).

All binders with quantity `0` are erased before codegen.

## Custom representations

Each module item (other than primitives) can be given a custom representation.

- For function definitions, we merely need to provide a function of the same
type (though technically we should also verify that the representation is
functionally equivalent to the original).
- For data definitions, we need to "implement" the constructors and induction of
the original data type.

For example, this is how the prelude represents natural numbers as JavaScript numbers:

```
repr data Nat as JsUint {
  z as js-uint-zero,
  s n as js-uint-plus js-uint-one (repr n),
  case n to E {
    z => b,
    s => r,
  } as {
    js-zero-or-pos [\x => E (unrepr x)] (\_ => b) (\x => r (unrepr x)) (repr n)
  }
}

repr def add as \a b => unrepr (js-uint-plus (repr a) (repr b))
repr def sub as \a b => unrepr (js-uint-minus (repr a) (repr b))
repr def mul as \a b => unrepr (js-uint-times (repr a) (repr b))
```

We also have some operators to reason about representations:

- if `x : A`, then `repr x : Repr A`
- if `x : Repr B`, then `unrepr x : B`

These reduce definitionally to the item's defined representation.

In the prelude, all list-like things with irrelevant indices are represented as
JavaScript arrays. See `examples/paper/refinement.sf` for an example of zero-cost
conversion between lists and vectors.

The system of custom representations is explored further in the paper:
<https://trendsfp.github.io/abstracts/paper-019.pdf>

## Code generation

Superfluid generates code for Node.js. Upon compilation of a file with the `-g` flag (generate code),
the generated code is written to a file with the same name as the input file, but with a `.js` extension.

This can then be run with Node.js. Often you might need a larger stack size.
For example, `node --stack-size=200000 examples/paper/fizzbuzz.sf.js`.

## Examples

The `bootstrap/prelude` already contains quite a few examples of custom representations, including:

- `Fin` and `Nat` as JS numbers, with representations for common numeric operations.
- `List` as JS arrays
- `ByteList` and `ByteVec` as JS buffers
- `String` as JS strings
- `Bool` as JS booleans

Also see the `examples/` directory for:

- `paper/refinement.sf`: Zero-cost conversion between lists and vectors (the coherence rules are missing).
- `paper/fizzbuzz.sf`: Just a plain fizzbuzz implementation, but actually runs fast due to `Nat` representation.
- `paper/amicable.sf`: Finding amicable numbers. Again, runs fast due to `Nat` representation.
  However we can run the function at compile-time too, which doesn't have access
  to the fast `Nat` representation, and thus is really slow (but can do symbolic
  theorem proving!).
- `paper/binary.sf`: Storing player and inventory data structures as a
   contiguous byte buffer using representations (WIP).
- `paper/network.sf`: UDP buffers with zero-copy serialization and
   deserialization into records (WIP).

I have also written day 1 of Advent of Code 2024 Superfluid: <https://github.com/kontheocharis/advent-of-code-2024>.

More examples coming very soon.

# Acknowledgments

- A lot of the work on Superfluid started by mirroring the code in Andras
  Kovacs' [elaboration zoo](https://github.com/AndrasKovacs/elaboration-zoo).
- Thank you to Edwin Brady for the detailed discussions about: unification
  with postponing, quantitative type theory, instance resolution, and dependent
  pattern matching.

# Wishlist/missing features

- Induction-induction and induction-recursion for data types.
- Forward declarations.
- Positivity and termination checking.
- Mutual recursion for functions.
- Dependent pattern matching (coming soon).
- Coherence checking for representations.
- A well-scoped version of this compiler that is cleaner and less hacky. Work
  has begun: <https://github.com/kontheocharis/superfluid-idr>.
- Coinductive data types.
- A better compilation target: C/Rust/LLVM.
- More *internal* control over compilation: custom function/closure compilation,
  flat dependent pair types (as a library).
