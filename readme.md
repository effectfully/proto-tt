# proto-tt

It's a type checker for a simple dependently typed language. The type checking procedure is very similar to that of [1]: it's bidirectional and NbE-based, so we have raw terms and values, but since we're in a dependently typed setting, there are also typed terms indexed by values that represent types. E.g. typed Π-types are

```
data _⊢_ {n} (Γ : Con n) : Value n -> Set where
  πᵗ : (σₜ : Γ ⊢ typeᵛ) -> Γ ▻ eval σₜ ⊢ typeᵛ -> Γ ⊢ typeᵛ
  ...
```

That example demonstrates that evaluation is defined on typed terms, which is a great source of confidence that type checking terminates, because there is no evaluation defined on raw terms.

Type checking returns either a (rudimentary) error or a typed term, hence the type system is Church-like and all typing rules are just constructors of `_⊢_`. Unlike in [1] binders in `Value` have Kripke semantics, e.g.

```
data Value n where
  piᵛ  : Value  n -> Kripke n -> Value n
  lamᵛ : Kripke n -> Value  n
  ...
```

where `Kripke n = ∀ {m} -> n ⊑ m -> Value m -> Value m`.

There is one another constructor of `Term`: `pure`. It's used to store typed terms in raw terms to prevent retypechecking.

The [`Cubes`](https://github.com/effectfully/cubes) repo is directly based upon this one.

## References

[1] ["Simply Easy! An Implementation of a Dependently Typed Lambda Calculus"](http://strictlypositive.org/Easy.pdf), Andres Löh, Conor McBride, Wouter Swierstra.
