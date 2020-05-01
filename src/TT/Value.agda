{-# OPTIONS --no-positivity-check #-}

module TT.Value where

open import TT.Prelude
open import TT.Structures
open import TT.Term

infixl 6 _·ᵛ_ _$ᵛ_
infixr 5 _⇒ᵛ_

data Value n : Set
open Kripke Value public
data Value n where
  typeᵛ : Value  n
  piᵛ   : Value  n -> Kripke n -> Value n
  varᵛ  : Fin    n -> Value  n
  lamᵛ  : Kripke n -> Value  n
  _·ᵛ_  : Value  n -> Value  n -> Value n

Value⁽⁾ : Set
Value⁽⁾ = Value 0

Value⁺ : Set
Value⁺ = ∀ {n} -> Value n

instance
  valueContext : Context Value
  valueContext = record { ren = go } where
    go : Renames Value
    go ι  typeᵛ     = typeᵛ
    go ι (piᵛ σ τₖ) = piᵛ (go ι σ) (renᵏ ι τₖ)
    go ι (varᵛ v)   = varᵛ (ren ι v)
    go ι (lamᵛ bₖ)  = lamᵛ (renᵏ ι bₖ)
    go ι (f ·ᵛ x)   = go ι f ·ᵛ go ι x

  valueAppend : Append Value
  valueAppend = record { wk = go } where
    go : Weakens Value
    go  typeᵛ     = typeᵛ
    go (piᵛ σ τₖ) = piᵛ (go σ) (wkᵏ τₖ)
    go (varᵛ v)   = varᵛ (inject+ _ v)
    go (lamᵛ bₖ)  = lamᵛ (wkᵏ bₖ)
    go (f ·ᵛ x)   = go f ·ᵛ go x

  valueEnvironment : Environment Value
  valueEnvironment = record { fresh = varᵛ fzero }

_⇒ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
σ ⇒ᵛ τ = piᵛ σ (λ ι _ -> ren ι τ)

_$ᵛ_ : ∀ {n} -> Value n -> Value n -> Value n
lamᵛ k $ᵛ x = k [ x ]ᵏ
f      $ᵛ x = f ·ᵛ x

module _ {A} where
  open TermWith A

  mutual
    quoteᵛ : Value ∸> Term
    quoteᵛ  typeᵛ     = type
    quoteᵛ (piᵛ σ τₖ) = π (quoteᵛ σ) (quoteᵏ τₖ)
    quoteᵛ (varᵛ v)   = var v
    quoteᵛ (lamᵛ bₖ)  = ηƛ (quoteᵏ bₖ)
    quoteᵛ (f ·ᵛ x)   = quoteᵛ f · quoteᵛ x

    quoteᵏ : ∀ {n} -> Kripke n -> Term (suc n)
    quoteᵏ k = quoteᵛ (instᵏ k)

quoteᵛ₀ : Value ∸> Pure
quoteᵛ₀ = quoteᵛ

isUnshiftableᵛ : ∀ {n} -> Value (suc n) -> Bool
isUnshiftableᵛ = isUnshiftable ∘ quoteᵛ₀

isConstᵛ : ∀ {n} -> Value n -> Bool
isConstᵛ (lamᵛ b) = isUnshiftableᵛ (instᵏ b)
isConstᵛ  _       = false
