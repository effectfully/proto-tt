module TT.Typecheck where

open import TT.Core public

infix  4 _⊢_
infixl 8 _⟦_⟧ᵏ
infixl 2 _∋_

mutual
  data _⊢_ {n} (Γ : Con n) : Value n -> Set where
    typeᵗ    : Γ ⊢ typeᵛ
    πᵗ       :  (σₜ : Γ           ⊢ typeᵛ)
             ->       Γ ▻ eval σₜ ⊢ typeᵛ
             ->       Γ           ⊢ typeᵛ
    varᵗ     : ∀ v -> Γ ⊢ lookupᶜ v Γ
    ƛᵗ       : ∀ {σ} {τₖ : Kripke n}
             -> Γ ▻ σ ⊢ instᵏ τₖ
             -> Γ     ⊢ piᵛ σ τₖ
    _·ᵗ_     : ∀ {σ} {τₖ : Kripke n}
             ->       Γ ⊢ piᵛ σ τₖ
             -> (xₜ : Γ ⊢ σ)
             ->       Γ ⊢ τₖ ⟦ xₜ ⟧ᵏ
    qcoerceᵗ : ∀ {σ τ} -> quoteᵛ₀ σ ≡ quoteᵛ₀ τ -> Γ ⊢ σ -> Γ ⊢ τ
    wkᵗ      : ∀ {σ} -> ε ⊢ σ -> Γ ⊢ wk₀ σ

  ⟦_/_⟧ : ∀ {n m σ} {Γ : Con n} -> m ↤ n -> Γ ⊢ σ -> Value m
  ⟦ ρ / typeᵗ        ⟧ = typeᵛ
  ⟦ ρ / πᵗ σ τ       ⟧ = piᵛ ⟦ ρ / σ ⟧ ⟦ ρ / τ ⟧ᵏ
  ⟦ ρ / varᵗ v       ⟧ = lookupᵉ v ρ
  ⟦ ρ / ƛᵗ b         ⟧ = lamᵛ ⟦ ρ / b ⟧ᵏ
  ⟦ ρ / f ·ᵗ x       ⟧ = ⟦ ρ / f ⟧ $ᵛ ⟦ ρ / x ⟧
  ⟦ ρ / qcoerceᵗ q t ⟧ = ⟦ ρ / t ⟧
  ⟦ ρ / wkᵗ t        ⟧ = wk₀ (eval t)

  ⟦_/_⟧ᵏ : ∀ {n m σ τ} {Γ : Con n} -> m ↤ n -> Γ ▻ σ ⊢ τ -> Kripke m
  ⟦ ρ / b ⟧ᵏ ι x = ⟦ renᵉ ι ρ ▷ x / b ⟧

  eval : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Value n
  eval = ⟦ stopᵉ /_⟧

  _⟦_⟧ᵏ : ∀ {n σ} {Γ : Con n} -> Kripke n -> Γ ⊢ σ -> Value n
  k ⟦ x ⟧ᵏ = k [ eval x ]ᵏ

  ⟦_⟧[_] : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Value n -> Value n
  ⟦ b ⟧[ x ] = ⟦ stopᵉ ▷ x / b ⟧

  ⟦_⟧⟦_⟧ : ∀ {n σ τ} {Γ : Con n} -> Γ ▻ σ ⊢ τ -> Γ ⊢ σ -> Value n
  ⟦ b ⟧⟦ x ⟧ = ⟦ b ⟧[ eval x ]

module _ {A} where
  open TermWith A

  erase : ∀ {n σ} {Γ : Con n} -> Γ ⊢ σ -> Term n
  erase  typeᵗ         = type
  erase (πᵗ σ τ)       = π (erase σ) (erase τ)
  erase (varᵗ v)       = var v
  erase (ƛᵗ b)         = ƛ (erase b)
  erase (f ·ᵗ x)       = erase f · erase x
  erase (qcoerceᵗ q t) = erase t
  erase (wkᵗ t)        = wk₀ (erase t)

Typed : Set
Typed = ∃ λ (σ⁺ : Value⁺) -> ∀ {n} {Γ : Con n} -> Γ ⊢ σ⁺

open TermWith Typed public

data NonInferrable : Set where
  ƛₙᵢ : NonInferrable

data TCError : Set where
  mismatch     : ∀ {n} -> Pure n -> Pure n -> Term n -> TCError
  nonInferrable : NonInferrable -> TCError
  nonFunction  : ∀ {n} -> Term n -> TCError

instance
  ⊢Show : ∀ {n σ} {Γ : Con n} -> Show (Γ ⊢ σ)
  ⊢Show = record { show = show ∘ erase {⊥} }

  typedShow : Show Typed
  typedShow = record { show = λ p -> show (proj₂ p {Γ = ε}) }

  nonInferrableShow : Show NonInferrable
  nonInferrableShow = record { show = λ{ ƛₙᵢ -> "ƛ" } }

  tcErrorShow : Show TCError
  tcErrorShow = record
    { show = λ
        { (mismatch σᵢ σₑ t) ->  "the expected type of "
                             s++ showCode t
                             s++ " is "
                             s++ showCode σᵢ
                             s++ " but got "
                             s++ showCode σₑ
        ; (nonInferrable ni) -> "can't infer the type of " s++ show ni
        ; (nonFunction t)    -> showCode t s++ " is not a function"
        }
    }

TCM : Set -> Set
TCM A = TCError ⊎ A

throw : ∀ {A} -> TCError -> TCM A
throw = inj₁

coerceᵗ : ∀ {n σ τ} {Γ : Con n} -> Γ ⊢ σ -> TCM (Γ ⊢ τ)
coerceᵗ {σ = σ} {τ} t =
  maybeToSum (mismatch qσ qτ (erase t)) $ flip qcoerceᵗ t <$> qσ ≟ qτ where
    qσ = quoteᵛ₀ σ
    qτ = quoteᵛ₀ τ

mutual
  infer : ∀ {n} {Γ : Con n} -> Term n -> TCM (∃ (Γ ⊢_))
  infer (pure (, tₜ⁺)) = return (, tₜ⁺)
  infer  type          = return (, typeᵗ)
  infer (π σ τ)        = check σ typeᵛ >>= λ σₜ -> (λ τₜ -> , πᵗ σₜ τₜ) <$> check τ typeᵛ
  infer (var v)        = return (, varᵗ v)
  infer (ƛ b)          = throw $ nonInferrable ƛₙᵢ
  infer (f · x)        = infer f >>= λ
    { (piᵛ σ τₖ , fₜ) -> (λ xₜ -> , fₜ ·ᵗ xₜ) <$> check x σ
    ;  _              -> throw $ nonFunction f
    }

  check : ∀ {n} {Γ : Con n} -> Term n -> (σ : Value n) -> TCM (Γ ⊢ σ)
  check (ƛ b) (piᵛ σ τₖ) = ƛᵗ <$> check b (instᵏ τₖ)
  check  t     σ         = infer t >>= coerceᵗ ∘ proj₂

typecheck : Term⁽⁾ -> Value⁽⁾ -> TCM Term⁺
typecheck t σ = (λ tₜ {_} -> pure $ wk₀ σ , wkᵗ tₜ) <$> check t σ

_∋_ : ∀ σ t -> _
σ ∋ t = left show (check {Γ = ε} σ typeᵛ) >>=ᵗ λ σₜ -> left show (typecheck t (eval σₜ)) >>=ᵗ id
