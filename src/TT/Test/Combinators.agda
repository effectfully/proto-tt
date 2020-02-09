module TT.Test.Combinators where

open import TT.Typecheck

I : Type⁽⁾
I = pi type λ A → A ⇒ A

i : Term⁺
i = I
  ∋ lam 2 λ A x → x

A : Type⁽⁾
A = pi type λ A → pi (A ⇒ type) λ B → (pi A λ x → B · x) ⇒ pi A λ x → B · x

a : Term⁺
a = A
  ∋ lam 4 λ A B f x → f · x

ii : Term⁺
ii = I
   ∋ lam 1 λ A → i · (A ⇒ A) · (i · A)

ai : Term⁺
ai = I
   ∋ lam 1 λ A → a · A · (ƛ A) · (i · A)
