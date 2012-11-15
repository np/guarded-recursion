module guarded-rec where

open import Function
open import Type
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

postulate
  ▹_ : ∀ {a} → Set a → Set a

  ▹Set : ∀ {a} → ▹ (Set a) → Set a
--▹Set A = ▹ A

  next : ∀ {a} {A : Set a} → A → ▹ A

  ▹Set-rule : ∀ {a} {A : Set a} → ▹ A → ▹Set (next A)
  ▹Set-rule′ : ∀ {a} {A : Set a} → ▹Set (next A) → ▹ A

  fix  : ∀ {a} {A : Set a} → (▹ A → A) → A
  rule : ∀ {a} {A : Set a} → (f : ▹ A → A) → fix f ≡ f (next (fix f))

  _⊛_  : ∀ {a b} {A : Set a} {B : Set b} → ▹ (A → B) → ▹ A → ▹ B

F : ▹ ★ → ★
F X = ℕ × ▹Set X

un : (f : ▹ Set → Set) → fix f → f (next (fix f))
un = subst id ∘ rule

roll : (f : ▹ Set → Set) → f (next (fix f)) → fix f
roll = subst id ∘ sym ∘ rule

map▹ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ▹ A → ▹ B
map▹ f ▹x = next f ⊛ ▹x

S : ★
S = fix F

mapS : (ℕ → ℕ) → S → S
mapS f = fix mp
  where mp : ▹ (S → S) → S → S
        mp self s with un F s
        ... | x , xs = roll F (f x , (▹Set-rule (self ⊛ ▹Set-rule′ xs)))

nats : S
nats = fix f
  where f : ▹ S → S
        f self = roll F (zero , ▹Set-rule (map▹ (mapS suc) self))
