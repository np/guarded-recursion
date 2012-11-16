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

head : S → ℕ
head s with un F s
... | x , _ = x

tail : S → ▹ S
tail s with un F s
... | _ , xs = ▹Set-rule′ xs

cons : ℕ → ▹ S → S
cons x xs = roll F (x , ▹Set-rule xs)

mapS : (ℕ → ℕ) → S → S
mapS f = fix mp
  where mp : ▹ (S → S) → S → S
        mp self s = cons (f (head s)) (self ⊛ tail s)

mapS2 : (ℕ → ℕ) → S → S
mapS2 f = fix mp
  where
    mp : ▹ (S → S) → S → S
    mp self s = cons (f (head s)) (next (λ s' → cons (f (head s')) (self ⊛ tail s')) ⊛ tail s)

nats : S
nats = fix f
  where f : ▹ S → S
        f self = cons 0 (map▹ (mapS suc) self)

nats2 : S
nats2 = fix f
  where f : ▹ S → S
        f self = cons 0 (map▹ (mapS2 suc) self)


arrow : ▹ ℕ
arrow = map▹ head (tail nats)

browken : ▹ ℕ
browken = map▹ head (tail nats2)
