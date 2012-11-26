{-# OPTIONS --type-in-type #-}
open import Relation.Binary.PropositionalEquality
open import Function
open import Data.Nat
open import Data.Unit
open import Data.Product using (_×_; Σ; _,_; proj₁; proj₂)
module guarded-rec-data where
infixl 6 _⊛_

★ = Set

data ▹_ : ★ → ★

private
  -- 'run' should not appear in user code
  run : ∀ {A} → ▹ A → A

-- User code should not pattern-match on ▹_...
data ▹_ where
  next : ∀ {A} → A → ▹ A
  _⊛_  : ∀ {A} {B : A → ★} → ▹ ((x : A) → B x) → (x : ▹ A) → ▹ (B (run x))

run (next x) = x
run (f  ⊛ x) = run f (run x)

▹′ : ▹ ★ → ★
▹′ x = ▹ (run x)

foo : ∀ {A} {B : A → ★} {x} → ▹′ (next B ⊛ x) ≡ ▹ (B (run x))
foo = refl

const⊛ : ∀ {A} {X : ★} {x : ▹ X} → ▹′ (next (λ _ → A) ⊛ x) ≡ ▹ A
const⊛ = refl

-- useless
-- _⊛′_ : ∀ {A B} → ▹ (A → B) → ▹ A → ▹ B
-- _⊛′_ = _⊛_

-- useless
-- map▹′ : ∀ {A B} → (A → B) → ▹ A → ▹ B
-- map▹′ = map▹

map▹  : ∀ {A} {B : A → ★} → ((x : A) → B x) → (x : ▹ A) → ▹ (B (run x)) -- ▹′ (next B ⊛′ x)
map▹  f x = next f ⊛ x

▹′F : ∀ {A} → (A → ★) → ▹ A → ★
▹′F F = ▹′ ∘ map▹ F

zip : ∀ {A} {B : A → ★} → Σ (▹ A) (▹′F B) → ▹ Σ A B
zip (x , y) = map▹ _,_ x ⊛ y

unzip : ∀ {A} {B : A → ★} → ▹ Σ A B → Σ (▹ A) (▹′F B)
unzip p = map▹ proj₁ p , map▹ proj₂ p

module M
   (fix : ∀ {A} → (▹ A → A) → A)
   (fix-rule : ∀ {A} (f : ▹ A → A) → fix f ≡ f (next (fix f))) where

  S : ★ → ★
  S A = fix (λ X → A × ▹′ X)

  rollS : ∀ {A} → A × ▹ (S A) → S A
  rollS = subst id (sym (fix-rule _))

  unS : ∀ {A} → S A → A × ▹ (S A)
  unS = subst id (fix-rule _)

  hd : ∀ {A} → S A → A
  hd = proj₁ ∘ unS

  tl : ∀ {A} → S A → ▹ S A
  tl = proj₂ ∘ unS

  infixl 4 _∷_
  _∷_ : ∀ {A} → A → ▹ S A → S A
  x ∷ xs = rollS (x , xs)

  BF : ∀ {A} → ▹ (S A → S A → ★) → S A → S A → ★
  BF ▹B xs ys = (hd xs ≡ hd ys) × ▹′ (▹B ⊛ tl xs ⊛ tl ys)
  -- BF ▹B xs ys = (hd xs ≡ hd ys) × ▹ (run ▹B (run (tl xs)) (run (tl ys)))

  B : ∀ {A} → S A → S A → ★
  B = fix BF

  rollB : ∀ {A} {xs ys : S A} → BF (next B) xs ys → B xs ys
  rollB {xs = xs} {ys} = subst (λ B → B xs ys) (sym (fix-rule BF))

  B-reflF : ∀ {A} → ▹((xs : S A) → B xs xs) → (xs : S A) → B xs xs
  B-reflF ▹BR xs = rollB (refl , ▹BR ⊛ tl xs)

  B-refl : ∀ {A} (xs : S A) → B xs xs
  B-refl = fix B-reflF

  repeatS : ∀ {A} → A → S A
  repeatS x = fix (_∷_ x)

  mapSf : ∀ {A B} → (A → B) → ▹(S A → S B) → S A → S B
  mapSf f self xs = f (hd xs) ∷ self ⊛ tl xs

  mapS : ∀ {A B} → (A → B) → S A → S B
  mapS f = fix (mapSf f)

  nats : S ℕ
  nats = fix (λ self → 0 ∷ map▹ (mapS suc) self)

  ▹^ : ∀ ℕ → ★ → ★
  ▹^ zero    A = A
  ▹^ (suc n) A = ▹ ▹^ n A

  next^ : ∀ {A} n → A → ▹^ n A
  next^ zero    x = x
  next^ (suc n) x = next (next^ n x)

  map▹^ : ∀ {A B} n → (A → B) → ▹^ n A → ▹^ n B
  map▹^ zero    f = f
  map▹^ (suc n) f = map▹ (map▹^ n f)

  run^ : ∀ {A} n → ▹^ n A → A
  run^ zero = id
  run^ (suc n) = run^ n ∘ run

  ‼ : ∀ {A} → (n : ℕ) → S A → ▹^ n A
  ‼ zero    = hd
  ‼ (suc n) = map▹ (‼ n) ∘ tl

  run‼ : ∀ {A} → ℕ → S A → A
  run‼ n = run^ n ∘ ‼ n

module Foo where
  module F {A} (f : ▹ A → A) where
    fix : Hidden A
    fix = hide f (next (reveal fix))

    fix-rule : reveal fix ≡ f (next (reveal fix))
    fix-rule = refl {_} {A} {reveal fix}
  open F

  open M (λ f → reveal (fix f)) fix-rule public
open Foo

  -- -}
  -- -}
  -- -}
  -- -}
  -- -}
