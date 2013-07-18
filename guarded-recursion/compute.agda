-- Be afraid… Type as type Type
{-# OPTIONS --type-in-type #-}

{-
Be really afraid: this module is a hack to give definitional equalities
to ▹. This is done by introducing an 'evil' function called 'run' that
should not appear in user code. Is this safe to do? This remains to be
explored.

By the same token we give a definitional equalities to fix as well.
Beware of non-termination!
-}

open import guarded-recursion.prelude
  renaming (O to zero; S to suc)

module guarded-recursion.compute where

-- Same as in prelude but type-in-type
module Coe₀ where
    coe : {A B : ★} → A ≡ B → A → B
    coe = transport id

    coe! : {A B : ★} → A ≡ B → B → A
    coe! = transport id ∘ !

    module _ {A : ★} {P Q : A → ★} (p : P ≡ Q) {x} where
        coe₁ : P x → Q x
        coe₁ = transport (λ P → P x) p

        coe₁! : Q x → P x
        coe₁! = transport (λ P → P x) (! p)

    module _ {A : ★} {B : ★} {R S : A → B → ★} (p : R ≡ S) {x y} where
        coe₂ : R x y → S x y
        coe₂ = transport (λ R → R x y) p

        coe₂! : S x y → R x y
        coe₂! = transport (λ R → R x y) (! p)
open Coe₀

infixl 6 _⊛_

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

▸ : ▹ ★ → ★
▸ x = ▹ (run x)

▸F : ∀ {A} → (A → ★) → ▹ A → ★
▸F F x = ▸ (next F ⊛ x)

map▹ : ∀ {A} {B : A → ★} → ((x : A) → B x) → (x : ▹ A) → ▸F B x
map▹ f x = next f ⊛ x

private
  module Unused where
    by-computation : ∀ {A} {B : A → ★} {x} → ▸ (next B ⊛ x) ≡ ▹ (B (run x))
    by-computation = idp

    const⊛ : ∀ {A} {X : ★} {x : ▹ X} → ▸ (next (λ _ → A) ⊛ x) ≡ ▹ A
    const⊛ = idp

    -- useless: the dependent version is just as fine
    _⊛′_ : ∀ {A B} → ▹ (A → B) → ▹ A → ▹ B
    _⊛′_ = _⊛_

    -- useless: the dependent version is just as fine
    map▹′ : ∀ {A B} → (A → B) → ▹ A → ▹ B
    map▹′ = map▹

zip : ∀ {A} {B : A → ★} → Σ (▹ A) (▸F B) → ▹ Σ A B
zip (x , y) = map▹ _,_ x ⊛ y

unzip : ∀ {A} {B : A → ★} → ▹ Σ A B → Σ (▹ A) (▸F B)
unzip p = map▹ fst p , map▹ snd p

module M
   (fix      : ∀ {A} → (▹ A → A) → A)
   (fix-rule : ∀ {A} (f : ▹ A → A) → fix f ≡ f (next (fix f))) where

  -- Streams of 'A's
  S : ★ → ★
  S A = fix (λ X → A × ▸ X)

  rollS : ∀ {A} → A × ▹ (S A) → S A
  rollS = coe! (fix-rule _)

  unS : ∀ {A} → S A → A × ▹ (S A)
  unS = coe (fix-rule _)

  hd : ∀ {A} → S A → A
  hd = fst ∘ unS

  tl : ∀ {A} → S A → ▹ S A
  tl = snd ∘ unS

  infixl 4 _∷_
  _∷_ : ∀ {A} → A → ▹ S A → S A
  x ∷ xs = rollS (x , xs)

  BF : ∀ {A} → ▹ (S A → S A → ★) → S A → S A → ★
  BF ▹B xs ys = (hd xs ≡ hd ys) × ▸ (▹B ⊛ tl xs ⊛ tl ys)

  B : ∀ {A} → S A → S A → ★
  B = fix BF

  rollB : ∀ {A} {xs ys : S A} → BF (next B) xs ys → B xs ys
  rollB = coe₂! (fix-rule BF)

  B-reflF : ∀ {A} → ▹((xs : S A) → B xs xs) → (xs : S A) → B xs xs
  B-reflF ▹BR xs = rollB (idp , ▹BR ⊛ tl xs)

  -- Reflexivity of the Bisimilarity relation
  -- Thanks to computation at the level of types this definition nicely
  -- goes through.
  B-refl : ∀ {A} (xs : S A) → B xs xs
  B-refl = fix B-reflF

  repeatS : ∀ {A} → A → S A
  repeatS x = fix (_∷_ x)

  zapSf : ∀ {A B} → ▹ (S (A → B) → S A → S B)
                  →    S (A → B) → S A → S B
  zapSf zapS fs xs = hd fs (hd xs) ∷ zapS ⊛ tl fs ⊛ tl xs

  zapS : ∀ {A B} → S (A → B) → S A → S B
  zapS = fix zapSf

  -- repeatS and zapS form an applicative functor

  iterateS : ∀ {A} → (A → A) → A → S A
  iterateS f = fix λ iterateS x → x ∷ iterateS ⊛ next (f x)

  mapSf : ∀ {A B} → (A → B) → ▹(S A → S B) → S A → S B
  mapSf f mapS xs = f (hd xs) ∷ mapS ⊛ tl xs

  mapS : ∀ {A B} → (A → B) → S A → S B
  mapS f = fix (mapSf f)

  nats : S ℕ
  nats = fix (λ nats → 0 ∷ map▹ (mapS suc) nats)

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

module HiddenFix {A} (f : ▹ A → A) where
    -- This definition is not intended to termination-check.
    -- Use with care it's really easy to make the type-checker loop.
    {-# NO_TERMINATION_CHECK #-}
    fix : Hidden A
    fix = hide f (next (reveal fix))

    fix-rule : reveal fix ≡ f (next (reveal fix))
    fix-rule = idp {_} {A} {reveal fix}

open HiddenFix
open M (reveal ∘ fix) fix-rule

  -- -}
  -- -}
  -- -}
  -- -}
  -- -}
