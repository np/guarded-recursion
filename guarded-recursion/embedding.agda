-- Axiomatic embedding of guarded recursion in Agda
module guarded-recursion.embedding where

open import Level using () renaming (zero to ₀; suc to ↑)
open import Function using (id; _∘_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; if_then_else_)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Unit using (⊤; Hidden; Unit; hide; reveal)
open import Data.Product using (_×_; _,_; proj₁; proj₂; curry)
open import Relation.Binary using (Reflexive)
open import Relation.Binary.PropositionalEquality
              using (_≡_; subst; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality.TrustMe as UnsafeButPlease

ℕ² = ℕ × ℕ

-- Let's rename "Set₀" as "★" to avoid confusion with set-theory
★ = Set

-- Let's rename "Set ℓ" as "★_ ℓ" to avoid confusion with set-theory
★_ : ∀ ℓ → Set (↑ ℓ)
★_ ℓ = Set ℓ

Endo : ∀ {a} → ★_ a → ★_ a
Endo A = A → A

Fix : ∀ {a} → ★_ a → ★_ a
Fix X = (X → X) → X

coe : ∀ {ℓ} {A B : ★_ ℓ} → A ≡ B → A → B
coe = subst id

coe₁ : ∀ {a ℓ} {A : ★_ a} {P Q : A → ★_ ℓ} → P ≡ Q → ∀ {x} → P x → Q x
coe₁ pf {x} = subst (λ P → P x) pf

coe₂ : ∀ {a b ℓ} {A : ★_ a} {B : ★_ b} {R S : A → B → ★_ ℓ} → R ≡ S → ∀ {x y} → R x y → S x y
coe₂ pf {x} {y} = subst (λ R → R x y) pf

module M
    (▹_ : ∀ {a} → ★_ a → ★_ a)

    (▸ : ∀ {a} → ▹ (★_ a) → ★_ a)

    (next : ∀ {a} {A : ★_ a} → A → ▹ A)

    (▸-rule : ∀ {a} {A : ★_ a} → ▸ (next A) ≡ ▹ A)

    (fix      : ∀ {a} {A : ★_ a} → (▹ A → A) → A)
    (fix-rule : ∀ {a} {A : ★_ a} {f : ▹ A → A} → fix f ≡ f (next (fix f)))

    (_⊛′_ : ∀ {a b} {A : ★_ a} {B : ★_ b} → ▹ (A → B) → ▹ A → ▹ B)
    (_⊛_ : ∀ {a b} {A : ★_ a} {B : A → ★_ b}
           → ▹ ((x : A) → B x) → (x : ▹ A) → ▸ (next B ⊛′ x))

    (fix-uniq : ∀ {a} {A : ★_ a} (u : A) f → u ≡ f (next u) → u ≡ fix f)

    (next⊛next : ∀ {a b} {A : ★_ a} {B : ★_ b} (f : A → B) (x : A)
                 → next f ⊛′ next x ≡ next (f x))

    where

    roll▸ : ∀ {a} {A : ★_ a} → ▹ A → ▸ (next A)
    roll▸ = coe (sym ▸-rule)

    un▸ : ∀ {a} {A : ★_ a} → ▸ (next A) → ▹ A
    un▸ = coe ▸-rule

    ▹Fix : ∀ {a} → ★_ a → ★_ a
    ▹Fix X = (▹ X → X) → X

    ▹Endo : ∀ {a} → ★_ a → ★_ a
    ▹Endo X = ▹ X → X

    μ : ∀ {a} → Fix (★_ a)
    μ F = fix (F ∘ ▸)

    un : ∀ {a f} → fix {A = ★_ a} f → f (next (fix f))
    un = coe fix-rule

    unμ : ∀ {a} f → μ {a} f → f (▹ μ f)
    unμ {a} f x rewrite sym (▸-rule {A = μ f}) = un x

    roll : ∀ {a f} → f (next (fix f)) → fix {A = ★_ a} f
    roll = coe (sym fix-rule)

    μ-rule : ∀ {a} f → μ {a} f ≡ f (▹ μ f)
    μ-rule f = trans fix-rule (cong f (▸-rule {A = μ f}))

    rollμ : ∀ {a} f → f (▹ μ f) → μ {a} f
    rollμ f = subst id (sym (μ-rule f))

    un₁ : ∀ {a b} {A : ★_ a} {f x} → fix {A = A → ★_ b} f x → f (next (fix f)) x
    un₁ = coe₁ fix-rule

    roll₁ : ∀ {a b} {A : ★_ a} {f x} → f (next (fix f)) x → fix {A = A → ★_ b} f x
    roll₁ = coe₁ (sym fix-rule)

    un₂ : ∀ {a b} {A : ★_ a} {B : ★_ b} {c f x y} → fix {A = A → B → ★_ c} f x y → f (next (fix f)) x y
    un₂ = coe₂ fix-rule

    roll₂ : ∀ {a b} {A : ★_ a} {B : ★_ b} {c f x y} → f (next (fix f)) x y → fix {A = A → B → ★_ c} f x y
    roll₂ = coe₂ (sym fix-rule)

    map▹ : ∀ {a b} {A : ★_ a} {B : ★_ b} → (A → B) → ▹ A → ▹ B
    map▹ f ▹x = next f ⊛′ ▹x

    {-
    alternatively
    _⊛′′_ : ∀ {a b} {A : ★_ a} {B : A → ★_ b} → ▹ ((x : A) → B x) → (x : A) → ▹ (B x)
    ▹f ⊛′′ x = map▹ (λ f → f x) ▹f
    -}

    {-
    alternatively
    _$_ : ∀ {a b} {A : ★_ a} (B : A → ★_ b) → ▹ A → ▹ (★_ b)
    f $ ▹x = map▹ f ▹x
    -}

    ▹^ : ∀ {a} → ℕ → ★_ a → ★_ a
    ▹^ zero    A = A
    ▹^ (suc n) A = ▹ ▹^ n A

    next^ : ∀ {a} {A : ★_ a} n → A → ▹^ n A
    next^ zero    x = x
    next^ (suc n) x = next (next^ n x)

    map▹^ : ∀ {a b} {A : ★_ a} {B : ★_ b} n → (A → B) → ▹^ n A → ▹^ n B
    map▹^ zero    f = f
    map▹^ (suc n) f = map▹ (map▹^ n f)


    module SimpleStream where
      F : ★ → ★ → ★
      F A X = A × X

      S : ★ → ★
      S A = μ (F A)

    μ₁F' : ∀ {a} {A : ★_ a} → ((A → ▹ ★) → A → ★) → (▹(A → ★) → A → ★)
    μ₁F' F self = F (λ x → (self ⊛′ next x))

    μ₁F : ∀ {a} {A : ★_ a} → ((A → ★) → A → ★) → (▹(A → ★) → A → ★)
    μ₁F F self = F (λ x → ▸ (self ⊛′ next x))

    μ₁ : ∀ {a} {A : ★_ a} → ((A → ★) → A → ★) → A → ★
    μ₁ F = fix (μ₁F F)

    module μId where
        μid : ★
        μid = μ id

        μid-rule : μid ≡ ▹ μid
        μid-rule = trans fix-rule (▸-rule {A = μ id})

        ω : μid
        ω = fix (rollμ id)

    module CoNat where
        Coℕ : ★
        Coℕ = μ Maybe

        rollNat : Maybe (▹ Coℕ) → Coℕ
        rollNat = rollμ Maybe

        ze : Coℕ
        ze = rollNat nothing

        su : ▹ Coℕ → Coℕ
        su x = rollNat (just x)

        su′ : Coℕ → Coℕ
        su′ = su ∘ next

        ω : Coℕ
        ω = fix su

    module Neg where
        {- data X : ★ where
             rollX : Fix X
                   : (X → X) → X
           -}
        X : ★
        X = μ Endo

        rollX : Endo (▹ X) → X
           -- : (▹ X → ▹ X) → X
        rollX = rollμ Endo

        rollX′ : ▹(Endo X) → X
            -- : ▹(X → X) → X
        rollX′ = rollX ∘ _⊛′_

        unX : X → Endo (▹ X)
        unX = unμ Endo

        -- δ = λ x → x x
        δ : X → ▹ X
        δ = λ x → (unX x) (next x)

    module Neg' where
        {- data X : ★ where
             c : Fix X
               : ((X → X) → X) → X
           -}
        X : ★
        X = μ Fix

        rollX : Fix (▹ X) → X
        rollX = rollμ Fix

        unX : X → Fix (▹ X)
        unX = unμ Fix

    module μ₁Id where
        -- μ₁id = ▹∘▹∘…∘▹
        -- μ₁id A = ▹ (▹ … (▹ A))
        μ₁id : ★ → ★
        μ₁id = μ₁ id

        betterfix₁ : ∀ {a} {A : ★_ a} {x : A} (F : Endo (A → ★)) → (▹ μ₁ F x → μ₁F F (next (μ₁ F)) x) → μ₁ F x
        betterfix₁ {a} {A} {x} F f = fix helper
          where helper : _ → _
                helper self = roll₁ (f self)

        ▹ω-inh' : ∀ {A : ★} {x : A} (F : Endo (A → ★)) → (▸ (next (μ₁ F) ⊛′ next x) → μ₁F F (next (μ₁ F)) x) → μ₁ F x
        ▹ω-inh' {A} {x} F f = fix helper
          where helper : _ → _
                helper self = roll₁ (f (coe (sym (cong ▸ (next⊛next (μ₁ F) x))) (roll▸ self)))

        ▹ω-inh : ∀ {A} → μ₁id A
        -- ▹ω-inh {A} = fix λ self → roll₁ (coe (sym (cong ▸ (next⊛next μ₁id A))) (roll▸ self))
        ▹ω-inh {A} = betterfix₁ id (λ self → coe (sym (cong ▸ (next⊛next μ₁id A))) (roll▸ self))

        -- ▹ω-inh {A} = fix λ self → {!!} -- (coe (sym (cong ▸ (next⊛next μ₁idω A))) (roll▸ self))

    fix2 : ∀ {a} {A : ★_ a} → (▹ A → A) → A
    fix2 f = fix (f ∘ next ∘ f)

    fix≡fix2 : ∀ {a} {A : ★_ a} (f : ▹ A → A) → fix f ≡ fix2 f
    fix≡fix2 f = fix-uniq (fix f) (f ∘ next ∘ f) (trans fix-rule (cong (f ∘ next) fix-rule))

    module Streams where
        F : ★ → ★ → ★
        F A X = A × X

        -- S : ★ → ★
        -- S A = μ (F A)

        F^ : ℕ → ★ → ★ → ★
        F^ n A X = A × ▹^ n X

        S^ : ℕ → ★ → ★
        S^ n A = μ (F^ n A)

        S : ★ → ★
        S = S^ 0

        S₂ = S^ 1

        unS : ∀ {A} → S A → F A (▹ S A)
        unS = unμ (F _)

        rollS : ∀ {A} → F A (▹ S A) → S A
        rollS = rollμ (F _)

        unS^ : ∀ {A} n → S^ n A → F^ n A (▹ S^ n A)
        unS^ n = unμ (F^ n _)

        rollS^ : ∀ {A} n → F^ n A (▹ S^ n A) → S^ n A
        rollS^ n = rollμ (F^ n _)

        hd : ∀ {A} → S A → A
        hd = proj₁ ∘ unS

        tl : ∀ {A} → S A → ▹ S A
        tl = proj₂ ∘ unS

        cons : ∀ {A} n → A → ▹^ n (▹ (S^ n A)) → S^ n A
        cons n x xs = rollS^ n (x , xs)

        infixr 4 _∷_
        _∷_ : ∀ {A} → A → ▹ (S A) → S A
        _∷_ = cons 0

        infixr 4 _∷₂_
        _∷₂_ : ∀ {A} → A → ▹^ 2 (S₂ A) → S₂ A
        x ∷₂ xs = roll (x , map▹ roll▸ xs)

        repeatS : ∀ {A} → A → S A
        repeatS x = fix λ x… → x ∷ x…

        module MapS {A B : ★} (f : A → B) where
            mapSf : ▹(S A → S B) → S A → S B
            mapSf self s = f (hd s) ∷ self ⊛′ tl s

            mapS : S A → S B
            mapS = fix mapSf

            mapS2f : ▹(S A → S B) → S A → S B
            mapS2f self s = f (hd s) ∷ map▹ (λ s' → f (hd s') ∷ self ⊛′ tl s') (tl s)

            mapS2f' : ▹(S A → S B) → S A → S B
            mapS2f' self = mapSf (next (mapSf self))

            mapS2f≡mapS2f' : mapS2f ≡ mapS2f'
            mapS2f≡mapS2f' = refl

            mapS2 : S A → S B
            mapS2 = fix mapS2f

            mapS2' : S A → S B
            mapS2' = fix mapS2f'

            mapS2≡mapS2' : mapS2 ≡ mapS2'
            mapS2≡mapS2' = refl

            mapS2'' : S A → S B
            mapS2'' = fix2 mapSf

            mapS2≡mapS2'' : mapS2 ≡ mapS2''
            mapS2≡mapS2'' = refl

            mapS≡mapS2 : mapS ≡ mapS2
            mapS≡mapS2 = fix≡fix2 mapSf

        open MapS

        group2 : S ℕ → ▹ S₂ ℕ²
        group2 = fix λ self s → map▹ (λ tls → (hd s , hd tls) ∷₂ self ⊛′ tl tls) (tl s)

        ‼ : ∀ {A} → (n : ℕ) → S A → ▹^ n A
        ‼ zero    = hd
        ‼ (suc n) = map▹ (‼ n) ∘ tl

        toFun : ∀ {A} → S A → (n : ℕ) → ▹^ n A
        toFun s n = ‼ n s

        fromFun : ∀ {A} → (ℕ → A) → S A
        fromFun {A} = fix λ self (f : ℕ → A) → f 0 ∷ self ⊛′ next (f ∘ suc)

        nats : S ℕ
        nats = fix λ self → 0 ∷ map▹ (mapS suc) self

        nats2 : S ℕ
        nats2 = fix λ self → 0 ∷ map▹ (mapS2 suc) self

        nats≡nats2 : nats ≡ nats2
        nats≡nats2 rewrite mapS≡mapS2 suc = refl

        arrow : ▹ ℕ
        arrow = ‼ 1 nats

        module Sim
            {A : ★}
            (ℛ : A → A → ★)
            (ℛ-refl : Reflexive ℛ)
          where
            ≈F : ▹(S A × S A → ★) → S A × S A → ★
            ≈F X (xs , ys) = ℛ (hd xs) (hd ys) × ▸ ((map▹ curry X ⊛′ (tl xs)) ⊛′ tl ys)

            _≈_ : S A × S A → ★
            _≈_ = fix ≈F

            ≈-tail : ∀ {xs ys : S A} → _≈_ (xs , ys) → ▸ ((map▹ curry (next _≈_) ⊛′ tl xs) ⊛′ tl ys)
            ≈-tail pf = proj₂ (un₁ pf)

            {- Does not work yet
            ≈-refl : Reflexive (curry _≈_)
            ≈-refl {x} = (fix λ pf x → roll₁ {f = ≈F} (ℛ-refl , helper pf x)) x
              where helper' : _ → _ → _
                    helper' pf x = map▹ (λ f → f x) pf
                    helper : _ → _ → _
                    helper pf x = let r = helper' pf x in {!roll▸ r!}
            -}

    module DelayedStreams where
        data F (A : ★) (X : ★) : ★ where
          done  : F A X
          skip  : X → F A X
          yield : A → X → F A X

        mapF : ∀ {A B X Y} → (A → B) → (X → Y) → F A X → F B Y
        mapF f g done = done
        mapF f g (skip x) = skip (g x)
        mapF f g (yield a x) = yield (f a) (g x)

        S : ★ → ★
        S A = μ (F A)

        unS : ∀ {A} → S A → F A (▹ S A)
        unS = mapF id un▸ ∘ un

        rollS : ∀ {A} → F A (▹ S A) → S A
        rollS = roll ∘ mapF id roll▸

        unfoldS : ∀ {A X} → (X → F A (▹ X)) → X → S A
        unfoldS coalg = fix λ self x → rollS (mapF id (λ x′ → self ⊛′ x′) (coalg x))

        repeatS : ∀ {A} → A → S A
        repeatS x = fix λ self → rollS (yield x self)

        neverS : ∀ {A} → S A
        neverS = fix λ self → rollS (skip self)

        -- Co-algebra style...
        mapS : ∀ {A B} → (A → B) → S A → S B
        mapS {A} {B} f = unfoldS (mapF f id ∘ unS)

        filterF : ∀ {A X} → (A → Bool) → F A X → F A X
        filterF f done         = done
        filterF f (skip xs)    = skip xs
        filterF f (yield x xs) = if f x then yield x xs
                                        else skip xs

        filterS : ∀ {A} → (A → Bool) → S A → S A
        filterS f = unfoldS (filterF f ∘ unS)

module FuelBased where
    fix : ∀ {a} {A : ★_ a} → ℕ → (A → A) → A
    fix zero    f = STUCK where postulate STUCK : _
    fix (suc n) f = f (fix n f)

    fix-rule : ∀ {a} {A : ★_ a} (n : ℕ) {f : A → A} → fix n f ≡ f (fix n f)
    fix-rule zero        = UnsafeButPlease.trustMe
    fix-rule (suc n) {f} = cong f (fix-rule n)

    fix-uniq : ∀ {a} {A : ★_ a} (n : ℕ) (u : A) f → u ≡ f u → u ≡ fix n f
    fix-uniq zero    u f pf = UnsafeButPlease.trustMe
    fix-uniq (suc n) u f pf = trans pf (cong f (fix-uniq n u f pf))

    module I (n : ℕ) = M id id id refl (fix n) (fix-rule n) id id
                         (fix-uniq n) (λ _ _ → refl)

module HiddenFix {a} {A : ★_ a} (f : A → A) where
    -- This definition is not intended to termination-check.
    -- Use with care it's really easy to make the type-checker loop.
    {-# NO_TERMINATION_CHECK #-}
    fix : Hidden A
    fix = hide f (reveal fix)

    fix-rule : reveal fix ≡ f (reveal fix)
    fix-rule = refl {a} {A} {reveal fix}

    -- This definition is not intended to termination-check.
    -- Use with care it's really easy to make the type-checker loop.
    {-# NO_TERMINATION_CHECK #-}
    fix-uniq : (u : A) → u ≡ f u → u ≡ reveal fix
    fix-uniq u pf = trans pf (trans (cong f (fix-uniq u pf)) (sym fix-rule))

module Test where
  open HiddenFix
  open M id id id refl (reveal ∘ fix) (λ {_} {_} {f} → fix-rule f) id id
                 (λ {_} {_} u f → fix-uniq f u) (λ _ _ → refl) public
  open Streams
  two : map▹ hd (tl nats) ≡ 1
  two = refl

-- -}
-- -}
-- -}
