module guarded-rec where

open import Function
open import Type
open import Data.Nat
open import Data.Unit using (⊤)
open import Data.Product
open import Relation.Binary.PropositionalEquality

module M
    (▹_ : ∀ {a} → Set a → Set a)

    (▹′ : ∀ {a} → ▹ (Set a) → Set a)
   --▹′ A = ▹ A

    (next : ∀ {a} {A : Set a} → A → ▹ A)

    (▹′-rule  : ∀ {a} {A : Set a} → ▹ A → ▹′ (next A))
    (▹′-rule′ : ∀ {a} {A : Set a} → ▹′ (next A) → ▹ A)

    (fix      : ∀ {a} {A : Set a} → (▹ A → A) → A)
    (fix-rule : ∀ {a} {A : Set a} {f : ▹ A → A} → fix f ≡ f (next (fix f)))

    (_⊛_ : ∀ {a b} {A : Set a} {B : Set b} → ▹ (A → B) → ▹ A → ▹ B)

    (un : ∀ {a} {f : ▹ (Set a) → Set a} → fix f → f (next (fix f)))
   --un = subst id fix-rule

    (roll : ∀ {a} {f : ▹ (Set a) → Set a} → f (next (fix f)) → fix f)
   --roll = subst id (sym fix-rule)

    (fix-uniq : ∀ {a} {A : Set a} (u : A) f → u ≡ f (next u) → u ≡ fix f)

    (next⊛next : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) (x : A)
                 → next f ⊛ next x ≡ next (f x))

    where

    map▹ : ∀ {a b} {A : Set a} {B : Set b} → (A → B) → ▹ A → ▹ B
    map▹ f ▹x = next f ⊛ ▹x

    μid : ★
    μid = fix ▹′

    ω : μid
    ω = fix λ self → roll (▹′-rule self)

    ▹ωF : ▹(★ → ★) → ★ → ★
    ▹ωF self A = ▹′ (self ⊛ next A)

    ▹ω : ★ → ★
    ▹ω = fix ▹ωF

    ▹ω-inh : ∀ {A} → ▹ω A
    ▹ω-inh {A} = fix λ self → subst (λ x → x A)
                                (sym (fix-rule {f = ▹ωF}))
                                (subst id (sym (cong ▹′ (next⊛next ▹ω A)))
                                       (▹′-rule self))

    F : ★ → ▹ ★ → ★
    F A X = A × ▹′ X

    -- S : ★ → ★
    -- S A = fix (F A)

    ▹^ : ∀ {a} → ℕ → Set a → Set a
    ▹^ zero    A = A
    ▹^ (suc n) A = ▹ ▹^ n A

    next^ : ∀ {a} {A : Set a} n → A → ▹^ n A
    next^ zero    x = x
    next^ (suc n) x = next (next^ n x)

    map▹^ : ∀ {a b} {A : Set a} {B : Set b} n → (A → B) → ▹^ n A → ▹^ n B
    map▹^ zero    f = f
    map▹^ (suc n) f = map▹ (map▹^ n f)

    F^ : ℕ → ★ → ▹ ★ → ★
    F^ n A X = A × ▹^ n (▹′ X)

    S^ : ℕ → ★ → ★
    S^ n A = fix (F^ n A)

    S : ★ → ★
    S = S^ 0

    S₂ = S^ 1

    hd : ∀ {A} → S A → A
    hd = proj₁ ∘ un

    tl : ∀ {A} → S A → ▹ S A
    tl = ▹′-rule′ ∘ proj₂ ∘ un

    cons : ∀ {A} n → A → ▹^ n (▹ (S^ n A)) → S^ n A
    cons n x xs = roll (x , map▹^ n ▹′-rule xs)

    infixr 4 _∷_
    _∷_ : ∀ {A} → A → ▹ (S A) → S A
    _∷_ = cons 0

    infixr 4 _∷₂_
    _∷₂_ : ∀ {A} → A → ▹^ 2 (S₂ A) → S₂ A
    x ∷₂ xs = roll (x , map▹ ▹′-rule xs)

    fix2 : ∀ {a} {A : Set a} → (▹ A → A) → A
    fix2 f = fix (f ∘ next ∘ f)

    fix≡fix2 : ∀ {a} {A : Set a} (f : ▹ A → A) → fix f ≡ fix2 f
    fix≡fix2 f = fix-uniq (fix f) (f ∘ next ∘ f) (trans fix-rule (cong (f ∘ next) fix-rule))

    rep : ∀ {A} → A → S A
    rep x = fix λ x… → x ∷ x…

    module MapS {A B : ★} (f : A → B) where
        mapSf : ▹(S A → S B) → S A → S B
        mapSf self s = f (hd s) ∷ self ⊛ tl s

        mapS : S A → S B
        mapS = fix mapSf

        mapS2f : ▹(S A → S B) → S A → S B
        mapS2f self s = f (hd s) ∷ map▹ (λ s' → f (hd s') ∷ self ⊛ tl s') (tl s)
        -- mapS2f self s = f (hd s) ∷ next (λ s' → f (hd s') ∷ self ⊛ tl s') ⊛ (tl s)

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

    ℕ² = ℕ × ℕ

    group2 : S ℕ → ▹ S₂ ℕ²
    group2 = fix λ self s → map▹ (λ tls → (hd s , hd tls) ∷₂ self ⊛ tl tls) (tl s)

    ‼ : ∀ {A} → (n : ℕ) → S A → ▹^ n A
    ‼ zero    = hd
    ‼ (suc n) = map▹ (‼ n) ∘ next

    toFun : ∀ {A} → S A → (n : ℕ) → ▹^ n A
    toFun s n = ‼ n s

    fromFun : ∀ {A} → (ℕ → A) → S A
    fromFun {A} = fix λ self (f : ℕ → A) → f 0 ∷ self ⊛ next (f ∘ suc)

    -- toFun∘fromFun : ∀ {A} (f : ℕ → A) (n : ℕ) → toFun (fromFun f) n ≡ next^ n (f n)

    nats : S ℕ
    nats = fix λ self → 0 ∷ map▹ (mapS suc) self

    nats2 : S ℕ
    nats2 = fix λ self → 0 ∷ map▹ (mapS2 suc) self

    nats≡nats2 : nats ≡ nats2
    nats≡nats2 rewrite mapS≡mapS2 suc = refl

    arrow : ▹ ℕ
    arrow = ‼ 1 nats

fix : ∀ {a} {A : Set a} → ℕ → (A → A) → A
fix zero    f = STUCK where postulate STUCK : _
fix (suc n) f = f (fix n f)

open import Relation.Binary.PropositionalEquality.TrustMe

fix-rule : ∀ {a} {A : Set a} (n : ℕ) {f : A → A} → fix n f ≡ f (fix n f)
fix-rule zero        = trustMe
fix-rule (suc n) {f} = cong f (fix-rule n)

fix-uniq : ∀ {a} {A : Set a} (n : ℕ) (u : A) f → u ≡ f u → u ≡ fix n f
fix-uniq zero    u f pf = trustMe
fix-uniq (suc n) u f pf = trans pf (cong f (fix-uniq n u f pf))

module I (n : ℕ) = M id id id id id (fix n) (fix-rule n) id
                     (subst id (fix-rule n)) (subst id (sym (fix-rule n)))
                     (fix-uniq n) (λ _ _ → refl)

-- -}
-- -}
-- -}
