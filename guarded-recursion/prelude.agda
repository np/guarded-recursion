-- Note that this module assumes function extensionality
module guarded-recursion.prelude where


open import Level
              public
              using (_⊔_)
              renaming (zero to ₀
                       ;suc  to ₛ)
open import Function
              public
              using (id; _∘_; _∘′_)
open import Data.Nat
              public
              using (ℕ; _+_)
              renaming (zero to O
                       ;suc  to S)
open import Data.Bool
              public
              renaming (Bool  to 𝟚
                       ;false to 0₂
                       ;true  to 1₂)
open import Data.Sum
              public
              using (_⊎_; [_,_])
              renaming (inj₁ to inl
                       ;inj₂ to inr)
open import Data.Maybe
              public
              using (Maybe; nothing; just)
open import Data.Empty
              public
              renaming (⊥ to 𝟘
                       ;⊥-elim to 𝟘-elim)
open import Data.Unit
              public
              using ()
          --  using (Hidden; Unit; hide; reveal)
              renaming (⊤ to 𝟙)
open import Data.Unit.NonEta
              public
              using (Hidden; Unit; hide; reveal)
import      Data.Product
open        Data.Product
              public
              using (Σ; _×_; _,_; curry; <_,_>)
              renaming (proj₁ to fst
                       ;proj₂ to snd)
open import Relation.Binary
              public
              using (Reflexive)
import      Relation.Binary.PropositionalEquality
open        Relation.Binary.PropositionalEquality
              public
              using (_≡_)
              renaming (subst to transport
                       ;refl  to idp
                       ;sym   to !
                       ;cong  to ap)
import Relation.Binary.PropositionalEquality.TrustMe
module ThisIsUnsafeButPlease = Relation.Binary.PropositionalEquality.TrustMe

-- using stdlib only
infixr 8 _∙_
_∙_ = Relation.Binary.PropositionalEquality.trans

ℕ² = ℕ × ℕ

-- Let's rename "Set₀" as "Type" to avoid confusion with set-theory
Type = Set

-- Let's rename "Set ℓ" as "Type_ ℓ" to avoid confusion with set-theory
Type_ : ∀ ℓ → Set (ₛ ℓ)
Type_ ℓ = Set ℓ

-→- : ∀ {a b} → Type_ a → Type_ b → Type_ (a ⊔ b)
-→- A B = A → B

Endo : ∀ {a} → Type_ a → Type_ a
Endo A = A → A

Fix : ∀ {a} → Type_ a → Type_ a
Fix X = (X → X) → X

postulate
  funext : ∀ {a b}
             {A : Type_ a} {B : A → Type_ b}
             {f g : (x : A) → B x}
           → (∀ x → f x ≡ g x)
           → f ≡ g

𝟘-elim-uniq! : ∀ {a} {A : Type_ a} {f : 𝟘 → A} → 𝟘-elim ≡ f
𝟘-elim-uniq! = funext (λ())

[,]-uniq! : ∀ {a b c} {A : Type_ a} {B : Type_ b} {C : Type_ c}
              {f : (A ⊎ B) → C}
            → [ f ∘ inl , f ∘ inr ] ≡ f
[,]-uniq! = funext p
  where p : (_ : _ ⊎ _) → _
        p (inl _) = idp
        p (inr _) = idp

module Coe {ℓ} where
    coe : {A B : Type_ ℓ} → A ≡ B → A → B
    coe = transport id

    coe! : {A B : Type_ ℓ} → A ≡ B → B → A
    coe! = transport id ∘ !

    module _ {a} {A : Type_ a} {P Q : A → Type_ ℓ} (p : P ≡ Q) {x} where
        coe₁ : P x → Q x
        coe₁ = transport (λ P → P x) p

        coe₁! : Q x → P x
        coe₁! = transport (λ P → P x) (! p)

    module _ {a b} {A : Type_ a} {B : Type_ b} {R S : A → B → Type_ ℓ} (p : R ≡ S) {x y} where
        coe₂ : R x y → S x y
        coe₂ = transport (λ R → R x y) p

        coe₂! : S x y → R x y
        coe₂! = transport (λ R → R x y) (! p)

[0:_1:_] : ∀ {a} {A : Type_ a} (a₀ a₁ : A) → 𝟚 → A
[0: a₀ 1: a₁ ] 0₂ = a₀
[0: a₀ 1: a₁ ] 1₂ = a₁
