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
              using (Hidden; Unit; hide; reveal)
              renaming (⊤ to 𝟙)
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

-- Let's rename "Set₀" as "★" to avoid confusion with set-theory
★ = Set

-- Let's rename "Set ℓ" as "★_ ℓ" to avoid confusion with set-theory
★_ : ∀ ℓ → Set (ₛ ℓ)
★_ ℓ = Set ℓ

-→- : ∀ {a b} → ★_ a → ★_ b → ★_ (a ⊔ b)
-→- A B = A → B

Endo : ∀ {a} → ★_ a → ★_ a
Endo A = A → A

Fix : ∀ {a} → ★_ a → ★_ a
Fix X = (X → X) → X

postulate
  funext : ∀ {a b}
             {A : ★_ a} {B : A → ★_ b}
             {f g : (x : A) → B x}
           → (∀ x → f x ≡ g x)
           → f ≡ g

𝟘-elim-uniq! : ∀ {a} {A : ★_ a} {f : 𝟘 → A} → 𝟘-elim ≡ f
𝟘-elim-uniq! = funext (λ())

[,]-uniq! : ∀ {a b c} {A : ★_ a} {B : ★_ b} {C : ★_ c}
              {f : (A ⊎ B) → C}
            → [ f ∘ inl , f ∘ inr ] ≡ f
[,]-uniq! = funext p
  where p : (_ : _ ⊎ _) → _
        p (inl _) = idp
        p (inr _) = idp

module Coe {ℓ} where
    coe : {A B : ★_ ℓ} → A ≡ B → A → B
    coe = transport id

    coe! : {A B : ★_ ℓ} → A ≡ B → B → A
    coe! = transport id ∘ !

    module _ {a} {A : ★_ a} {P Q : A → ★_ ℓ} (p : P ≡ Q) {x} where
        coe₁ : P x → Q x
        coe₁ = transport (λ P → P x) p

        coe₁! : Q x → P x
        coe₁! = transport (λ P → P x) (! p)

    module _ {a b} {A : ★_ a} {B : ★_ b} {R S : A → B → ★_ ℓ} (p : R ≡ S) {x y} where
        coe₂ : R x y → S x y
        coe₂ = transport (λ R → R x y) p

        coe₂! : S x y → R x y
        coe₂! = transport (λ R → R x y) (! p)

[0:_1:_] : ∀ {a} {A : ★_ a} (a₀ a₁ : A) → 𝟚 → A
[0: a₀ 1: a₁ ] 0₂ = a₀
[0: a₀ 1: a₁ ] 1₂ = a₁
