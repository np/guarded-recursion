module guarded-recursion.prelude where


open import Level
              public
              using ()
              renaming (zero to ₀; suc to ₛ)
open import Function
              public
              using (id; _∘_)
open import Data.Nat
              public
              using (ℕ; zero; suc; _+_)
open import Data.Bool
              public
              renaming (Bool  to 𝟚
                       ;false to 0₂
                       ;true  to 1₂)
open import Data.Maybe
              public
              using (Maybe; nothing; just)
open import Data.Unit
              public
              using (Hidden; Unit; hide; reveal)
              renaming (⊤ to 𝟙)
import      Data.Product
open        Data.Product
              public
              using (Σ; _×_; _,_; curry)
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

Endo : ∀ {a} → ★_ a → ★_ a
Endo A = A → A

Fix : ∀ {a} → ★_ a → ★_ a
Fix X = (X → X) → X

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
