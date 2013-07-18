open import guarded-recursion.prelude renaming (★ to Type)
open import guarded-recursion.model

-- Agda^{ω}^{op}
module guarded-recursion.model.Agda where

  open Presheaf
            Type
            -→-
            id
            _∘′_
            idp
            idp
            idp
            𝟙
            _
            idp
         public
  open WithProducts
            _×_
            fst
            snd
            <_,_>
            idp
            idp
            idp
         public
  open Str1 ℕ
         public
  open WithMore
            𝟘
            𝟘-elim
            𝟘-elim-uniq!
            _⊎_
            inl
            inr
            [_,_]
            idp
            idp
            [,]-uniq!
         public

  <_>ᵖ : ∀ {A : Type} → A → 𝟙ᵖ →ᵖ [ A ]ᵖ 
  < x >ᵖ = (λ _ _ → x) , (λ _ → idp) 

  42s : 𝟙ᵖ →ᵖ Strᵖ
  42s = repeatᵖ < 42 >ᵖ

  test : ℕ × ℕ × ℕ × ℕ × 𝟙
  test = fst 42s 3 _

  test-test : test ≡ (42 , 42 , 42 , 42 , _)
  test-test = idp
  -- -}
  -- -}
  -- -}
  -- -}
  -- -}
