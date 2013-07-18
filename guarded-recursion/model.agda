open import Data.Nat
  using (ℕ; zero; suc; _+_)
open import Data.Product
  using (Σ; _,_)
  renaming (proj₁ to fst; proj₂ to snd)
{-
-- using agda-nplib
open import Relation.Binary.PropositionalEquality.NP
  using (_≡_; _∙_; !; ap; idp)
-}
-- using stdlib only
open import Relation.Binary.PropositionalEquality
  using (_≡_; trans)
  renaming (sym to !; refl to idp; cong to ap)

module guarded-recursion.model where

-- using stdlib only
infixr 8 _∙_
_∙_ = trans

Type = Set

postulate
  funext : ∀ {A : Type} {B : A → Type}
             (f g : (x : A) → B x)
           → ∀ x → f x ≡ g x
           → f ≡ g

-- ℂʷᵒᵖ (ℂ^{ω}^{op})
module Presheaf
  (Objⁱ : Type)
  (_→ⁱ_ : Objⁱ → Objⁱ → Type)
  (idⁱ  : {A : Objⁱ} → A →ⁱ A)
  (_∘ⁱ_ : {A B C : Objⁱ} → (B →ⁱ C) → (A →ⁱ B) → (A →ⁱ C))
  (∘-idⁱ : {A B : Objⁱ} {f : A →ⁱ B} → f ∘ⁱ idⁱ ≡ f)
  (id-∘ⁱ : {A B : Objⁱ} {f : A →ⁱ B} → idⁱ ∘ⁱ f ≡ f)
  (∘-assocⁱ : {A B C D : Objⁱ}
              {f : C →ⁱ D} {g : B →ⁱ C} {h : A →ⁱ B}
              → (f ∘ⁱ g) ∘ⁱ h ≡ f ∘ⁱ (g ∘ⁱ h))
  (𝟙ⁱ : Objⁱ)
  (!ⁱ : {A : Objⁱ} → A →ⁱ 𝟙ⁱ)
  (!-uniqⁱ : {A : Objⁱ} {f : A →ⁱ 𝟙ⁱ} → f ≡ !ⁱ)
  where

  Objᵖ : Type
  Objᵖ = Σ (ℕ → Objⁱ) λ A →
           (n : ℕ) → A (1 + n) →ⁱ A n

  _→ᵖ_ : Objᵖ → Objᵖ → Type
  (A , rᴬ) →ᵖ (B , rᴮ) = Σ ((n : ℕ) → A n →ⁱ B n) λ f →
                            (n : ℕ) → f n ∘ⁱ rᴬ n ≡ rᴮ n ∘ⁱ f (1 + n)

  idᵖ : {A : Objᵖ} → A →ᵖ A
  idᵖ = (λ n → idⁱ) , (λ n → id-∘ⁱ ∙ ! ∘-idⁱ)

  {-
      B ---f--> D
      ^         ^
      |         |
      g         h
      |         |
      A ---i--> C
  -}
  module _ {A B C D}
           (f : B →ⁱ D) (g : A →ⁱ B)
           (h : C →ⁱ D) (i : A →ⁱ C) where
    Squareⁱ = f ∘ⁱ g ≡ h ∘ⁱ i

  module _ {A B} {f g : A →ⁱ B} where
    ap-∘ⁱ  : ∀ {X} {h : X →ⁱ A} → f ≡ g → f ∘ⁱ h ≡ g ∘ⁱ h
    ap-∘ⁱ {h = h} = ap (λ x → x ∘ⁱ h)

    ap-∘ⁱ' : ∀ {X} {h : B →ⁱ X} → f ≡ g → h ∘ⁱ f ≡ h ∘ⁱ g
    ap-∘ⁱ' {h = h} = ap (_∘ⁱ_ h)

  !-irrⁱ : {A : Objⁱ} {f g : A →ⁱ 𝟙ⁱ} → f ≡ g
  !-irrⁱ = !-uniqⁱ ∙ ! !-uniqⁱ

  ∘-!ⁱ : {A : Objⁱ} {f : 𝟙ⁱ →ⁱ A} { !g : 𝟙ⁱ →ⁱ 𝟙ⁱ} → f ∘ⁱ !g ≡ f
  ∘-!ⁱ = ap-∘ⁱ' !-irrⁱ ∙ ∘-idⁱ

  with-∘-assocⁱ : {A B C C' D : Objⁱ}
              {f  : C  →ⁱ D} {g  : B →ⁱ C}
              {f' : C' →ⁱ D} {g' : B →ⁱ C'}
              {h : A →ⁱ B}
              → f ∘ⁱ g ≡ f' ∘ⁱ g'
              → f ∘ⁱ (g ∘ⁱ h) ≡ f' ∘ⁱ (g' ∘ⁱ h)
  with-∘-assocⁱ p = ! ∘-assocⁱ ∙ ap-∘ⁱ p ∙ ∘-assocⁱ

  {-
      B ---f--> D ---e--> F
      ^         ^         ^
      |         |         |
      g    L    h    R    j
      |         |         |
      A ---i--> C ---k--> E
  -}
  module _
           {A B C D E F}
           {f : B →ⁱ D} {g : A →ⁱ B}
           {h : C →ⁱ D} {i : A →ⁱ C}
           {e : D →ⁱ F}
           {j : E →ⁱ F} {k : C →ⁱ E}
           (L : Squareⁱ f g h i)
           (R : Squareⁱ e h j k) where

      private
        efg-ehi : (e ∘ⁱ f) ∘ⁱ g ≡ e ∘ⁱ (h ∘ⁱ i)
        efg-ehi = ∘-assocⁱ ∙ ap-∘ⁱ' L

        ehi-jki : e ∘ⁱ (h ∘ⁱ i) ≡ j ∘ⁱ (k ∘ⁱ i)
        ehi-jki = ! ∘-assocⁱ ∙ ap-∘ⁱ R ∙ ∘-assocⁱ

      LR : Squareⁱ (e ∘ⁱ f) g j (k ∘ⁱ i)
      LR = efg-ehi ∙ ehi-jki

  _∘ᵖ_ : {A B C : Objᵖ} → (B →ᵖ C) → (A →ᵖ B) → (A →ᵖ C)
  (f , ☐f) ∘ᵖ (g , ☐g) = (λ n → f n ∘ⁱ g n)
                       , (λ n → LR (☐g n) (☐f n))

  -- TODO: the real thing™
  _≡ᵖ_ : {A B : Objᵖ} (f g : A →ᵖ B) → Type
  (f , _) ≡ᵖ (g , _) = ∀ n → f n ≡ g n
  infix 2 _≡ᵖ_

  ∘-idᵖ : {A B : Objᵖ} {f : A →ᵖ B} → f ∘ᵖ idᵖ ≡ᵖ f
  ∘-idᵖ _ = ∘-idⁱ

  id-∘ᵖ : {A B : Objᵖ} {f : A →ᵖ B} → idᵖ ∘ᵖ f ≡ᵖ f
  id-∘ᵖ _ = id-∘ⁱ

  ∘-assocᵖ : {A B C D : Objᵖ}
             {f : C →ᵖ D} {g : B →ᵖ C} {h : A →ᵖ B}
             → (f ∘ᵖ g) ∘ᵖ h ≡ᵖ f ∘ᵖ (g ∘ᵖ h)
  ∘-assocᵖ _ = ∘-assocⁱ

  𝟙ᵖ : Objᵖ
  𝟙ᵖ = (λ _ → 𝟙ⁱ) , (λ _ → idⁱ)
  !ᵖ : {A : Objᵖ} → A →ᵖ 𝟙ᵖ
  !ᵖ = (λ _ → !ⁱ) , (λ _ → !-irrⁱ)
  !-uniqᵖ : {A : Objᵖ} {f : A →ᵖ 𝟙ᵖ} → f ≡ᵖ !ᵖ
  !-uniqᵖ _ = !-uniqⁱ

  [_]ᵖ : Objⁱ → Objᵖ
  [ A ]ᵖ = (λ _ → A) , (λ _ → idⁱ)

  ▸ : Objᵖ → Objᵖ
  ▸ (A , rᴬ) = ▸A , ▸rᴬ
     module Later where
       ▸A : ℕ → Objⁱ
       ▸A 0       = 𝟙ⁱ
       ▸A (suc n) = A n
       ▸rᴬ : (n : ℕ) → ▸A (1 + n) →ⁱ ▸A n
       ▸rᴬ 0       = !ⁱ
       ▸rᴬ (suc n) = rᴬ n

  next : {A : Objᵖ} → A →ᵖ ▸ A
  next {A , rᴬ} = f , ☐
     module Next where
       open Later A rᴬ
       f : (n : ℕ) → A n →ⁱ ▸A n
       f 0       = !ⁱ
       f (suc n) = rᴬ n

       ☐ : (n : ℕ) → f n ∘ⁱ rᴬ n ≡ ▸rᴬ n ∘ⁱ f (1 + n)
       ☐ 0       = idp
       ☐ (suc n) = idp

  -- TODO: naturality of next

  module _ {A : Objᵖ} (f : A →ᵖ A) where
    Contractive = Σ (▸ A →ᵖ A) λ g → f ≡ᵖ g ∘ᵖ next

  module _ {A B : Objⁱ} {i : B →ⁱ B} {f : A →ⁱ B} where
    id-∘ⁱ' : i ≡ idⁱ → i ∘ⁱ f ≡ f
    id-∘ⁱ' p = ap-∘ⁱ p ∙ id-∘ⁱ
  module _ {A B : Objⁱ} {i : A →ⁱ A} {f : A →ⁱ B} where
    ∘-idⁱ' : i ≡ idⁱ → f ∘ⁱ i ≡ f
    ∘-idⁱ' p = ap-∘ⁱ' p ∙ ∘-idⁱ

  fix : {A : Objᵖ} (f : ▸ A →ᵖ A) → 𝟙ᵖ →ᵖ A
  fix {A , rᴬ} (f , ☐) = fixf , λ n → ∘-idⁱ ∙ fix☐ n
    module Fix where
      open Later A rᴬ

      fixf : (n : ℕ) → 𝟙ⁱ →ⁱ A n
      fixf 0       = f 0
      fixf (suc n) = f (suc n) ∘ⁱ fixf n

      fix☐ : (n : ℕ) → fixf n ≡ rᴬ n ∘ⁱ fixf (1 + n)
      fix☐ 0       = ! ∘-!ⁱ          ∙ with-∘-assocⁱ (☐ 0)
      fix☐ (suc n) = ap-∘ⁱ' (fix☐ n) ∙ with-∘-assocⁱ (☐ (suc n))

  module WithProducts
    (_×ⁱ_ : Objⁱ → Objⁱ → Objⁱ)
    -- projections
    (fstⁱ : ∀ {A B} → (A ×ⁱ B) →ⁱ A)
    (sndⁱ : ∀ {A B} → (A ×ⁱ B) →ⁱ B)
    -- injection (pair creation)
    (<_,_>ⁱ : ∀ {A B C} → A →ⁱ B → A →ⁱ C → A →ⁱ (B ×ⁱ C))
    -- computation rules
    (fst-<,> : ∀ {A B C} {f : A →ⁱ B} {g : A →ⁱ C}
               → fstⁱ ∘ⁱ < f , g >ⁱ ≡ f)
    (snd-<,> : ∀ {A B C} {f : A →ⁱ B} {g : A →ⁱ C}
               → sndⁱ ∘ⁱ < f , g >ⁱ ≡ g)
    -- η-rule
    (<fst,snd> : ∀ {A B} → < fstⁱ , sndⁱ >ⁱ ≡ idⁱ {A ×ⁱ B})
    -- universal property
    (<,>-∘ : ∀ {A B C X} {f₀ : A →ⁱ B} {f₁ : A →ⁱ C} {g : X →ⁱ A}
             → < f₀ , f₁ >ⁱ ∘ⁱ g ≡ < f₀ ∘ⁱ g , f₁ ∘ⁱ g >ⁱ)
    where

    firstⁱ : ∀ {A B C} → A →ⁱ B → (A ×ⁱ C) →ⁱ (B ×ⁱ C)
    firstⁱ f = < f ∘ⁱ fstⁱ , sndⁱ >ⁱ

    secondⁱ : ∀ {A B C} → B →ⁱ C → (A ×ⁱ B) →ⁱ (A ×ⁱ C)
    secondⁱ f = < fstⁱ , f ∘ⁱ sndⁱ >ⁱ

    <_×_>ⁱ : ∀ {A B C D} (f : A →ⁱ C) (g : B →ⁱ D) → (A ×ⁱ B) →ⁱ (C ×ⁱ D)
    < f × g >ⁱ = < f ∘ⁱ fstⁱ , g ∘ⁱ sndⁱ >ⁱ

    module _ {A B C} {f f' : A →ⁱ B} {g g' : A →ⁱ C} where
        ≡<_,_> : f ≡ f' → g ≡ g' → < f , g >ⁱ ≡ < f' , g' >ⁱ
        ≡< p , q > = ap (λ f → < f , g >ⁱ) p ∙ ap (λ g → < f' , g >ⁱ) q

    module _ {A B} where
        <fst,id∘snd> : < fstⁱ , idⁱ ∘ⁱ sndⁱ >ⁱ ≡ idⁱ {A ×ⁱ B}
        <fst,id∘snd> = ≡< idp , id-∘ⁱ > ∙ <fst,snd>

    _×ᵖ_ : Objᵖ → Objᵖ → Objᵖ
    (A , rᴬ) ×ᵖ (B , rᴮ) = (λ n → A n ×ⁱ B n) , (λ n → < rᴬ n × rᴮ n >ⁱ)

    <_,_>ᵖ : ∀ {A B C} → A →ᵖ B → A →ᵖ C → A →ᵖ (B ×ᵖ C)
    <_,_>ᵖ {A , rᴬ} {B , rᴮ} {C , rᶜ} (f , f☐) (g , g☐) =
      (λ n → < f n , g n >ⁱ) ,
      (λ n → <,>-∘
           ∙ ≡< f☐ n ∙ ap-∘ⁱ' (! fst-<,>) ∙ ! ∘-assocⁱ
              , g☐ n ∙ ap-∘ⁱ' (! snd-<,>) ∙ ! ∘-assocⁱ >
           ∙ ! <,>-∘)

    _^_  : Objⁱ → ℕ → Objⁱ
    A ^ 0      = 𝟙ⁱ
    A ^(suc n) = A ×ⁱ (A ^ n)

    module _ {A} where
        initⁱ : ∀ n → (A ^(1 + n)) →ⁱ (A ^ n)
        initⁱ zero    = !ⁱ
        initⁱ (suc n) = secondⁱ (initⁱ n)

    module Str1
      (A    : Objⁱ)
      where
      Str : ℕ → Objⁱ
      Str n = A ^(1 + n)

      rStr : (n : ℕ) → Str (1 + n) →ⁱ Str n
      rStr = λ n → initⁱ (1 + n)

      Strᵖ : Objᵖ
      Strᵖ = Str , rStr

      open Later Str (snd Strᵖ) renaming (▸A to ▸Str; ▸rᴬ to ▸rStr)

      roll : (n : ℕ) → (A ^ n) →ⁱ ▸Str n
      roll 0       = !ⁱ -- or idⁱ {𝟙ⁱ}
      roll (suc n) = idⁱ
      unroll : (n : ℕ) → ▸Str n →ⁱ (A ^ n)
      unroll 0       = !ⁱ -- or idⁱ {𝟙ⁱ}
      unroll (suc n) = idⁱ

      hdᵖ : Strᵖ →ᵖ [ A ]ᵖ
      hdᵖ = (λ _ → fstⁱ) , (λ n → fst-<,> ∙ ! id-∘ⁱ)

      tlᵖ : Strᵖ →ᵖ ▸ Strᵖ
      tlᵖ = f , ☐
        where
          f : (n : ℕ) → Str n →ⁱ ▸Str n
          f n = roll n ∘ⁱ sndⁱ
          ☐ : (n : ℕ) → f n ∘ⁱ rStr n ≡ ▸rStr n ∘ⁱ f (1 + n)
          ☐ 0       = !-irrⁱ
          ☐ (suc n) = ∘-assocⁱ ∙ id-∘ⁱ ∙ snd-<,> ∙ ap-∘ⁱ' (! id-∘ⁱ)

      ∷ᵖ : ([ A ]ᵖ ×ᵖ ▸ Strᵖ) →ᵖ Strᵖ
      ∷ᵖ = f , ☐
        where
          f : (n : ℕ) → (A ×ⁱ ▸Str n) →ⁱ Str n
          f n = secondⁱ (unroll n)
          ☐ : (n : ℕ) → f n ∘ⁱ snd ([ A ]ᵖ ×ᵖ ▸ Strᵖ) n ≡ rStr n ∘ⁱ f (1 + n)
          ☐ 0       = <,>-∘ ∙ ≡< fst-<,> ∙ id-∘ⁱ , !-irrⁱ > ∙ !(∘-idⁱ' <fst,id∘snd>)
          ☐ (suc n) = id-∘ⁱ' <fst,id∘snd> ∙ ≡< id-∘ⁱ , idp > ∙ !(∘-idⁱ' <fst,id∘snd>)

      repeatᵖ : (𝟙ᵖ →ᵖ [ A ]ᵖ) → 𝟙ᵖ →ᵖ Strᵖ
      repeatᵖ f = fix repeatᵖ′
        where repeatᵖ′ : ▸ Strᵖ →ᵖ Strᵖ
              repeatᵖ′ = ∷ᵖ ∘ᵖ < f ∘ᵖ !ᵖ , idᵖ >ᵖ

{-
      mapᵖ : ([ A ]ᵖ →ᵖ [ A ]ᵖ) → Strᵖ →ᵖ Strᵖ
      mapᵖ f = {!fix!}

  module _
    (A B : ℕ → Objⁱ)
    (rᴬ  : (n : ℕ) → A (1 + n) →ⁱ A n)
    (rᴮ  : (n : ℕ) → B (1 + n) →ⁱ B n)
    (f   : (n : ℕ) → A n →ⁱ B n)
    (☐f  : (n : ℕ) → f n ∘ⁱ rᴬ n ≡ rᴮ n ∘ⁱ f (1 + n))
    where

    --☐n :

-- -}
-- -}
-- -}
-- -}
