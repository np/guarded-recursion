open import guarded-recursion.prelude
              renaming (★ to Type)

module guarded-recursion.model where

{- not using it yet
postulate
  funext : ∀ {A : Type} {B : A → Type}
             (f g : (x : A) → B x)
           → ∀ x → f x ≡ g x
           → f ≡ g
-}

-- ℂʷᵒᵖ (ℂ^{ω}^{op})
-- Notation:
--   For the category ℂ we use superscript 'c' to disambiguate (e.g. _→ᶜ_)
--   We use ᵖ for the presheaf category.
module Presheaf
  (Objᶜ : Type)
  (_→ᶜ_ : Objᶜ → Objᶜ → Type)
  (idᶜ  : {A : Objᶜ} → A →ᶜ A)
  (_∘ᶜ_ : {A B C : Objᶜ} → (B →ᶜ C) → (A →ᶜ B) → (A →ᶜ C))
  (∘-idᶜ : {A B : Objᶜ} {f : A →ᶜ B} → f ∘ᶜ idᶜ ≡ f)
  (id-∘ᶜ : {A B : Objᶜ} {f : A →ᶜ B} → idᶜ ∘ᶜ f ≡ f)
  (∘-assocᶜ : {A B C D : Objᶜ}
              {f : C →ᶜ D} {g : B →ᶜ C} {h : A →ᶜ B}
              → (f ∘ᶜ g) ∘ᶜ h ≡ f ∘ᶜ (g ∘ᶜ h))
  (𝟙ᶜ : Objᶜ)
  (!ᶜ : {A : Objᶜ} → A →ᶜ 𝟙ᶜ)
  (!-uniqᶜ : {A : Objᶜ} {f : A →ᶜ 𝟙ᶜ} → f ≡ !ᶜ)
  where

  Objᵖ : Type
  Objᵖ = Σ (ℕ → Objᶜ) λ A →
           (n : ℕ) → A (1 + n) →ᶜ A n

  _→ᵖ_ : Objᵖ → Objᵖ → Type
  (A , rᴬ) →ᵖ (B , rᴮ) = Σ ((n : ℕ) → A n →ᶜ B n) λ f →
                            (n : ℕ) → f n ∘ᶜ rᴬ n ≡ rᴮ n ∘ᶜ f (1 + n)

  idᵖ : {A : Objᵖ} → A →ᵖ A
  idᵖ = (λ n → idᶜ) , (λ n → id-∘ᶜ ∙ ! ∘-idᶜ)

  {-
      B ---f--> D
      ^         ^
      |         |
      g         h
      |         |
      A ---i--> C
  -}
  module _ {A B C D}
           (f : B →ᶜ D) (g : A →ᶜ B)
           (h : C →ᶜ D) (i : A →ᶜ C) where
    Squareᶜ = f ∘ᶜ g ≡ h ∘ᶜ i

  module _ {A B} {f g : A →ᶜ B} where
    ap-∘ᶜ  : ∀ {X} {h : X →ᶜ A} → f ≡ g → f ∘ᶜ h ≡ g ∘ᶜ h
    ap-∘ᶜ {h = h} = ap (λ x → x ∘ᶜ h)

    ap-∘ᶜ' : ∀ {X} {h : B →ᶜ X} → f ≡ g → h ∘ᶜ f ≡ h ∘ᶜ g
    ap-∘ᶜ' {h = h} = ap (_∘ᶜ_ h)

  !-irrᶜ : {A : Objᶜ} {f g : A →ᶜ 𝟙ᶜ} → f ≡ g
  !-irrᶜ = !-uniqᶜ ∙ ! !-uniqᶜ

  ∘-!ᶜ : {A : Objᶜ} {f : 𝟙ᶜ →ᶜ A} { !g : 𝟙ᶜ →ᶜ 𝟙ᶜ} → f ∘ᶜ !g ≡ f
  ∘-!ᶜ = ap-∘ᶜ' !-irrᶜ ∙ ∘-idᶜ

  with-∘-assocᶜ : {A B C C' D : Objᶜ}
              {f  : C  →ᶜ D} {g  : B →ᶜ C}
              {f' : C' →ᶜ D} {g' : B →ᶜ C'}
              {h : A →ᶜ B}
              → f ∘ᶜ g ≡ f' ∘ᶜ g'
              → f ∘ᶜ (g ∘ᶜ h) ≡ f' ∘ᶜ (g' ∘ᶜ h)
  with-∘-assocᶜ p = ! ∘-assocᶜ ∙ ap-∘ᶜ p ∙ ∘-assocᶜ

  with-!∘-assocᶜ : {A B B' C D : Objᶜ}
              {f  : C  →ᶜ D}
              {g  : B  →ᶜ C} {h : A →ᶜ B}
              {g' : B' →ᶜ C} {h' : A →ᶜ B'}
              → g ∘ᶜ h ≡ g' ∘ᶜ h'
              → (f ∘ᶜ g) ∘ᶜ h ≡ (f ∘ᶜ g') ∘ᶜ h'
  with-!∘-assocᶜ p = ∘-assocᶜ ∙ ap-∘ᶜ' p ∙ ! ∘-assocᶜ

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
           {f : B →ᶜ D} {g : A →ᶜ B}
           {h : C →ᶜ D} {i : A →ᶜ C}
           {e : D →ᶜ F}
           {j : E →ᶜ F} {k : C →ᶜ E}
           (L : Squareᶜ f g h i)
           (R : Squareᶜ e h j k) where

      private
        efg-ehi : (e ∘ᶜ f) ∘ᶜ g ≡ e ∘ᶜ (h ∘ᶜ i)
        efg-ehi = ∘-assocᶜ ∙ ap-∘ᶜ' L

        ehi-jki : e ∘ᶜ (h ∘ᶜ i) ≡ j ∘ᶜ (k ∘ᶜ i)
        ehi-jki = ! ∘-assocᶜ ∙ ap-∘ᶜ R ∙ ∘-assocᶜ

      LR : Squareᶜ (e ∘ᶜ f) g j (k ∘ᶜ i)
      LR = efg-ehi ∙ ehi-jki

  {-
                    X
                  / . \
                /   .   \
              /     .     \
           f/       .u!     \g
          /         .         \
        v           v           v
      A <---fst--- A×B ---snd---> B
  -}
  module _
     {A B A×B X : Objᶜ}
     {fstᶜ   : A×B →ᶜ A}
     {sndᶜ   : A×B →ᶜ B}
     {f      : X →ᶜ A}
     {g      : X →ᶜ B}
     (u!     : X →ᶜ A×B)
     (fst-u! : fstᶜ ∘ᶜ u! ≡ f)
     (snd-u! : sndᶜ ∘ᶜ u! ≡ g)
     where
     1-ProductDiagram = fst-u! , snd-u!

  module ProductDiagram
     {A B A×B : Objᶜ}
     {fstᶜ : A×B →ᶜ A}
     {sndᶜ : A×B →ᶜ B}
     {<_,_>ᶜ : ∀ {X} → X →ᶜ A → X →ᶜ B → X →ᶜ A×B}
     (fst-<,> : ∀ {X} {f : X →ᶜ A} {g : X →ᶜ B}
                → fstᶜ ∘ᶜ < f , g >ᶜ ≡ f)
     (snd-<,> : ∀ {X} {f : X →ᶜ A} {g : X →ᶜ B}
                → sndᶜ ∘ᶜ < f , g >ᶜ ≡ g)
     (<,>-uniq! : ∀ {A B X : Objᶜ} {f : X →ᶜ A×B}
                  → < fstᶜ ∘ᶜ f , sndᶜ ∘ᶜ f >ᶜ ≡ f)
     where

     module _ {X} {f : X →ᶜ A} {g : X →ᶜ B} where
        1-productDiagram = 1-ProductDiagram < f , g >ᶜ fst-<,> snd-<,>

  _∘ᵖ_ : {A B C : Objᵖ} → (B →ᵖ C) → (A →ᵖ B) → (A →ᵖ C)
  (f , ☐f) ∘ᵖ (g , ☐g) = (λ n → f n ∘ᶜ g n)
                       , (λ n → LR (☐g n) (☐f n))

  -- TODO: the real thing™
  _≡ᵖ_ : {A B : Objᵖ} (f g : A →ᵖ B) → Type
  (f , _) ≡ᵖ (g , _) = ∀ n → f n ≡ g n
  infix 2 _≡ᵖ_

  ∘-idᵖ : {A B : Objᵖ} {f : A →ᵖ B} → f ∘ᵖ idᵖ ≡ᵖ f
  ∘-idᵖ _ = ∘-idᶜ

  id-∘ᵖ : {A B : Objᵖ} {f : A →ᵖ B} → idᵖ ∘ᵖ f ≡ᵖ f
  id-∘ᵖ _ = id-∘ᶜ

  ∘-assocᵖ : {A B C D : Objᵖ}
             {f : C →ᵖ D} {g : B →ᵖ C} {h : A →ᵖ B}
             → (f ∘ᵖ g) ∘ᵖ h ≡ᵖ f ∘ᵖ (g ∘ᵖ h)
  ∘-assocᵖ _ = ∘-assocᶜ

  𝟙ᵖ : Objᵖ
  𝟙ᵖ = (λ _ → 𝟙ᶜ) , (λ _ → idᶜ)
  !ᵖ : {A : Objᵖ} → A →ᵖ 𝟙ᵖ
  !ᵖ = (λ _ → !ᶜ) , (λ _ → !-irrᶜ)
  !-uniqᵖ : {A : Objᵖ} {f : A →ᵖ 𝟙ᵖ} → f ≡ᵖ !ᵖ
  !-uniqᵖ _ = !-uniqᶜ

  [_]ᵖ : Objᶜ → Objᵖ
  [ A ]ᵖ = (λ _ → A) , (λ _ → idᶜ)

  ▸ : Objᵖ → Objᵖ
  ▸ (A , rᴬ) = ▸A , ▸rᴬ
     module Later where
       ▸A : ℕ → Objᶜ
       ▸A 0       = 𝟙ᶜ
       ▸A (suc n) = A n
       ▸rᴬ : (n : ℕ) → ▸A (1 + n) →ᶜ ▸A n
       ▸rᴬ 0       = !ᶜ
       ▸rᴬ (suc n) = rᴬ n

  next : {A : Objᵖ} → A →ᵖ ▸ A
  next {A , rᴬ} = f , ☐
     module Next where
       open Later A rᴬ
       f : (n : ℕ) → A n →ᶜ ▸A n
       f 0       = !ᶜ
       f (suc n) = rᴬ n

       ☐ : (n : ℕ) → f n ∘ᶜ rᴬ n ≡ ▸rᴬ n ∘ᶜ f (1 + n)
       ☐ 0       = idp
       ☐ (suc n) = idp

  -- TODO: naturality of next

  module _ {A : Objᵖ} (f : A →ᵖ A) where
    Contractive = Σ (▸ A →ᵖ A) λ g → f ≡ᵖ g ∘ᵖ next

  module _ {A B : Objᶜ} {i : B →ᶜ B} {f : A →ᶜ B} where
    id-∘ᶜ' : i ≡ idᶜ → i ∘ᶜ f ≡ f
    id-∘ᶜ' p = ap-∘ᶜ p ∙ id-∘ᶜ
  module _ {A B : Objᶜ} {i : A →ᶜ A} {f : A →ᶜ B} where
    ∘-idᶜ' : i ≡ idᶜ → f ∘ᶜ i ≡ f
    ∘-idᶜ' p = ap-∘ᶜ' p ∙ ∘-idᶜ

  fix : {A : Objᵖ} (f : ▸ A →ᵖ A) → 𝟙ᵖ →ᵖ A
  fix {A , rᴬ} (f , ☐) = fixf , λ n → ∘-idᶜ ∙ fix☐ n
    module Fix where
      open Later A rᴬ

      fixf : (n : ℕ) → 𝟙ᶜ →ᶜ A n
      fixf 0       = f 0
      fixf (suc n) = f (suc n) ∘ᶜ fixf n

      fix☐ : (n : ℕ) → fixf n ≡ rᴬ n ∘ᶜ fixf (1 + n)
      fix☐ 0       = ! ∘-!ᶜ          ∙ with-∘-assocᶜ (☐ 0)
      fix☐ (suc n) = ap-∘ᶜ' (fix☐ n) ∙ with-∘-assocᶜ (☐ (suc n))

  module WithProducts
    (_×ᶜ_ : Objᶜ → Objᶜ → Objᶜ)
    -- projections
    (fstᶜ : ∀ {A B} → (A ×ᶜ B) →ᶜ A)
    (sndᶜ : ∀ {A B} → (A ×ᶜ B) →ᶜ B)
    -- injection (pair creation)
    (<_,_>ᶜ : ∀ {A B C} → A →ᶜ B → A →ᶜ C → A →ᶜ (B ×ᶜ C))
    -- computation rules
    (fst-<,> : ∀ {A B C} {f : A →ᶜ B} {g : A →ᶜ C}
               → fstᶜ ∘ᶜ < f , g >ᶜ ≡ f)
    (snd-<,> : ∀ {A B C} {f : A →ᶜ B} {g : A →ᶜ C}
               → sndᶜ ∘ᶜ < f , g >ᶜ ≡ g)
    -- universal property
    (<,>-uniq! : ∀ {A B X : Objᶜ} {f : X →ᶜ (A ×ᶜ B)}
                 → < fstᶜ ∘ᶜ f , sndᶜ ∘ᶜ f >ᶜ ≡ f)
    where

    firstᶜ : ∀ {A B C} → A →ᶜ B → (A ×ᶜ C) →ᶜ (B ×ᶜ C)
    firstᶜ f = < f ∘ᶜ fstᶜ , sndᶜ >ᶜ

    secondᶜ : ∀ {A B C} → B →ᶜ C → (A ×ᶜ B) →ᶜ (A ×ᶜ C)
    secondᶜ f = < fstᶜ , f ∘ᶜ sndᶜ >ᶜ

    <_×_>ᶜ : ∀ {A B C D} (f : A →ᶜ C) (g : B →ᶜ D) → (A ×ᶜ B) →ᶜ (C ×ᶜ D)
    < f × g >ᶜ = < f ∘ᶜ fstᶜ , g ∘ᶜ sndᶜ >ᶜ

    module _ {A B C} {f f' : A →ᶜ B} {g g' : A →ᶜ C} where
        ≡<_,_> : f ≡ f' → g ≡ g' → < f , g >ᶜ ≡ < f' , g' >ᶜ
        ≡< p , q > = ap (λ f → < f , g >ᶜ) p ∙ ap (λ g → < f' , g >ᶜ) q

    module _ {A B C X} {f₀ : A →ᶜ B} {f₁ : A →ᶜ C} {g : X →ᶜ A} where
        <,>-∘ : < f₀ , f₁ >ᶜ ∘ᶜ g ≡ < f₀ ∘ᶜ g , f₁ ∘ᶜ g >ᶜ
        <,>-∘ = ! <,>-uniq! ∙ ≡< ! ∘-assocᶜ ∙ ap-∘ᶜ fst-<,>
                               , ! ∘-assocᶜ ∙ ap-∘ᶜ snd-<,> >

    module _ {A B} where
        -- η-rule
        <fst,snd> : < fstᶜ , sndᶜ >ᶜ ≡ idᶜ {A ×ᶜ B}
        <fst,snd> = ≡< ! ∘-idᶜ , ! ∘-idᶜ > ∙ <,>-uniq!

        <fst,id∘snd> : < fstᶜ , idᶜ ∘ᶜ sndᶜ >ᶜ ≡ idᶜ {A ×ᶜ B}
        <fst,id∘snd> = ≡< idp , id-∘ᶜ > ∙ <fst,snd>

    _×ᵖ_ : Objᵖ → Objᵖ → Objᵖ
    (A , rᴬ) ×ᵖ (B , rᴮ) = (λ n → A n ×ᶜ B n) , (λ n → < rᴬ n × rᴮ n >ᶜ)

    <_,_>ᵖ : ∀ {A B C} → A →ᵖ B → A →ᵖ C → A →ᵖ (B ×ᵖ C)
    <_,_>ᵖ {A , rᴬ} {B , rᴮ} {C , rᶜ} (f , f☐) (g , g☐) =
      (λ n → < f n , g n >ᶜ) ,
      (λ n → <,>-∘
           ∙ ≡< f☐ n ∙ ap-∘ᶜ' (! fst-<,>) ∙ ! ∘-assocᶜ
              , g☐ n ∙ ap-∘ᶜ' (! snd-<,>) ∙ ! ∘-assocᶜ >
           ∙ ! <,>-∘)

    _^_  : Objᶜ → ℕ → Objᶜ
    A ^ 0      = 𝟙ᶜ
    A ^(suc n) = A ×ᶜ (A ^ n)

    module _ {A} where
        initᶜ : ∀ n → (A ^(1 + n)) →ᶜ (A ^ n)
        initᶜ zero    = !ᶜ
        initᶜ (suc n) = secondᶜ (initᶜ n)

    module Str1
      (A    : Objᶜ)
      where
      Str : ℕ → Objᶜ
      Str n = A ^(1 + n)

      rStr : (n : ℕ) → Str (1 + n) →ᶜ Str n
      rStr = λ n → initᶜ (1 + n)

      Strᵖ : Objᵖ
      Strᵖ = Str , rStr

      open Later Str (snd Strᵖ) renaming (▸A to ▸Str; ▸rᴬ to ▸rStr)

      roll : (n : ℕ) → (A ^ n) →ᶜ ▸Str n
      roll 0       = !ᶜ -- or idᶜ {𝟙ᶜ}
      roll (suc n) = idᶜ
      unroll : (n : ℕ) → ▸Str n →ᶜ (A ^ n)
      unroll 0       = !ᶜ -- or idᶜ {𝟙ᶜ}
      unroll (suc n) = idᶜ

      hdᵖ : Strᵖ →ᵖ [ A ]ᵖ
      hdᵖ = (λ _ → fstᶜ) , (λ n → fst-<,> ∙ ! id-∘ᶜ)

      tlᵖ : Strᵖ →ᵖ ▸ Strᵖ
      tlᵖ = f , ☐
        where
          f : (n : ℕ) → Str n →ᶜ ▸Str n
          f n = roll n ∘ᶜ sndᶜ
          ☐ : (n : ℕ) → f n ∘ᶜ rStr n ≡ ▸rStr n ∘ᶜ f (1 + n)
          ☐ 0       = !-irrᶜ
          ☐ (suc n) = ∘-assocᶜ ∙ id-∘ᶜ ∙ snd-<,> ∙ ap-∘ᶜ' (! id-∘ᶜ)

      ∷ᵖ : ([ A ]ᵖ ×ᵖ ▸ Strᵖ) →ᵖ Strᵖ
      ∷ᵖ = f , ☐
        where
          f : (n : ℕ) → (A ×ᶜ ▸Str n) →ᶜ Str n
          f n = secondᶜ (unroll n)
          ☐ : (n : ℕ) → f n ∘ᶜ snd ([ A ]ᵖ ×ᵖ ▸ Strᵖ) n ≡ rStr n ∘ᶜ f (1 + n)
          ☐ 0       = <,>-∘ ∙ ≡< fst-<,> ∙ id-∘ᶜ , !-irrᶜ > ∙ !(∘-idᶜ' <fst,id∘snd>)
          ☐ (suc n) = id-∘ᶜ' <fst,id∘snd> ∙ ≡< id-∘ᶜ , idp > ∙ !(∘-idᶜ' <fst,id∘snd>)

      repeatᵖ : (𝟙ᵖ →ᵖ [ A ]ᵖ) → 𝟙ᵖ →ᵖ Strᵖ
      repeatᵖ f = fix repeatᵖ′
        where repeatᵖ′ : ▸ Strᵖ →ᵖ Strᵖ
              repeatᵖ′ = ∷ᵖ ∘ᵖ < f ∘ᵖ !ᵖ , idᵖ >ᵖ

{-
      mapᵖ : ([ A ]ᵖ →ᵖ [ A ]ᵖ) → Strᵖ →ᵖ Strᵖ
      mapᵖ f = {!fix!}

  module _
    (A B : ℕ → Objᶜ)
    (rᴬ  : (n : ℕ) → A (1 + n) →ᶜ A n)
    (rᴮ  : (n : ℕ) → B (1 + n) →ᶜ B n)
    (f   : (n : ℕ) → A n →ᶜ B n)
    (☐f  : (n : ℕ) → f n ∘ᶜ rᴬ n ≡ rᴮ n ∘ᶜ f (1 + n))
    where

    --☐n :

-- -}
-- -}
-- -}
-- -}
