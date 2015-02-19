open import guarded-recursion.prelude

module guarded-recursion.model where

-- ℂʷᵒᵖ (ℂ^{ω}^{op})
-- Notation:
--   For the category ℂ we use superscript 'c' to disambiguate (e.g. _→ᶜ_)
--   We use ᵖ for the presheaf category.
module Presheaf
  {o m}
  (Objᶜ : Type_ o)
  (_→ᶜ_ : Objᶜ → Objᶜ → Type_ m)
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

  -- Index preserving maps
  _→ᶜ°_ : (A B : ℕ → Objᶜ) → Type_ _
  A →ᶜ° B = (n : ℕ) → A n →ᶜ B n

  Endoᶜ° : (ℕ → Objᶜ) → Type_ _
  Endoᶜ° A = A →ᶜ° A

  -- Restriction maps
  Rmap : (ℕ → Objᶜ) → Type_ _
  Rmap A = (A ∘ S) →ᶜ° A

  Objᵖ : Type_ _
  Objᵖ = Σ (ℕ → Objᶜ) Rmap

  _→ᵖ_ : Objᵖ → Objᵖ → Type_ _
  (A , rᴬ) →ᵖ (B , rᴮ) = Σ (A →ᶜ° B) λ f →
                           (n : ℕ) → f n ∘ᶜ rᴬ n ≡ rᴮ n ∘ᶜ f (1 + n)

  [_]ᵖ : Objᶜ → Objᵖ
  [ A ]ᵖ = (λ _ → A) , (λ _ → idᶜ)

  ⟨_⟩ᵖ : {A B : Objᶜ} → A →ᶜ B → [ A ]ᵖ →ᵖ [ B ]ᵖ
  ⟨ f ⟩ᵖ = (λ _ → f) , (λ n → ∘-idᶜ ∙ ! id-∘ᶜ)

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

  module _ {A B C} {f f' : B →ᶜ C} {g g'  : A →ᶜ B} where
    ap-∘ᶜ  : f ≡ f' → g ≡ g' → f ∘ᶜ g ≡ f' ∘ᶜ g'
    ap-∘ᶜ p q = ap (λ x → x ∘ᶜ g) p ∙ ap (_∘ᶜ_ f') q

  !-irrᶜ : {A : Objᶜ} {f g : A →ᶜ 𝟙ᶜ} → f ≡ g
  !-irrᶜ = !-uniqᶜ ∙ ! !-uniqᶜ

  ∘-!ᶜ : {A : Objᶜ} {f : 𝟙ᶜ →ᶜ A} { !g : 𝟙ᶜ →ᶜ 𝟙ᶜ} → f ∘ᶜ !g ≡ f
  ∘-!ᶜ = ap-∘ᶜ idp !-irrᶜ ∙ ∘-idᶜ

  with-∘-assocᶜ : {A B C C' D : Objᶜ}
              {f  : C  →ᶜ D} {g  : B →ᶜ C}
              {f' : C' →ᶜ D} {g' : B →ᶜ C'}
              {h : A →ᶜ B}
              → f ∘ᶜ g ≡ f' ∘ᶜ g'
              → f ∘ᶜ (g ∘ᶜ h) ≡ f' ∘ᶜ (g' ∘ᶜ h)
  with-∘-assocᶜ p = ! ∘-assocᶜ ∙ ap-∘ᶜ p idp ∙ ∘-assocᶜ

  with-!∘-assocᶜ : {A B B' C D : Objᶜ}
              {f  : C  →ᶜ D}
              {g  : B  →ᶜ C} {h : A →ᶜ B}
              {g' : B' →ᶜ C} {h' : A →ᶜ B'}
              → g ∘ᶜ h ≡ g' ∘ᶜ h'
              → (f ∘ᶜ g) ∘ᶜ h ≡ (f ∘ᶜ g') ∘ᶜ h'
  with-!∘-assocᶜ p = ∘-assocᶜ ∙ ap-∘ᶜ idp p ∙ ! ∘-assocᶜ

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
        efg-ehi = ∘-assocᶜ ∙ ap-∘ᶜ idp L

        ehi-jki : e ∘ᶜ (h ∘ᶜ i) ≡ j ∘ᶜ (k ∘ᶜ i)
        ehi-jki = ! ∘-assocᶜ ∙ ap-∘ᶜ R idp ∙ ∘-assocᶜ

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

  infixr 9 _∘ᵖ_
  _∘ᵖ_ : {A B C : Objᵖ} → (B →ᵖ C) → (A →ᵖ B) → (A →ᵖ C)
  (f , ☐f) ∘ᵖ (g , ☐g) = (λ n → f n ∘ᶜ g n)
                       , (λ n → LR (☐g n) (☐f n))

  -- TODO: the real thing™
  _≡ᵖ_ : {A B : Objᵖ} (f g : A →ᵖ B) → Type_ _
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

  ▸ : Objᵖ → Objᵖ
  ▸ (A , rᴬ) = ▸A , ▸rᴬ
     module Later where
       ▸A : ℕ → Objᶜ
       ▸A 0     = 𝟙ᶜ
       ▸A (S n) = A n
       ▸rᴬ : (n : ℕ) → ▸A (1 + n) →ᶜ ▸A n
       ▸rᴬ 0     = !ᶜ
       ▸rᴬ (S n) = rᴬ n

  -- ▸ functor action on morphisms
  ▸[_] : {A B : Objᵖ} → (A →ᵖ B) → ▸ A →ᵖ ▸ B
  ▸[_] {A , rᴬ} {B , rᴮ} (f , ☐) = ▸f , ▸☐
     module Later[] where
       open Later A rᴬ
       open Later B rᴮ renaming (▸A to ▸B; ▸rᴬ to ▸rᴮ)
       ▸f : ▸A →ᶜ° ▸B
       ▸f 0     = !ᶜ
       ▸f (S n) = f n
       ▸☐ : (n : ℕ) → ▸f n ∘ᶜ ▸rᴬ n ≡ ▸rᴮ n ∘ᶜ ▸f (1 + n)
       ▸☐ 0     = !-irrᶜ
       ▸☐ (S n) = ☐ n

  ▸-id : {A : Objᵖ}
       → ▸[ idᵖ {A} ] ≡ᵖ idᵖ
  ▸-id 0     = !-irrᶜ
  ▸-id (S n) = idp

  ▸-∘ : {A B C : Objᵖ} {f : B →ᵖ C} {g : A →ᵖ B}
      → ▸[ f ∘ᵖ g ] ≡ᵖ ▸[ f ] ∘ᵖ ▸[ g ]
  ▸-∘ 0     = !-irrᶜ
  ▸-∘ (S n) = idp

  {-
  ▸-[]ᵖ : {A : Objᶜ} → ▸ [ A ]ᵖ →ᵖ [ A ]ᵖ
  ▸-[]ᵖ {A} = ▸f , ▸☐
    where
      open Later (λ _ → A) (λ _ → idᶜ)
      ▸f : ▸A →ᶜ° (λ _ → A)
      ▸f O     = {!!}
      ▸f (S n) = idᶜ
      ▸☐ : (n : ℕ) → ▸f n ∘ᶜ ▸rᴬ n ≡ idᶜ ∘ᶜ ▸f (1 + n)
      ▸☐ O     = {!!}
      ▸☐ (S n) = idp
  -}

  next : {A : Objᵖ} → A →ᵖ ▸ A
  next {A , rᴬ} = f , ☐
     module Next where
       open Later A rᴬ
       f : (n : ℕ) → A n →ᶜ ▸A n
       f 0     = !ᶜ
       f (S n) = rᴬ n

       ☐ : (n : ℕ) → f n ∘ᶜ rᴬ n ≡ ▸rᴬ n ∘ᶜ f (1 + n)
       ☐ 0     = idp
       ☐ (S n) = idp

  next-nat : {A B : Objᵖ} {f : A →ᵖ B} → ▸[ f ] ∘ᵖ next ≡ᵖ next ∘ᵖ f
  next-nat             0     = !-irrᶜ
  next-nat {f = f , ☐} (S n) = ☐ n

  module _ {A : Objᵖ} (f : A →ᵖ A) where
    Contractive = Σ (▸ A →ᵖ A) λ g → f ≡ᵖ g ∘ᵖ next

  module _ {A B : Objᶜ} {i : B →ᶜ B} {f : A →ᶜ B} where
    id-∘ᶜ' : i ≡ idᶜ → i ∘ᶜ f ≡ f
    id-∘ᶜ' p = ap-∘ᶜ p idp ∙ id-∘ᶜ
  module _ {A B : Objᶜ} {i : A →ᶜ A} {f : A →ᶜ B} where
    ∘-idᶜ' : i ≡ idᶜ → f ∘ᶜ i ≡ f
    ∘-idᶜ' p = ap-∘ᶜ idp p ∙ ∘-idᶜ

  fix1 : {A : Objᵖ} (f : ▸ A →ᵖ A) → 𝟙ᵖ →ᵖ A
  fix1 {A , rᴬ} (f , ☐) = fixf , λ n → ∘-idᶜ ∙ fix☐ n
    module Fix1 where
      open Later A rᴬ

      fixf : (n : ℕ) → 𝟙ᶜ →ᶜ A n
      fixf 0     = f 0
      fixf (S n) = f (S n) ∘ᶜ fixf n

      fix☐ : (n : ℕ) → fixf n ≡ rᴬ n ∘ᶜ fixf (1 + n)
      fix☐ 0     = ! ∘-!ᶜ             ∙ with-∘-assocᶜ (☐ 0)
      fix☐ (S n) = ap-∘ᶜ idp (fix☐ n) ∙ with-∘-assocᶜ (☐ (S n))

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
        <,>-∘ = ! <,>-uniq! ∙ ≡< ! ∘-assocᶜ ∙ ap-∘ᶜ fst-<,> idp
                               , ! ∘-assocᶜ ∙ ap-∘ᶜ snd-<,> idp >

    module _ {A B} where
        -- η-rule
        <fst,snd> : < fstᶜ , sndᶜ >ᶜ ≡ idᶜ {A ×ᶜ B}
        <fst,snd> = ≡< ! ∘-idᶜ , ! ∘-idᶜ > ∙ <,>-uniq!

        <fst,id∘snd> : < fstᶜ , idᶜ ∘ᶜ sndᶜ >ᶜ ≡ idᶜ {A ×ᶜ B}
        <fst,id∘snd> = ≡< idp , id-∘ᶜ > ∙ <fst,snd>

    _×ᶜ°_ : (A B : ℕ → Objᶜ) → ℕ → Objᶜ
    (A ×ᶜ° B) n = A n ×ᶜ B n

    _×ʳ_ : {A B : ℕ → Objᶜ} → Rmap A → Rmap B → Rmap (A ×ᶜ° B)
    (rᴬ ×ʳ rᴮ) n = < rᴬ n × rᴮ n >ᶜ

    _×ᵖ_ : Objᵖ → Objᵖ → Objᵖ
    (A , rᴬ) ×ᵖ (B , rᴮ) = (A ×ᶜ° B) , (rᴬ ×ʳ rᴮ)

    fstᵖ : ∀ {A B} → (A ×ᵖ B) →ᵖ A
    fstᵖ = (λ _ → fstᶜ) , (λ _ → fst-<,>)

    sndᵖ : ∀ {A B} → (A ×ᵖ B) →ᵖ B
    sndᵖ = (λ _ → sndᶜ) , (λ _ → snd-<,>)

    <_,_>ᵖ : ∀ {A B C} → A →ᵖ B → A →ᵖ C → A →ᵖ (B ×ᵖ C)
    <_,_>ᵖ {A , rᴬ} {B , rᴮ} {C , rᶜ} (f , f☐) (g , g☐) =
      (λ n → < f n , g n >ᶜ) ,
      (λ n → <,>-∘
           ∙ ≡< f☐ n ∙ ap-∘ᶜ idp (! fst-<,>) ∙ ! ∘-assocᶜ
              , g☐ n ∙ ap-∘ᶜ idp (! snd-<,>) ∙ ! ∘-assocᶜ >
           ∙ ! <,>-∘)

    firstᵖ : ∀ {A B C} → A →ᵖ B → (A ×ᵖ C) →ᵖ (B ×ᵖ C)
    firstᵖ f = < f ∘ᵖ fstᵖ , sndᵖ >ᵖ

    ▸-× : {A B : Objᵖ} → ▸(A ×ᵖ B) →ᵖ (▸ A ×ᵖ ▸ B)
    ▸-× {A , rᴬ} {B , rᴮ} = ▸f , ▸☐
      module LaterProduct where
          open Later A rᴬ
          open Later B rᴮ                 renaming (▸A to ▸B; ▸rᴬ to ▸rᴮ)
          open Later (A ×ᶜ° B) (rᴬ ×ʳ rᴮ) renaming (▸A to ▸AB; ▸rᴬ to ▸rᴬᴮ)
          ▸f : ▸AB →ᶜ° (▸A ×ᶜ° ▸B)
          ▸f 0     = < !ᶜ , !ᶜ >ᶜ
          ▸f (S n) = idᶜ
          ▸☐ : (n : ℕ) → ▸f n ∘ᶜ ▸rᴬᴮ n ≡ (▸rᴬ ×ʳ ▸rᴮ) n ∘ᶜ ▸f (1 + n)
          ▸☐ 0     = <,>-∘ ∙ ≡< !-irrᶜ , !-irrᶜ > ∙ ! ∘-idᶜ
          ▸☐ (S n) = id-∘ᶜ ∙ ! ∘-idᶜ

    _^_  : Objᶜ → ℕ → Objᶜ
    A ^ 0    = 𝟙ᶜ
    A ^(S n) = A ×ᶜ (A ^ n)

    fix : {A B : Objᵖ} (f : (B ×ᵖ ▸ A) →ᵖ A) → B →ᵖ A
    fix {A , rᴬ} {B , rᴮ} (f , ☐) = fixf , fix☐
     module Fix where
      open Later A rᴬ
      open Later B rᴮ renaming (▸A to ▸B; ▸rᴬ to ▸rᴮ)

      fixf : (n : ℕ) → B n →ᶜ A n
      fixf 0     = f 0 ∘ᶜ < idᶜ , !ᶜ >ᶜ
      fixf (S n) = f (S n) ∘ᶜ < idᶜ , fixf n ∘ᶜ rᴮ n >ᶜ

      fix☐ : (n : ℕ) → fixf n ∘ᶜ rᴮ n ≡ rᴬ n ∘ᶜ fixf (1 + n)
      fix☐ 0     = ∘-assocᶜ ∙ ap-∘ᶜ idp (<,>-∘ ∙ ≡< id-∘ᶜ ∙ ! (∘-idᶜ' fst-<,>) ∙ ! ∘-assocᶜ , !-irrᶜ > ∙ ! <,>-∘) ∙ with-∘-assocᶜ (☐ 0)
      fix☐ (S n) = ∘-assocᶜ ∙ ap-∘ᶜ idp (<,>-∘ ∙ ≡< id-∘ᶜ ∙ ! (∘-idᶜ' fst-<,>) ∙ ! ∘-assocᶜ , h      > ∙ ! <,>-∘) ∙ with-∘-assocᶜ (☐ (S n))
        where h = ap-∘ᶜ (fix☐ n) idp ∙ with-!∘-assocᶜ (! snd-<,>)

    module _ {A} where
        initᶜ : ∀ n → (A ^(1 + n)) →ᶜ (A ^ n)
        initᶜ 0     = !ᶜ
        initᶜ (S n) = secondᶜ (initᶜ n)

    module Str1
      (A    : Objᶜ)
      where

      Aᵖ = [ A ]ᵖ

      Str : ℕ → Objᶜ
      Str n = A ^(1 + n)

      rStr : (n : ℕ) → Str (1 + n) →ᶜ Str n
      rStr = λ n → initᶜ (1 + n)

      Strᵖ : Objᵖ
      Strᵖ = Str , rStr

      open Later Str (snd Strᵖ) renaming (▸A to ▸Str; ▸rᴬ to ▸rStr)

      roll : (n : ℕ) → (A ^ n) →ᶜ ▸Str n
      roll 0     = !ᶜ -- or idᶜ {𝟙ᶜ}
      roll (S n) = idᶜ
      unroll : (n : ℕ) → ▸Str n →ᶜ (A ^ n)
      unroll 0     = !ᶜ -- or idᶜ {𝟙ᶜ}
      unroll (S n) = idᶜ

      hdᵖ : Strᵖ →ᵖ Aᵖ
      hdᵖ = (λ _ → fstᶜ) , (λ n → fst-<,> ∙ ! id-∘ᶜ)

      tlᵖ : Strᵖ →ᵖ ▸ Strᵖ
      tlᵖ = f , ☐
        where
          f : (n : ℕ) → Str n →ᶜ ▸Str n
          f n = roll n ∘ᶜ sndᶜ
          ☐ : (n : ℕ) → f n ∘ᶜ rStr n ≡ ▸rStr n ∘ᶜ f (1 + n)
          ☐ 0     = !-irrᶜ
          ☐ (S n) = ∘-assocᶜ ∙ id-∘ᶜ ∙ snd-<,> ∙ ap-∘ᶜ idp (! id-∘ᶜ)

      ∷ᵖ : (Aᵖ ×ᵖ ▸ Strᵖ) →ᵖ Strᵖ
      ∷ᵖ = f , ☐
        where
          f : (n : ℕ) → (A ×ᶜ ▸Str n) →ᶜ Str n
          f n = secondᶜ (unroll n)
          ☐ : (n : ℕ) → f n ∘ᶜ snd (Aᵖ ×ᵖ ▸ Strᵖ) n ≡ rStr n ∘ᶜ f (1 + n)
          ☐ 0     = <,>-∘ ∙ ≡< fst-<,> ∙ id-∘ᶜ , !-irrᶜ > ∙ !(∘-idᶜ' <fst,id∘snd>)
          ☐ (S n) = id-∘ᶜ' <fst,id∘snd> ∙ ≡< id-∘ᶜ , idp > ∙ !(∘-idᶜ' <fst,id∘snd>)

      repeatᵖ : (𝟙ᵖ →ᵖ Aᵖ) → 𝟙ᵖ →ᵖ Strᵖ
      repeatᵖ f = fix1 it
        where it : ▸ Strᵖ →ᵖ Strᵖ
              it = ∷ᵖ ∘ᵖ < f ∘ᵖ !ᵖ , idᵖ >ᵖ

      {-
      iterate f x = x ∷ iterate f (f x)
      or 
      iterate f = (∷) id (iterate f ∘ f)
      -}
      {-
      iterateᵖ : (Aᵖ →ᵖ Aᵖ) → Aᵖ →ᵖ Strᵖ
      iterateᵖ f = fix it -- sndᵖ ∘ᵖ fix it ∘ᵖ !ᵖ
        where
           it : Aᵖ ×ᵖ ▸ Strᵖ →ᵖ Strᵖ
           it = < fstᵖ , ∷ᵖ >ᵖ ∘ᵖ firstᵖ (f ∘ᵖ {!!}) ∘ᵖ ▸-×
      -}

{-
      mapᵖ : ([ A ]ᵖ →ᵖ [ A ]ᵖ) → Strᵖ →ᵖ Strᵖ
      mapᵖ f = {!fix!}
-}

  Objᶜ↑ : ℕ → Endo (ℕ → Objᶜ)
  Objᶜ↑ k A n = A (n + k)

  ↑ᶜ° : ∀ k {A B} → A →ᶜ° B → Objᶜ↑ k A →ᶜ° Objᶜ↑ k B
  ↑ᶜ° k f n = f (n + k)

  ↑r : ∀ k {A} → Rmap A → Rmap (Objᶜ↑ k A)
  ↑r k rᴬ n = rᴬ (n + k)

  Objᵖ↑ : ℕ → Endo Objᵖ
  Objᵖ↑ k (A , rᴬ) = Objᶜ↑ k A , ↑r k rᴬ

  r* : {A : ℕ → Objᶜ}
       (rᴬ : Rmap A)
       (n : ℕ) → A (1 + n) →ᶜ A 0
  r* rᴬ 0     = rᴬ 0
  r* rᴬ (S n) = r* rᴬ n ∘ᶜ rᴬ (S n)

  module _
    {A B : ℕ → Objᶜ}
    {rᴬ  : (n : ℕ) → A (1 + n) →ᶜ A n}
    {rᴮ  : (n : ℕ) → B (1 + n) →ᶜ B n}
    (f   : (n : ℕ) → A n →ᶜ B n)
    (☐f  : (n : ℕ) → f n ∘ᶜ rᴬ n ≡ rᴮ n ∘ᶜ f (1 + n))
    where

    ☐* : (n : ℕ) → f 0 ∘ᶜ r* rᴬ n ≡ r* rᴮ n ∘ᶜ f (1 + n)
    ☐* 0     = ☐f 0
    ☐* (S n) = ! ∘-assocᶜ
             ∙ ap-∘ᶜ (☐* n) idp
             ∙ ∘-assocᶜ
             ∙ ap-∘ᶜ idp (☐f (S n))
             ∙ ! ∘-assocᶜ

  module _
    {A B : ℕ → Objᶜ}
    {rᴬ  : (n : ℕ) → A (1 + n) →ᶜ A n}
    {rᴮ  : (n : ℕ) → B (1 + n) →ᶜ B n}
    (f   : (n : ℕ) → A n →ᶜ B n)
    (☐f  : (n : ℕ) → f n ∘ᶜ rᴬ n ≡ rᴮ n ∘ᶜ f (1 + n))
    (k : ℕ)
    where

    --☐*' : (n : ℕ) → f k ∘ᶜ r* (↑r k rᴬ) n ≡ r* (↑r k rᴮ) n ∘ᶜ f ((1 + n) + k)
    --☐*' n = ☐* (↑ᶜ° k f) {!!} n

  module WithMore -- TODO upto topos
    -- Initial object
    (𝟘ᶜ : Objᶜ)
    (¡ᶜ : {A : Objᶜ} → 𝟘ᶜ →ᶜ A)
    (¡-uniqᶜ : {A : Objᶜ} {f : 𝟘ᶜ →ᶜ A} → ¡ᶜ ≡ f)

    -- Coproducts
    (_+ᶜ_ : Objᶜ → Objᶜ → Objᶜ)
    -- injections
    (inlᶜ : ∀ {A B} → A →ᶜ (A +ᶜ B))
    (inrᶜ : ∀ {A B} → B →ᶜ (A +ᶜ B))
    -- projection (coproduct elimination)
    ([_,_]ᶜ : ∀ {A B C} → B →ᶜ A → C →ᶜ A → (B +ᶜ C) →ᶜ A)
    -- computation rules
    ([,]-inl : ∀ {A B C} {f : B →ᶜ A} {g : C →ᶜ A}
               → [ f , g ]ᶜ ∘ᶜ inlᶜ ≡ f)
    ([,]-inr : ∀ {A B C} {f : B →ᶜ A} {g : C →ᶜ A}
               → [ f , g ]ᶜ ∘ᶜ inrᶜ ≡ g)
    -- universal property
    ([,]-uniq! : ∀ {A B X : Objᶜ} {f : (A +ᶜ B) →ᶜ X}
                 → [ f ∘ᶜ inlᶜ , f ∘ᶜ inrᶜ ]ᶜ ≡ f)
    where
-- -}
-- -}
-- -}
-- -}
