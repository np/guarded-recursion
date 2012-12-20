-- broken since the clocks are not supposed to be freely instantiable
module ...
    (Clk : ★)
    (▹ : ∀ {a} → Clk → Set a → Set a)

    (▹′ : ∀ {a} κ → ▹ κ (Set a) → Set a)
   --▹′ κ A = ▹ κ A

    (next : ∀ {κ a} {A : Set a} → A → ▹ κ A)

    (▹′-rule : ∀ {κ a} {A : Set a} → ▹′ κ (next A) ≡ ▹ κ A)
    -- (▹′-rule : ∀ {a} {A : Set a} → ▹′ ∘ next ≡ ▹_ {A})

    (fix      : ∀ {κ a} {A : Set a} → (▹ κ A → A) → A)
    (fix-rule : ∀ {κ a} {A : Set a} {f : ▹ κ A → A} → fix f ≡ f (next (fix f)))

    (_⊛_ : ∀ {κ a b} {A : Set a} {B : Set b} → ▹ κ (A → B) → ▹ κ A → ▹ κ B)

    (fix-uniq : ∀ {κ a} {A : Set a} (u : A) (f : ▹ κ A → A) → u ≡ f (next u) → u ≡ fix f)

    (next⊛next : ∀ {κ a b} {A : Set a} {B : Set b} (f : A → B) (x : A)
                 → next f ⊛ next x ≡ next {κ} (f x))

    where

    roll▹′ : ∀ {κ a} {A : Set a} → ▹ κ A → ▹′ κ (next A)
    roll▹′ = coe (sym ▹′-rule)

    un▹′ : ∀ {κ a} {A : Set a} → ▹′ κ (next A) → ▹ κ A
    un▹′ = coe ▹′-rule

    ▹Fix : ∀ {a} → Clk → Set a → Set a
    ▹Fix κ X = (▹ κ X → X) → X

    ▹Endo : ∀ {a} → Clk → Set a → Set a
    ▹Endo κ X = ▹ κ X → X

    μ : ∀ {a} → Fix (Set a)
    μ F = ∀ {κ} → fix (F ∘ ▹′ κ)

    un : ∀ {κ a f} → fix {κ} {A = Set a} f → f (next (fix f))
    un = coe fix-rule

    {-
    unμ : ∀ {κ a} f → μ {a} f → f (▹ κ (μ f))
    unμ {κ} {a} f x rewrite sym (▹′-rule {κ} {A = μ f}) = {!un {κ} x!}
    -}

    roll : ∀ {κ a f} → f (next (fix f)) → fix {κ} {A = Set a} f
    roll = coe (sym fix-rule)

    {-
    μ-rule : ∀ {κ a} f → μ {a} f ≡ f (▹ κ (μ f))
    μ-rule f = {!trans fix-rule (cong f (▹′-rule {A = μ f}))!}
    -}

    rollμ : ∀ {a} f → (∀ {κ} → f (▹ κ (μ f))) → μ {a} f
    rollμ f x {κ} = {!roll (x {κ})!}
    -- rollμ f = subst id (sym (μ-rule f))

    un₁ : ∀ {κ a b} {A : Set a} {f x} → fix {κ} {A = A → Set b} f x → f (next (fix f)) x
    un₁ = coe₁ fix-rule

    roll₁ : ∀ {κ a b} {A : Set a} {f x} → f (next (fix f)) x → fix {κ} {A = A → Set b} f x
    roll₁ = coe₁ (sym fix-rule)

    un₂ : ∀ {κ a b} {A : Set a} {B : Set b} {c f x y} → fix {κ} {A = A → B → Set c} f x y → f (next (fix f)) x y
    un₂ = coe₂ fix-rule

    roll₂ : ∀ {κ a b} {A : Set a} {B : Set b} {c f x y} → f (next (fix f)) x y → fix {κ} {A = A → B → Set c} f x y
    roll₂ = coe₂ (sym fix-rule)

    map▹ : ∀ {κ a b} {A : Set a} {B : Set b} → (A → B) → ▹ κ A → ▹ κ B
    map▹ f ▹x = next f ⊛ ▹x

    _⊛′_ : ∀ {κ a b} {A : Set a} {B : A → Set b} → ▹ κ ((x : A) → B x) → (x : A) → ▹ κ (B x)
    ▹f ⊛′ x = map▹ (λ f → f x) ▹f

    module SimpleStream where
      F : ★ → ★ → ★
      F A X = A × X

      S : ★ → ★
      S A = μ (F A)

    {-
    data IsStream (s : S A) : ★ where
      -- cons : ∀ x xs → IsStream xs → IsStream (cons x xs)
      cons : ∀ x xs → (▹ IsStream) ⊛ next xs → IsStream (cons x xs)
      cons : ∀ x xs → ▹ (IsStream xs) → IsStream (cons x xs)

      -}

    μ₁F' : ∀ {κ a} {A : Set a} → ((A → ▹ κ ★) → A → ★) → (▹ κ (A → ★) → A → ★)
    μ₁F' F self = F (λ x → (self ⊛ next x))

    μ₁F : ∀ {κ a} {A : Set a} → ((A → ★) → A → ★) → (▹ κ (A → ★) → A → ★)
    μ₁F F self = F (λ x → ▹′ _ (self ⊛ next x))

    -- μ₁ : Fix (Endo ★)
    μ₁ : ∀ {a} {A : Set a} → ((A → ★) → A → ★) → A → ★
    μ₁ F x = ∀ {κ} → fix (μ₁F {κ} F) x

    module μId where
        μid : ★
        μid = μ id

        {-
        μid-rule : μid ≡ (∀ {κ} → ▹ κ μid)
        μid-rule = {!trans fix-rule (▹′-rule {A = μ id})!}
        -}

        ω : μid
        ω = fix (rollμ id)
