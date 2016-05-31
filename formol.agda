{-# OPTIONS --without-K #-}

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

-- Syntax

data Var : Set where
  vz : Var
  vs : Var → Var

data Ctx : Set where
  ·   : Ctx
  _,_ : Ctx → Var → Ctx

-- data Sort : Set where
--   Type : ℕ → Sort

data Exp : Set where
  Type : ℕ → Exp
  Π    : Exp → Exp → Exp
  Id   : Exp → Exp → Exp → Exp
  ∥_∥   : Exp → Exp
  var  : Var → Exp
  lλ   : Exp → Exp
  _∘_  : Exp → Exp → Exp
  refl : Exp → Exp
  J    : Exp → Exp → Exp → Exp → Exp → Exp → Exp
  [_]  : Exp → Exp
  elim : Exp → Exp → Exp → Exp → Exp → Exp
  seq  : Exp → Exp → Exp → Exp

data Wne : Set where
  nvar  : Var → Wne
  na_∘_ : Wne → Exp → Wne
  nelim : Exp → Exp → Exp → Exp → Wne → Wne
  nJ    : Exp → Exp → Exp → Exp → Exp → Wne → Wne

data Whnf : Set where
  nType : ℕ → Whnf
  nΠ    : Exp → Exp → Whnf
  nId   : Exp → Exp → Exp → Whnf
  n∥_∥   : Exp → Whnf
  ne    : Wne → Whnf
  nλ    : Exp → Whnf
  nrefl : Exp → Whnf
  n[_]  : Exp → Whnf
  nseq  : Exp → Exp → Exp → Whnf

data _⊢_∷_ : Ctx → Exp → Exp → Set where
  triv : ∀ Γ t T → Γ ⊢ t ∷ T

postulate ↓_ : Exp → Whnf

↑ne_ : Wne → Exp
↑ne nvar x = var x
↑ne (na n ∘ t) = (↑ne n) ∘ t
↑ne nelim T U t u n = elim T U t u (↑ne n)
↑ne nJ T U b u v n = J T U b u v (↑ne n)

↑_ : Whnf → Exp
↑ nType i = Type i
↑ nΠ A B = Π A B
↑ nId T u v = Id T u v
↑ n∥ T ∥ = ∥ T ∥
↑ ne x = ↑ne x
↑ nλ t = lλ t
↑ nrefl t = refl t
↑ n[ t ] = [ t ]
↑ nseq T u v = seq T u v

data _⊢_≡_∷_ : Ctx → Exp → Exp → Exp → Set where
  eq : ∀ e Γ t u T → Γ ⊢ e ∷ Id T t u → Γ ⊢ t ≡ u ∷ T

-- data _∧_ : Set → Set → Set where
--   _&&_ : ∀ A B → A → B → A ∧ B

mutual
  _⊢_⋈̂_∷_ : Ctx → Exp → Exp → Exp → Set
  _⊢_⋈_∷_ : Ctx → Whnf → Whnf → Whnf → Set

  Γ ⊢ t₁ ⋈̂ t₂ ∷ T = Γ ⊢ ↓ t₁ ⋈ ↓ t₂ ∷ (↓ T)

  Γ ⊢ nType j ⋈ nType k ∷ nType i = Γ ⊢ Type j ≡ Type k ∷ Type i
  Γ ⊢ nΠ A B ⋈ nΠ A' B' ∷ nType i = {!   !}
  Γ ⊢ nId x x₁ x₂ ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ n∥ x ∥ ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ ne x ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ nλ x ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ nrefl x ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ n[ x ] ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ nseq x x₁ x₂ ⋈ A₂ ∷ nType i = {!   !}
  Γ ⊢ a₁ ⋈ a₂ ∷ A = {!   !}

-- _⊢_⋈_∷_ : Ctx → Exp → Exp → Exp → Set
-- Γ ⊢ t₁ ⋈ t₂ ∷ Type i = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ Π T T₁ = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ Id T T₁ T₂ = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ ∥ T ∥ = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ var x = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ lλ T = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ (T ∘ T₁) = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ refl T = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ J T T₁ T₂ T₃ T₄ T₅ = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ [ T ] = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ elim T T₁ T₂ T₃ T₄ = {!   !}
-- Γ ⊢ t₁ ⋈ t₂ ∷ seq T T₁ T₂ = {!   !}
