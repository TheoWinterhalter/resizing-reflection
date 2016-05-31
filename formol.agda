{-# OPTIONS --without-K --sized-types #-}

open import Size

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

data Exp : {i : Size} → Set where
  Type : {i : Size} → ℕ → Exp {i}
  Π    : {i : Size} → Exp {i} → Exp {i} → Exp {↑ i}
  Id   : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {↑ i}
  ∥_∥   : {i : Size} → Exp {i} → Exp {↑ i}
  var  : {i : Size} → Var → Exp {i}
  lλ   : {i : Size} → Exp {i} → Exp {↑ i}
  _∘_  : {i : Size} → Exp {i} → Exp {i} → Exp {↑ i}
  refl : {i : Size} → Exp {i} → Exp {↑ i}
  J    : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {↑ i}
  [_]  : {i : Size} → Exp {i} → Exp {↑ i}
  elim : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {↑ i}
  seq  : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {↑ i}

data Wne : {i : Size} → Set where
  nvar  : {i : Size} → Var → Wne {i}
  na_∘_ : {i : Size} → Wne {i} → Exp {i} → Wne {↑ i}
  nelim : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Wne {i} → Wne {↑ i}
  nJ    : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Exp {i} → Wne {i} → Wne {↑ i}

data Whnf : {i : Size} → Set where
  nType : {i : Size} → ℕ → Whnf {i}
  nΠ    : {i : Size} → Exp {i} → Exp {i} → Whnf {↑ i}
  nId   : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Whnf {↑ i}
  n∥_∥   : {i : Size} → Exp {i} → Whnf {↑ i}
  ne    : {i : Size} → Wne {i} → Whnf {↑ i}
  nλ    : {i : Size} → Exp {i} → Whnf {↑ i}
  nrefl : {i : Size} → Exp {i} → Whnf {↑ i}
  n[_]  : {i : Size} → Exp {i} → Whnf {↑ i}
  nseq  : {i : Size} → Exp {i} → Exp {i} → Exp {i} → Whnf {↑ i}

data _⊢_∷_ : Ctx → Exp → Exp → Set where
  triv : ∀ Γ t T → Γ ⊢ t ∷ T

postulate ↓_ : {i : Size} → Exp {i} → Whnf {i}

injne_ : Wne → Exp
injne nvar x = var x
injne (na n ∘ t) = (injne n) ∘ t
injne nelim T U t u n = elim T U t u (injne n)
injne nJ T U b u v n = J T U b u v (injne n)

inj_ : Whnf → Exp
inj nType i = Type i
inj nΠ A B = Π A B
inj nId T u v = Id T u v
inj n∥ T ∥ = ∥ T ∥
inj ne x = injne x
inj nλ t = lλ t
inj nrefl t = refl t
inj n[ t ] = [ t ]
inj nseq T u v = seq T u v

data _⊢_≡_∷_ : Ctx → Exp → Exp → Exp → Set where
  eq : ∀ e Γ t u T → Γ ⊢ e ∷ Id T t u → Γ ⊢ t ≡ u ∷ T

data Σ {X : Set} (A : X → Set) : Set where
  _&&_ : (x₀ : X) → A x₀ → Σ \(x : X) → A x

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

data ⊥ : Set where

-- Note: We need the recursive call in the Pi case to get validity of function
-- type injectivity.

-- Now termination checking fails because it doesn't know anything about ↓

mutual
  _⊢_⋈̂_∷_ : Ctx → Exp → Exp → Exp → Set
  _⊢_⋈_∷_  : Ctx → Whnf → Whnf → Whnf → Set

  Γ ⊢ t₁ ⋈̂ t₂ ∷ T = Γ ⊢ ↓ t₁ ⋈ ↓ t₂ ∷ (↓ T)

  Γ ⊢ nType j   ⋈ nType k      ∷ nType i = Γ ⊢ Type j   ≡ Type k      ∷ Type i
  Γ ⊢ nΠ A B    ⋈ nΠ A' B'     ∷ nType i = Σ λ j → Σ λ k → (Γ ⊢ {!   !} ⋈̂ {!   !} ∷ {!   !}) × {!   !}
  Γ ⊢ nId T u v ⋈ nId T' u' v' ∷ nType i = Γ ⊢ Id T u v ≡ Id T' u' v' ∷ Type i
  Γ ⊢ n∥ T ∥     ⋈ n∥ T' ∥       ∷ nType i = Γ ⊢ ∥ T ∥     ≡ ∥ T' ∥      ∷ Type i
  Γ ⊢ ne N      ⋈ ne N'        ∷ nType i = Γ ⊢ injne N    ≡ injne N'      ∷ Type i
  Γ ⊢ A         ⋈ A'           ∷ nType i = ⊥
  Γ ⊢ a₁        ⋈ a₂           ∷ A       = Γ ⊢ (inj a₁)   ≡ (inj a₂)      ∷ (inj A)
