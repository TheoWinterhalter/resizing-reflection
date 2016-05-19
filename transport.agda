{-# OPTIONS --type-in-type #-}

-- open import Agda.Primitive

data Id {A : Set} : A → A → Set where
  Refl : ∀ {x : A} → Id x x

J : (A : Set) (C : (x y : A) → Id x y → Set)
        -> ((x : A) -> C x x Refl)
        -> (M N : A) (P : Id M N) -> C M N P
J A C b M .M Refl = b M

-- transport : ∀ (A A' : Set₀) (x y : A) (p : Id A A') (e : Id {_} {A} x y) → Id {_} {A'} x y
-- transport = ?

transport : ∀ (A A' : Set) (x : A) (p : Id A A') → A'
transport = λ A A' x p → J Set (λ T T' eq → T → T') (λ T → λ x → x) A A' p x
