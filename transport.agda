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

f_equal : ∀ A B (f : A → B) (u u' : A) → (Id u u') → Id (f u) (f u')
f_equal A B f u u' p = J A (λ x y p → Id (f x) (f y)) (λ x → Refl) u u' p

sym : ∀ A (x y : A) → Id x y → Id y x
sym A x y p = J A (λ u v e → Id v u) (λ u → Refl) x y p

trans : ∀ A (x y z : A) → Id x y → Id y z → Id x z
trans A x y z p = J A (λ x₁ y₁ e → Id y₁ z → Id x₁ z) (λ x₁ e → e) x y p
