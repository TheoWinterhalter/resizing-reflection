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

_* : ∀ {A A' : Set} (p : Id A A') → A → A'
_* {A} {A'} p x = transport A A' x p

ap : ∀ {A} {B} (f : A → B) {u u' : A} → (Id u u') → Id (f u) (f u')
ap {A} {B} f {u} {u'} p = J A (λ x y p → Id (f x) (f y)) (λ x → Refl) u u' p

sym : ∀ A (x y : A) → Id x y → Id y x
sym A x y p = J A (λ u v e → Id v u) (λ u → Refl) x y p

_⁻¹ : ∀ {A} {x y : A} → Id x y → Id y x
_⁻¹ {A} {x} {y} p = sym A x y p

trans : ∀ A (x y z : A) → Id x y → Id y z → Id x z
trans A x y z p = J A (λ x₁ y₁ e → Id y₁ z → Id x₁ z) (λ x₁ e → e) x y p

_·_ : ∀ {A} {x y z : A} → Id x y → Id y z → Id x z
_·_ {A} {x} {y} {z} p q = trans A x y z p q


-- When A = A' and B = B' then (x : A) → B = (x : A') → B'
-- We first need to transport along the domain
transdom : ∀ {A} {A'} (p : Id A A') (B' : A' → Set) → (A → Set)
transdom p B' a = B' ((p *) a)

Π : ∀ (A : Set) (B : A → Set) → Set
Π A B = ∀ (x : A) → B x

-- transfun : ∀ A A' (B : A → Set) (B' : A' → Set) →
--           (p : Id A A') → Id B (transdom p B') → Id (Π A B) (Π A' B')
-- transfun A' .A' _ B' Refl Refl = Refl

transfun : ∀ A A' (B : A → Set) (B' : A' → Set) →
          (p : Id A A') → Id B (transdom p B') → Id (Π A B) (Π A' B')
transfun A A' B B' p q = J Set (λ x y e → ∀ (X : x → Set) (Y : y → Set) → Id X (transdom e Y) → Id (Π x X) (Π y Y)) (λ x X Y e → J (x → Set) (λ u v f → Id (Π x u) (Π x v)) (λ u → Refl) X Y e) A A' p B B' q

-- transid : ∀ T T' (u v : T) (u' v' : T') (p : Id T T') →
--           Id u (((p ⁻¹) *) u') → Id v (((p ⁻¹) *) v') →
--           Id (Id u v) (Id u' v')
-- transid T T' u v u' v' p q r = J Set {! λ T T' p → ∀ (u v : T) (u' v' : T') → Id (Id u v) (Id u' v')  !} {!   !} {!   !} {!   !} {!   !}

app : ∀ A (B : A → Set) (f f' : Π A B) (u u' : A) →
      (p : Id f f') → (q : Id u u') →
      Id (f u) (((ap B (q ⁻¹)) *) (f' u'))
app A B f f' u u' p q = ap (λ g → g u) p · J A (λ x y e → Id (f' x) (((ap B (e ⁻¹)) *) (f' y))) (λ x → Refl) u u' q
