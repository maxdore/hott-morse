{-# OPTIONS --without-K --rewriting --termination-depth=2 #-}

open import HoTT
open import cw.CW
open import cw.examples.Sphere

module cw.examples.Torus where

⊤-has-dec-eq : has-dec-eq ⊤
⊤-has-dec-eq unit unit = inl idp

⊤-is-set : is-set ⊤
⊤-is-set = dec-eq-is-set ⊤-has-dec-eq


cw-torus-skel : Skeleton {lzero} (S (S 0))

CWTorus : Type₀
CWTorus = ⟦ cw-torus-skel ⟧

α₁ : Bool → S⁰ → ⊤
α₁ _ _ = unit

X₁ = attached-skeleton (⊤ , ⊤-is-set) (Bool , Bool-is-set) α₁

α₂ : ⊤ → S¹ → (Attached α₁)
α₂ unit = Pushout-rec ψ ψ (cst idp)
    where
    ψ : ⊤ → Attached α₁
    ψ unit = PushoutGeneric.from-cc (inl unit)

X₂ = attached-skeleton X₁ (⊤ , ⊤-is-set) α₂

cw-torus-skel = X₂


