{-# OPTIONS --without-K #-}

open import HoTT
open import homotopy.Freudenthal

module homotopy.IterSuspensionStable where

{- π (S k) (Ptd-Susp^ (S n) X) == π k (Ptd-Susp^ n X), where k = S k'
   Susp^Stable below assumes k ≠ O instead of taking k' as the argument -}
module Susp^StableSucc {i} (X : Ptd i) (cX : is-connected 0 (fst X))
  (n : ℕ) (k' : ℕ) (kle : S k' ≤ n *2) where

  {- need k,n ≥ 1 -}
  k : ℕ
  k = S k'

  {- some numeric computations -}
  private
    kle' : ⟨ k ⟩ ≤T ⟨ n ⟩₋₁ +2+ ⟨ n ⟩₋₁
    kle' = ≤T-trans (⟨⟩-monotone-≤ kle) (inl (lemma n))
      where lemma : (n : ℕ) → ⟨ n *2 ⟩ == ⟨ n ⟩₋₁ +2+ ⟨ n ⟩₋₁
            lemma O = idp
            lemma (S n') = ap S (ap S (lemma n')
                                 ∙ ! (+2+-βr ⟨ S n' ⟩₋₂ ⟨ S n' ⟩₋₂))

  private
    module F = FreudenthalIso
      ⟨ n ⟩₋₂ k (ℕ-S≠O _) kle' (⊙Susp^ n X)
      (transport (λ t → is-connected t (fst (⊙Susp^ n X)))
                 (+2+0 ⟨ n ⟩₋₂) (⊙Susp^-conn n cX))

  stable : (tk : k ≠ 0) (tsk : S k ≠ 0)
    → π (S k) tsk (⊙Susp^ (S n) X) == π k tk (⊙Susp^ n X)
  stable tk tsk =
    π (S k) tsk (⊙Susp^ (S n) X)
      =⟨ π-inner-iso k tk tsk (⊙Susp^ (S n) X) ⟩
    π k tk (⊙Ω (⊙Susp^ (S n) X))
      =⟨ ! (π-Trunc-shift-iso k tk (⊙Ω (⊙Susp^ (S n) X))) ⟩
    Ω^-Group k tk (⊙Trunc ⟨ k ⟩ (⊙Ω (⊙Susp^ (S n) X))) Trunc-level
      =⟨ ! (group-ua F.iso) ⟩
    Ω^-Group k tk (⊙Trunc ⟨ k ⟩ (⊙Susp^ n X)) Trunc-level
      =⟨ π-Trunc-shift-iso k tk (⊙Susp^ n X) ⟩
    π k tk (⊙Susp^ n X) ∎

{- π (S k) (⊙Susp^ (S n) X) == π k (⊙Susp^ n X), where k > 0 -}
module Susp^Stable {i} (X : Ptd i) (cX : is-connected 0 (fst X))
  (n : ℕ) (k : ℕ) (tk : k ≠ O) (tsk : S k ≠ O) (kle : k ≤ n *2) where

  private
    lemma : ∀ {i} (C : (n : ℕ) → n ≠ 0 → S n ≠ O → Type i)
      → ((n : ℕ) (tsn : S n ≠ 0) (tssn : S (S n) ≠ 0)
            → C (S n) tsn tssn)
      → ((n : ℕ) (tn : n ≠ 0) (tsn : S n ≠ 0)
            → C n tn tsn)
    lemma C f O tn _ = ⊥-rec (tn idp)
    lemma C f (S n) tsn tssn = f n tsn tssn

  abstract
    stable : π (S k) tsk (⊙Susp^ (S n) X) == π k tk (⊙Susp^ n X)
    stable = lemma
      (λ r tr tsr → (r ≤ n *2) →
         π (S r) tsr (⊙Susp^ (S n) X) == π r tr (⊙Susp^ n X))
      (λ r' tsr' tssr' → λ rle →
        Susp^StableSucc.stable X cX n r' rle tsr' tssr')
      k tk tsk kle
