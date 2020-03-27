{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT renaming (pt to pt⊙)
open import homotopy.DisjointlyPointedSet
open import lib.types.Nat
open import lib.types.Vec

module simplicial.SCequivCW where

open import cw.CW public
open import cw.examples.Sphere public
open import simplicial.Base


SC-to-CW : {dim : ℕ} → SC (S dim) → Skeleton {lzero} dim
SC-to-CW {dim} sc = SC-to-CW' dim dim ltS sc
  where
  SC-to-CW' : (n : ℕ) → (predim : ℕ) → (p : n < (S predim)) → SC (S predim) → Skeleton {lzero} n
  SC-to-CW' 0 predim _ (complex ss _) = (Fin (length (lookup ss (0 , O<S predim)))) , Fin-is-set
  SC-to-CW' (S n) predim p (complex ss c) =
      attached-skeleton
          (SC-to-CW' n predim (<-cancel-S-left p) (complex ss c))
          ((Fin (length (lookup ss (n , <-cancel-S-left p)))) , Fin-is-set)
          λ cells sph → {!!}


