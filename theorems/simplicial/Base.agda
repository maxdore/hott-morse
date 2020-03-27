{-# OPTIONS --without-K --rewriting --allow-unsolved-metas #-}

open import HoTT renaming (pt to pt⊙)
open import homotopy.DisjointlyPointedSet
open import lib.types.Nat
open import lib.types.Vec

module simplicial.Base where

-- HELPERS
combinations : ℕ → List ℕ -> List (List ℕ)
combinations 0 _ = nil :: nil
combinations _ nil = nil
combinations (S n) (x :: xs) = (map (λ ys → x :: ys) (combinations (n) xs)) ++ (combinations (S n) xs)

standardSimplex : ℕ → List ℕ
standardSimplex O = nil
standardSimplex (S x) = (S x) :: (standardSimplex x)

-- UGLY HELPER FUNCTIONS -- TO BE REPLACED WITH STANDARD FUNCTIONS LATER ON
bfilter : {A : Type₀} → ((a : A) → Bool) → List A → List A
bfilter f nil = nil
bfilter f (a :: l) with f a
... | inl _ = a :: (bfilter f l)
... | inr _ = bfilter f l

ℕin : ℕ → List ℕ → Bool
ℕin x nil = inr unit
ℕin x (y :: ys) with ℕ-has-dec-eq x y
... | inl x₁ = inl unit
... | inr x₁ = inr unit

_lsubset_ : List ℕ → List ℕ → Bool
nil lsubset ys = inl unit
(x :: xs) lsubset ys with ℕin x ys
... | inl _ = xs lsubset ys
... | inr _ = inr unit



-- TYPES FOR SIMPLICES
-- 'Simplices' saves a collection of simplices, grouped by their dimension.
-- Note that we do not specify the dimensions of individual simplices, since
-- otherwise we could not simply save all simplices in a single vector
Simplex = List ℕ
Simplices : ℕ → Type₀
Simplices dim = (Vec (List Simplex) dim)

is-closed : {dim : ℕ} → (Simplices dim) → Type₀

record SC (dim : ℕ) : Type₀ where
  constructor complex
  field
    simplices : Simplices dim
    closed : is-closed simplices

simplices : {dim : ℕ} → SC dim → Simplices dim
simplices (complex simplices _) = simplices

faces : Simplex → List Simplex
faces s = concat (map (λ l → combinations l s) (standardSimplex (ℕ-pred (length s))))

-- removes grouping of simplices by dimension and puts all simplices in single list
compress : {dim : ℕ} → Simplices dim → List Simplex
compress {dim} []         = nil
compress {dim} (xs ∷ xss) = xs ++ compress xss

bodies : {dim : ℕ} → (SC dim) → Simplex → List Simplex
bodies (complex ss _) s = bfilter (λ o → (s lsubset o)) (compress ss)

-- inverse of compress function
unfold : {dim : ℕ}  → List Simplex → Simplices dim
unfold {dim} ss = unfold' {dim} ss (emptyss dim)
  where
  emptyss : (dim : ℕ) → Simplices dim
  emptyss 0 = []
  emptyss (S n) = nil ∷ (emptyss n)
  unfold' : {dim : ℕ}  → List Simplex → Simplices dim → Simplices dim
  unfold' {dim} nil sc = sc
  unfold' {dim} (x :: ss) sc = insert (faces x) sc
      where
      insert : {dim : ℕ} → List Simplex → Simplices dim → Simplices dim
      insert nil sc = sc
      insert (s :: ss) sc = insertS s sc
          where
          insertS : {dim : ℕ} → Simplex → Simplices dim → Simplices dim
          insertS s sc = updateAt ((length s) , {!!}) (λ l → s :: l) sc


is-closed {dim} ss = All (λ s → All (λ f → f ∈ ssc) (faces s)) ssc
  where ssc = compress ss

-- takes facet description of SC and generates their face closure
SCgenerator : (dim : ℕ) → List Simplex → SC dim
SC.simplices (SCgenerator dim ss) = unfold $ concat(concat (map(λ simplex → map (λ l → combinations l simplex) (standardSimplex (length simplex))) ss))
SC.closed (SCgenerator dim ss) = {!!}


-- EXAMPLES

sc-unit : SC 2
SC.simplices sc-unit = ((1 :: nil) :: (2 :: nil) :: nil) ∷ ((1 :: 2 :: nil) :: nil) ∷ []
SC.closed sc-unit = nil :: (nil :: (((here idp) :: ((there (here idp)) :: nil)) :: nil))

sc-circle : SC 2
SC.simplices sc-circle =
  ((1 :: nil) :: (2 :: nil) :: (3 :: nil) :: nil) ∷
  ((1 :: 2 :: nil) :: (1 :: 3 :: nil) :: (2 :: 3 :: nil) :: nil) ∷ []
SC.closed sc-circle = nil :: (nil :: (nil :: (((here idp) :: ((there (here idp)) :: nil)) :: (((here idp) :: ((there (there (here idp))) :: nil)) :: ((there (here idp) :: (there (there (here idp)) :: nil)) :: nil)))))


-- sc-circle-equiv-cw-circle : CWSphere 1 ≃ CWSphere 1
-- sc-circle-equiv-cw-circle = {!!}

sc-sphere : SC 3
sc-sphere = SCgenerator 3 ((1 :: 2 :: 3 :: nil) :: (1 :: 3 :: 4 :: nil) :: (2 :: 3 :: 4 :: nil) :: (1 :: 3 :: 4 :: nil) :: nil)

sc-unit-gen : SC 2
sc-unit-gen = SCgenerator 2 ((1 :: 2 :: nil) :: nil)

-- sc-unit≃sc-unit-gen : sc-unit ≃ sc-unit-gen
-- sc-unit≃sc-unit-gen = ?

