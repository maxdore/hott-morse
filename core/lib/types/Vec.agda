{-# OPTIONS --without-K --rewriting #-}

open import lib.Basics
open import lib.types.Sigma
open import lib.types.Bool
open import lib.types.Nat
open import lib.types.Fin

module lib.types.Vec where

infixr 5 _∷_

data Vec {i} (A : Type i) : ℕ → Type i where
  []  : Vec A 0
  _∷_ : ∀ {n} (x : A) (xs : Vec A n) → Vec A (S n)

infix 4 _[_]=_

data _[_]=_ {i} {A : Type i} : ∀ {n} → Vec A n → ℕ → A → Type i where
  here  : ∀ {n}     {x}   {xs : Vec A n} → x ∷ xs [ 0 ]= x
  there : ∀ {n} {m} {x y} {xs : Vec A n}
          (xs[m]=x : xs [ m ]= x) → y ∷ xs [ S m ]= x

module _ {i} {A : Type i} where

  length : ∀ {n} → Vec A n → ℕ
  length {n = n} _ = n

  head : ∀ {n} → Vec A (S n) → A
  head (x ∷ xs) = x

  vtail : ∀ {n} → Vec A (S n) → Vec A n
  vtail (x ∷ xs) = xs

  lookup : ∀ {n} → Vec A n → Fin n → A
  lookup [] ()
  lookup (x ∷ xs) (O , _) = x
  lookup (x ∷ xs) (S n , p) = lookup xs (n , <-cancel-S p)

  updateAt : ∀ {n} → Fin n → (A → A) → Vec A n → Vec A n
  updateAt (_ , _) _ [] = []
  updateAt (O , _) f (x ∷ xs) = (f x) ∷ xs
  updateAt (S n , p) f (x ∷ xs) = x ∷ (updateAt (n , <-cancel-S p) f xs)
