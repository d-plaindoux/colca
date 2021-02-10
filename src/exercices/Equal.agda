--
-- Created by Dependently-Typed Lambda Calculus on 2020-09-24
-- Equal
-- Author: dplaindoux
--

module Equal where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Bool using (Bool; true; false)

infix 30 _=?_

data Type : Set where
    nat  : Type

▲_ : Type → Set
▲ nat  = ℕ

_=?_ : { a : Type } → ▲ a → ▲ a → Bool

_=?_ {nat} zero zero       = true
_=?_ {nat} (suc m) (suc n) = m =? n
_=?_ {nat} _ _             = false

Nat :
  ∀self(P : Nat → Set) →
  ∀(zero : P(λz. λs. z)) →
  ∀(succ : ∀(n : Nat) → P (λz. λs. s n)) →
  P self
