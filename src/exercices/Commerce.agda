--
-- Created by Dependently-Typed Lambda Calculus on 2020-09-23
-- Commerce
-- Author: dplaindoux
--

{-# OPTIONS --without-K --safe #-}

module Commerce where

open import Relation.Nullary using (Reflects; Dec; yes; no)
open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; _+_; _≥?_; _≥_)
open import Agda.Builtin.Nat using (_-_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

module Customer where
    record Account : Set where
        field
            balance : ℕ

    account : ℕ -> Account
    account n = record { balance = n }

    _↑_ : Account → ℕ → Account
    c ↑ n = account (Account.balance c + n)

    _↓_ : Account → ℕ → Account
    c ↓ n = account (Account.balance c - n )

    infixl 50 _↑_
    infixl 50 _↓_

module Product where
    record Item : Set where
        field
            price : ℕ

    data Basket : Set where
        ∅      : Basket
        _then_ : Item → Basket → Basket

    total : Basket → ℕ
    total ∅ = 0
    total (a then b) = Item.price a + total b

module Payment where
    open Customer
    open Product

    pay : (c : Account) → (p : Basket) → {Account.balance c ≥ total p} → Account
    pay c p = c ↓ total p

    module Front where
        pay? : Account → Basket → Account
        pay? c p with Account.balance c ≥? total p
        ... | yes proof = pay c p {proof}
        ... | no  _     = c