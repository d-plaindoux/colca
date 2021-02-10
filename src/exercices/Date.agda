--
-- Inspired by a blog post written by Arnaud Bailly
-- https://abailly.github.io/posts/dependently-typed-date.html
--

{-# OPTIONS --without-K #-}

module Date where

open import Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<_; _≤_; z≤n; s≤s; _≤?_; _<?_)
open import Data.Nat.DivMod using (_%_)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Maybe using (Maybe; just; nothing)

open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (True; toWitness)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎; step-≡)

module Day where
    data t : Set where
        Day : (n : ℕ) → {True (1 ≤? n)} → t   -- Capture a day which should not be zero

    make : (n : ℕ) → {True (1 ≤? n)} → t
    make = Day

    value : t → ℕ
    value (Day n) = n

module Year where
    t : Set
    t = ℕ

    isLeap : t → Bool
    isLeap y = (check4 ∧ not check100) ∨ check400
        where check4   = y % 4   ≡ᵇ 0
              check100 = y % 100 ≡ᵇ 0
              check400 = y % 400 ≡ᵇ 0

module Month where
    data t : Set where
        January    : t
        February   : t
        March      : t
        April      : t
        May        : t
        June       : t
        July       : t
        August     : t
        September  : t
        October    : t
        November   : t
        December   : t

    toNat : t → ℕ
    toNat January    = 1
    toNat February   = 2
    toNat March      = 3
    toNat April      = 4
    toNat May        = 5
    toNat June       = 6
    toNat July       = 7
    toNat August     = 8
    toNat September  = 9
    toNat October    = 10
    toNat November   = 11
    toNat December   = 12

    next : t → t
    next January   = February
    next February  = March
    next March     = April
    next April     = May
    next May       = June
    next June      = July
    next July      = August
    next August    = September
    next September = October
    next October   = November
    next November  = December
    next December  = January
    
    duration : t → Year.t → Day.t
    duration January _   = Day.make 31
    duration February year with Year.isLeap year
    ... | true           = Day.make 29
    ... | false          = Day.make 28
    duration March _     = Day.make 31
    duration April _     = Day.make 30
    duration May _       = Day.make 31
    duration June _      = Day.make 30
    duration July _      = Day.make 31
    duration August _    = Day.make 31
    duration September _ = Day.make 30
    duration October _   = Day.make 31
    duration November _  = Day.make 30
    duration December _  = Day.make 31

{-
module Date where
    data t : Set where
       Valid   : (year : Year.t) → (month : Month.t) → (day : ℕ)
               → {≤max : True (day ≤? Day.value (Month.duration month year))}
               → {min≤ : True (1 ≤? day)}
                --------------------------------------------------------------
               → t

    make = Valid

    changeMonth : (year : Year.t) → (month : Month.t) -> t
    changeMonth year Month.December = make (suc year) Month.January 1
    changeMonth year month          = make year (Month.next month) 1

    addOneDay : t → t
    addOneDay (Valid year month day) with (suc day) ≤? Day.value (Month.duration month year)
    ... | yes proof = Valid year month (suc day) {proof} {s≤s z≤n}
    ... | no  _     = changeMonth year month
    addOneDay d     = d
-}

module Date where
    data t : Set where
       Valid   : (year : Year.t) → (month : Month.t) → (day : ℕ)
               → {≤max : day ≤ Day.value (Month.duration month year)}
               → {min≤ : 1 ≤ day}
                --------------------------------------------------------------
               → t
       Invalid : t

    1≤month : ∀ {month year} -> 1 ≤ Day.value (Month.duration month year)
    1≤month {Month.January} {year} =
        begin
           1 ≤ Day.value (Month.duration month year)

{-
    make : (year : Year.t) → (month : Month.t) → (day : ℕ) → t
    make year month day with day ≤? Day.value (Month.duration month year) | 1 ≤? day
    ... | yes p1 | yes p2 = Valid year month day {p1} {p2}
    ... | _      | _      = Invalid

    changeMonth : (year : Year.t) → (month : Month.t) -> t
    changeMonth year Month.December = Valid (suc year) Month.January 1 {1≤month} {s≤s z≤n}
    changeMonth year month          = Valid year (Month.next month) 1 {1≤month} {s≤s z≤n}

    addOneDay : t → t
    addOneDay (Valid year month day) with (suc day) ≤? Day.value (Month.duration month year)
    ... | yes proof = Valid year month (suc day) {proof} {s≤s z≤n}
    ... | no  _     = changeMonth year month
    addOneDay d     = d

    -- addDays : t → ℕ → t
-}