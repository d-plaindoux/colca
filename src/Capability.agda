module Capability where

open import Relation.Nullary
     using (yes; no)

open import Data.List
     using (List; []; [_]; _∷_; _++_)

open import Data.String
     using (String; _≟_)

open import Relation.Binary.PropositionalEquality
     using (_≢_; refl; _≡_)

-- Local modules ---------------------------------------------------------------

open import Common
     using (Id)

-- Capabilities Definition -----------------------------------------------------

infix  50 `_
infixr 15 _∙_

data Capability : Set where
  `_   : Id → Capability                          -- Name
  In   : Id → Capability                          -- Can enter
  Out  : Id → Capability                          -- Can exit
  Open : Id → Capability                          -- Can open
  ε    : Capability                               -- Null
  _∙_  : Capability → Capability → Capability     -- Path

-- Free variable ---------------------------------------------------------------

freeVar : Capability -> List Id
freeVar (` a)    = [ a ]
freeVar (a ∙ b)  = (freeVar a) ++ (freeVar b)
freeVar _        = []

-- Capability substitution -----------------------------------------------------

_[_/_] : Capability -> Id -> Capability -> Capability

` x [ y / M ] with x ≟ y
... | yes _       = M
... | no _        = ` x
(N ∙ R) [ y / M ] = N [ y / M ] ∙ R [ y / M ]
C [ _ / _ ]       = C

module Test where
  a = "a"
  b = "b"

  ------------------------------------------------------------------------------

  _ : freeVar (` a) ≡ [ a ]
  _ = refl

  _ : freeVar (` a ∙ ` b) ≡ a ∷ b ∷ []
  _ = refl

  ------------------------------------------------------------------------------

  _ : ∀ {M} → ` a [ a / M ] ≡ M
  _ = refl

  _ : ∀ {M} → ` b [ a / M ] ≡ ` b
  _ = refl

