module Ambient where

open import Relation.Nullary using (yes; no)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Basic sorts

Id : Set
Id = String

-- Capabilities & Processes

infix  50 `_
infix  40 _[_/_]
infix  30 Fun_∙_
infixr 20 _[_]
infixr 15 _∙_
infixr 10 _||_

data Capability : Set where
  `_   : Id → Capability
  In   : Id → Capability
  Out  : Id → Capability
  Open : Id → Capability

data Process : Set where
  Stop   : Process                                -- Inactivity
  _||_   : Process → Process → Process            -- Composition
  !_     : Process -> Process                     -- Repeat

  _[_]   : Capability → Process → Process                 -- Ambient
  ν_∙_   : Id → Process → Process                 -- Restriction
  _∙_    : Capability → Process → Process         -- Action

  <_>    : Capability → Process                   -- Message
  Fun_∙_ : Id -> Process → Process                -- Abstraction

-- Capability substitution

_[_:=_] : Capability -> Id -> Capability -> Capability

` x [ y := M ] with x ≟ y
... | yes _  = M
... | no _   = ` x
C [ _ := _ ] = C

-- Tests corner

_ : ` "a" [ "a" := Open "b" ] ≡ Open "b"
_ = refl

_ : ` "b" [ "a" := Open "b" ] ≡ ` "b"
_ = refl

-- Process substitution

_[_/_] : Process -> Id -> Capability -> Process

Stop [ _ / _ ]       = Stop
(P || Q) [ x / M ]   = P [ x / M ] || Q [ x / M ]
(! P) [ x / M ]      = ! (P [ x / M ])
(x [ P ]) [ y / M ]  = (x [ y := M ]) [ P [ y / M ] ]
(ν x ∙ P) [ y / M ] with x ≟ y
... | yes _          = ν x ∙ P
... | no _           = ν x ∙ (P [ y / M ])
< N > [ x / M ]      = < N [ x := M ] >
(Fun x ∙ P) [ y / M ] with x ≟ y
... | yes _          = Fun x ∙ P
... | no _           = Fun x ∙ (P [ y / M ])
( N ∙ P) [ x / M ]   = (N [ x := M ]) ∙ (P [ x / M ])

-- Operational semantic

infix 5 _=>_

data _=>_ : Process → Process → Set where
  RedIn    : ∀ {m n P Q R S} →
             ` m [ In n ∙ P || Q ] || ` n [ R ] || S
             =>
             ` n [ ` m [ P || Q ] || R ] || S

  RedOut   : ∀ {m n P Q R S} →
             ` m [ ` n [ Out m ∙ P || R ] || Q ] || S
             =>
            ` m [ Q ] || ` n [ P || R ] || S

  RedOpen  : ∀ {m P Q R} →
             ` m [ P ] || Open m ∙ Q || R
             =>
             P || Q || R

  RedApply : ∀ {M x P Q} →
             < M > || Fun x ∙ P || Q
             =>
             P [ x / M ] || Q

--- Congruence
