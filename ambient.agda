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
  ν_∙_   : Id → Process → Process                 -- Restriction
  Stop   : Process                                -- Inactivity
  _||_   : Process → Process → Process            -- Composition
  !_     : Process -> Process                     -- Replication
  _[_]   : Capability → Process → Process         -- Ambient
  _∙_    : Capability → Process → Process         -- Action
  Fun_∙_ : Id -> Process → Process                -- Input Action
  <_>    : Capability → Process                   -- Message

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
  Red_In    : ∀ {m n P Q R} →
              ` m [ In n ∙ P || Q ] || ` n [ R ]
              =>
              ` n [ ` m [ P || Q ] || R ]

  Red_Out   : ∀ {m n P Q R} →
              ` m [ ` n [ Out m ∙ P || R ] || Q ]
              =>
             ` m [ Q ] || ` n [ P || R ]

  Red_Open  : ∀ {m P Q} →
              ` m [ P ] || Open m ∙ Q
              =>
              P || Q

  Red_I/O   : ∀ {M x P} →
              < M > || Fun x ∙ P
              =>
              P [ x / M ]

--- Congruence
