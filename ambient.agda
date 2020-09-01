module Ambient where

open import Relation.Nullary using (yes; no)
open import Data.String using (String; _≟_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

-- Basic sorts -----------------------------------------------------------------

Id : Set
Id = String

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

-- Capability substitution -----------------------------------------------------

_[_:=_] : Capability -> Id -> Capability -> Capability

` x [ y := M ] with x ≟ y
... | yes _        = M
... | no _         = ` x
(N ∙ R) [ y := M ] = N [ y := M ] ∙ R [ y := M ]
C [ _ := _ ]       = C

-- Tests corner

_ : ` "a" [ "a" := Open "b" ] ≡ Open "b"
_ = refl

_ : ` "b" [ "a" := Open "b" ] ≡ ` "b"
_ = refl

-- Process Definition ----------------------------------------------------------

infix  40 _[_/_]
infixr 30 Fun_∙_
infix  20 _[_]
infixr 10 _||_

data Process : Set where
  ν_∙_   : Id → Process → Process                 -- Restriction
  Zero   : Process                                -- Inactivity
  _||_   : Process → Process → Process            -- Composition
  !_     : Process -> Process                     -- Replication
  _[_]   : Capability → Process → Process         -- Ambient
  _∙_    : Capability → Process → Process         -- Action
  Fun_∙_ : Id -> Process → Process                -- Input Action
  <_>    : Capability → Process                   -- Message

-- Process substitution --------------------------------------------------------

_[_/_] : Process -> Id -> Capability -> Process

Zero [ _ / _ ]       = Zero
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

-- Tests corner

_ : (` "a" [ < ` "b" > ]) [ "b" / Open "a" ] ≡ ` "a" [ < Open "a" > ]
_ = refl

_ : (< ` "a" > || < ` "b" >) [ "b" / Open "a" ] ≡ < ` "a" > || < Open "a" >
_ = refl

-- Congruence ------------------------------------------------------------------

infix 5 _≡≡_

data _≡≡_ : Process → Process → Set where
  Struct_Refl    : ∀ {P} →
                   P ≡≡ P

  Struct_Symm    : ∀ {P Q} →
                   P ≡≡ Q → Q ≡≡ P

  Struct_Trans   : ∀ {P Q R} →
                   P ≡≡ Q → Q ≡≡ R → P ≡≡ R

  Struct_Res     : ∀ {n P Q} →
                   P ≡≡ Q → ν n ∙ P ≡≡ ν n ∙ Q

  Struct_Par     : ∀ {P Q R} →
                   P ≡≡ Q → P || R ≡≡ Q || R

  Struct_Repl    : ∀ {P Q} →
                   P ≡≡ Q → ! P ≡≡ ! Q

  Struct_Amb     : ∀ {M P Q} →
                   P ≡≡ Q → M [ P ] ≡≡ M [ Q ]

  Struct_Action  : ∀ {M P Q} →
                   P ≡≡ Q → M ∙ P ≡≡ M ∙ Q

  Struct_Input   : ∀ {x P Q} →
                   P ≡≡ Q → Fun x ∙ P ≡≡ Fun x ∙ Q

  Struct_Comm    : ∀ {P Q} →
                   P ≡≡ Q → Q ≡≡ P

  Struct_Assoc   : ∀ {P Q R} →
                   (P || Q) || R ≡≡ P || (Q || R)

  Struct_ResRes  : ∀ {n m P} →
                   n ≢ m -> ν n ∙ ν m ∙ P ≡≡ ν m ∙ ν n ∙ P

  -- Struct_ResPar : ∀ {n m P} → ??? -- Free variale computation missing

  Struct_ResAmb  : ∀ {n m P} →
                   n ≢ m -> ν n ∙ (` m [ P ]) ≡≡ ` m [ ν n ∙ P ]

  Struct_ZeroPar : ∀ {P} →
                   P || Zero ≡≡ P

  Struct_ZeroRes : ∀ {n} →
                   ν n ∙ Zero ≡≡ Zero

  Struct_ZeroRep : ! Zero ≡≡ Zero

  Struct_ε       : ε ∙ Zero ≡≡ Zero

  Struct_∙       : ∀ {M M' P} →
                   (M ∙ M') ∙ P ≡≡ M ∙ (M' ∙ P)

-- Reduction rules -------------------------------------------------------------

infix 5 _~>_

data _~>_ : Process → Process → Set where
  Red_In    : ∀ {m n P Q R} →
              ` m [ In n ∙ P || Q ] || ` n [ R ]
              ~>
              ` n [ ` m [ P || Q ] || R ]

  Red_Out   : ∀ {m n P Q R} →
              ` m [ ` n [ Out m ∙ P || R ] || Q ]
              ~>
             ` m [ Q ] || ` n [ P || R ]

  Red_Open  : ∀ {m P Q} →
              ` m [ P ] || Open m ∙ Q
              ~>
              P || Q

  Red_I/O   : ∀ {M x P} →
              < M > || Fun x ∙ P
              ~>
              P [ x / M ]

  Red_Par   : ∀ {P Q R} →
              P ~> Q
              →
              P || R ~> Q || R

  Red_Res   : ∀ {n P Q} →
              P ~> Q
              →
              ν n ∙ P ~> ν n ∙ Q

  Red_Amb  : ∀ {M P Q} →
              P ~> Q
              →
              M [ P ] ~> M [ Q ]

  Red_≡≡   : ∀ {P P' Q Q'} →
             P' ≡≡ P → P ~> Q → Q' ≡≡ Q
             →
             P' ~> Q'

--------------------------------------------------------------------------------
