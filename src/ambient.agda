module Ambient where

open import Relation.Nullary
     using (yes; no)

open import Data.String
     using (String; _≟_)

open import Data.Bool
     using (Bool; true; false)

open import Relation.Binary.PropositionalEquality
     using (_≢_; refl)
     renaming (_≡_ to _≡≡_)

open import Data.List
     using (List; []; _∷_; _++_; filter)

-- Local modules ---------------------------------------------------------------

open import Common
     using (Id)

open import Capability
     using (Capability; `_; In; Out; Open; ε; _∙_)
     renaming (_[_/_] to _[_:=_]; fv to fv-capa)

-- Process Definition ----------------------------------------------------------

infix  40 _[_/_]
infixr 30 Fun_∙_
infix  20 _[_]
infixr 10 _||_

data Process : Set where
  ν_∙_   : Id → Process → Process                 -- Restriction
  Zero   : Process                                -- Inactivity
  _||_   : Process → Process → Process            -- Composition
  !_     : Process → Process                      -- Replication
  _[_]   : Capability → Process → Process         -- Ambient
  _∙_    : Capability → Process → Process         -- Action
  Fun_∙_ : Id → Process → Process                 -- Input Action
  <_>    : Capability → Process                   -- Message

-- Free variable ---------------------------------------------------------------

_-_ : List Id → Id → List Id
[] - _      = []
(x ∷ xs) - y with x ≟ y
... | yes _ = xs - y
... | no _  = x ∷ (xs - y)

fv : Process → List Id
fv (ν x ∙ P)   = fv P
fv Zero        = []
fv (P || Q)    = (fv P) ++ (fv Q)
fv (! P)       = fv P
fv (M [ P ])   = (fv-capa M) ++ (fv P)
fv (M ∙ P)     = (fv-capa M) ++ (fv P)
fv (Fun x ∙ P) = (fv P) - x
fv (< M >)     = fv-capa M

_∉_ : Id → List Id → Set
y ∉ l = member y l ≡≡ false
    where member : Id → List Id →  Bool -- Should propably use the List filter instead!
          member y []     = false
          member y (x ∷ xs) with x ≟ y
          ... | yes _ = true
          ... | no _  = member y xs

-- Process substitution --------------------------------------------------------

_[_/_] : Process → Id → Capability → Process

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

module Test where
  a = "a"
  b = "b"

  _ : (` a [ < ` b > ]) [ b / Open a ] ≡≡ ` a [ < Open a > ]
  _ = refl

  _ : (< ` a > || < ` b >) [ b / Open a ] ≡≡ < ` a > || < Open a >
  _ = refl

-- Congruence ------------------------------------------------------------------

infix 5 _≡_

data _≡_ : Process → Process → Set where
  Struct-Refl    : ∀ {P}
                   -----
                 → P ≡ P

  Struct-Symm    : ∀ {P Q}
                 → P ≡ Q
                   -----
                 → Q ≡ P

  Struct-Trans   : ∀ {P Q R}
                 → P ≡ Q → Q ≡ R
                   -------------
                 → P ≡ R

  Struct-Res     : ∀ {n P Q}
                 → P ≡ Q
                   -----------------
                 → ν n ∙ P ≡ ν n ∙ Q

  Struct-Par     : ∀ {P Q R}
                 → P ≡ Q
                   ---------------
                 → P || R ≡ Q || R

  Struct-Repl    : ∀ {P Q}
                 → P ≡ Q
                   ---------
                 → ! P ≡ ! Q

  Struct-Amb     : ∀ {M P Q}
                 → P ≡ Q
                   -----------------
                 → M [ P ] ≡ M [ Q ]

  Struct-Action  : ∀ {M P Q}
                 → P ≡ Q
                   -------------
                 → M ∙ P ≡ M ∙ Q

  Struct-Input   : ∀ {x P Q}
                 → P ≡ Q
                   ---------------------
                 → Fun x ∙ P ≡ Fun x ∙ Q

  Struct-Comm    : ∀ {P Q}
                 → P ≡ Q
                   -----
                 → Q ≡ P

  Struct-Assoc   : ∀ {P Q R}
                   -----------------------------
                 → (P || Q) || R ≡ P || (Q || R)

  Struct-ResRes  : ∀ {n m P}
                 → n ≢ m
                   -----------------------------
                 → ν n ∙ ν m ∙ P ≡ ν m ∙ ν n ∙ P

  Struct-ResPar  : ∀ {n P Q}
                 → n ∉ fv(P)
                   -----------------------------
                 → ν n ∙ (P || Q) ≡ P || ν n ∙ Q

  Struct-ResAmb  : ∀ {n m P}
                 → n ≢ m
                   -----------------------------------
                 → ν n ∙ (` m [ P ]) ≡ ` m [ ν n ∙ P ]

  Struct-ZeroPar : ∀ {P}
                   -------------
                 → P || Zero ≡ P

  Struct-ZeroRes : ∀ {n}
                   -----------------
                 → ν n ∙ Zero ≡ Zero

  Struct-ZeroRep : ! Zero ≡ Zero

  Struct-ε       : ---------------
                   ε ∙ Zero ≡ Zero

  Struct-∙       : ∀ {M M' P}
                   ---------------------------
                 → (M ∙ M') ∙ P ≡ M ∙ (M' ∙ P)

-- Reduction rules -------------------------------------------------------------

infix 5 _~>_

data _~>_ : Process → Process → Set where
  Red-In    : ∀ {m n P Q R}
              -----------------------------------------------------------------
            → ` m [ In n ∙ P || Q ] || ` n [ R ] ~> ` n [ ` m [ P || Q ] || R ]

  Red-Out   : ∀ {m n P Q R}
              ------------------------------------------------------------------
            → ` m [ ` n [ Out m ∙ P || R ] || Q ] ~> ` m [ Q ] || ` n [ P || R ]

  Red-Open  : ∀ {m P Q}
              ---------------------------------
            → ` m [ P ] || Open m ∙ Q ~> P || Q

  Red-I/O   : ∀ {M x P}
              ---------------------------------
            → < M > || Fun x ∙ P ~> P [ x / M ]

  Red-Par   : ∀ {P Q R}
            → P ~> Q
              ------------------
            → P || R ~> Q || R

  Red-Res   : ∀ {n P Q}
            → P ~> Q
              --------------------
            → ν n ∙ P ~> ν n ∙ Q

  Red-Amb   : ∀ {M P Q}
            → P ~> Q
              --------------------
            → M [ P ] ~> M [ Q ]

  Red-≡     : ∀ {P P' Q Q'}
            → P' ≡ P  → P ~> Q → Q ≡ Q'
              -------------------------
            → P' ~> Q'

--------------------------------------------------------------------------------
