module Stack where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎; step-≡)

module V1 where
    {-
    This first version introduces the Stack abstract data type.
    -}

    data Stack (A : Set) : Set where
        ∅    : Stack A
        _>>_ : A → Stack A → Stack A

    infixr 50 _>>_

    push : ∀ {A} → A → Stack A → Stack A
    push a s = a >> s

    peek : ∀ {A} → (S : Stack A) → A
    -- May be absurd can be used here but how?
    peek (a >> _) = a

    pop : ∀ {A} → (S : Stack A) → Stack A
    -- May be absurd can be used here but how?
    pop (a >> s) = s

    module Example where
        _ : Stack Bool
        _ = true >> false >> ∅

    module Laws where
        law1 : ∀ {A} (a : A) (s : Stack A) -> peek (push a s) ≡ a
        law1 a s =
            begin
               peek (push a s)
               ≡⟨⟩
               peek (a >> s)
               ≡⟨⟩
               a
            ∎

        law2 : ∀ {A} {a : A} {s : Stack A} → pop (push a s) ≡ s
        law2 = refl

module V2 where
    {-
    This second version introduces the expression as constraint in the type definition.
    This prevents incomplete pattern matching for peek and pop.

    For this purpose we first design empty? predicate and then we use it the type definition
    of peek and pop.
    -}

    data Stack (A : Set) : Set where
        ∅    : Stack A
        _>>_ : A → Stack A → Stack A

    infixr 50 _>>_

    empty? : ∀ {A} → Stack A → Bool
    empty? ∅ = true
    empty? _ = false

    push : ∀ {A} → A → Stack A → Stack A
    push a s = a >> s

    peek : ∀ {A} → (S : Stack A) -> {empty? S ≡ false} → A
    peek (a >> _) = a

    pop : ∀ {A} → (S : Stack A) -> {empty? S ≡ false} → Stack A
    pop (a >> s) = s

    module Example where
        _ : Stack Bool
        _ = pop (push true ∅) {refl}

    module Laws where
        law1 : ∀ {A} {a : A} {s : Stack A} → peek (push a s) {refl} ≡ a
        law1 = refl

        law2 : ∀ {A} {a : A} {s : Stack A} → pop (push a s) {refl} ≡ s
        law2 = refl

module V3 where
    {-
    In this third version we use an GADT for the Stack data representation.
    A Kind then is design on purpose and a phantom type is used for the
    association between the stack and the kind.
    -}

    data Kind : Set where
        Empty    : Kind
        NotEmpty : Kind

    data Stack (A : Set) : Kind → Set where
        ∅    : Stack A Empty
        _>>_ : ∀ {B} → A → Stack A B → Stack A NotEmpty

    infixr 50 _>>_

    push : ∀ {A B} → A → Stack A B → Stack A NotEmpty
    push a s = a >> s

    peek : ∀ {A} → Stack A NotEmpty → A
    peek (a >> _) = a

    {-
    B is in the ouput only! => No constraint with the input.
    Writing such pop function is impossible as is.

    pop : ∀ {A B} → Stack A NotEmpty → Stack A B
    pop (_ >> s) = s
    -}

    module Example where
        _ : Stack Bool NotEmpty
        _ = push true ∅

    module Laws where
        law1 : ∀ {A B} {a : A} {s : Stack A B} → peek (push a s) ≡ a
        law1 = refl

        -- law2 cannot be expressed ...

module V4 where
    {-
    In this fourth version we slightly review the NotEmpty construction.
    This opens the opportunity to express the pop function since a
    dependency can by modeled in the corresponding type definition.
    -}
    data Kind : Set where
        Empty    : Kind
        NotEmpty : Kind → Kind

    data Stack (A : Set) : Kind → Set where
        ∅  : Stack A Empty
        _>>_ : ∀ {B} → A → Stack A B → Stack A (NotEmpty B)

    infixr 50 _>>_

    push : ∀ {A B} → A → Stack A B → Stack A (NotEmpty B)
    push a s = a >> s

    peek : ∀ {A B} → Stack A (NotEmpty B) → A
    peek (a >> _) = a

    pop : ∀ {A B} → Stack A (NotEmpty B) → Stack A B
    pop (_ >> s) = s

    module Example where
        _ : Stack Bool (NotEmpty Empty)
        _ = push true ∅

    module Laws where
        law1 : ∀ {A B} {a : A} {s : Stack A B} → peek (push a s) ≡ a
        law1 = refl

        law2 : ∀ {A B} {a : A} {s : Stack A B} → pop (push a s) ≡ s
        law2 = refl

module V5 where
    {-
    In this last version we show that previous Kind definiton is isomorphic
    with the natural.
    -}

    data Stack (A : Set) : ℕ → Set where
        ∅  : Stack A 0
        _>>_ : ∀ {B} → A → Stack A B → Stack A (suc B)

    infixr 50 _>>_

    push : ∀ {A B} → A → Stack A B → Stack A (suc B)
    push a s = a >> s

    peek : ∀ {A B} → Stack A (suc B) → A
    peek (a >> _) = a

    pop : ∀ {A B} → Stack A (suc B) → Stack A B
    pop (_ >> s) = s

    module Example where
        _ : Stack Bool 1
        _ = push true ∅

    module Laws where
        law1 : ∀ {A B} {a : A} {s : Stack A B} → peek (push a s) ≡ a
        law1 = refl

        law2 : ∀ {A B} {a : A} {s : Stack A B} → pop (push a s) ≡ s
        law2 = refl
