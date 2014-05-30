module Sigma where

open import Data.Nat
open import Data.Bool
open import Data.String

data Σ (A : Set) (B : A → Set) : Set where
  _,_ : (a : A) → B a → Σ A B

fst : {A : Set} {B : A → Set} → Σ A B → A
fst (a , _) = a

snd : {A : Set} {B : A → Set} → (p : Σ A B) → B (fst p)
snd (_ , b) = b

pair : {A : Set} {B : A → Set} → (a : A) → (b : B a) → Σ A B
pair a b = a , b

type : Bool → Set
type b = if b then ℕ else String

x : Σ Bool type
x = true , 3

y : Σ Bool type
y = false , "hello"
