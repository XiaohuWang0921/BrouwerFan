{-# OPTIONS --without-K --safe --guardedness #-}

module Fan where

open import Data.List as List
open import Data.List.Properties as Listᵖ
open import Data.Vec as Vec
open import Data.Vec.Properties as Vecᵖ
open import Codata.Guarded.Stream as Stream
open import Codata.Guarded.Stream.Properties as Streamᵖ
open import Relation.Unary
open import Relation.Binary using (Rel)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Lex
open import Data.Bool as Bool
open import Data.Bool.Properties as Boolᵖ
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕᵖ
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product
open import Data.Sum as Sum
open import Level

pattern 0b = false
pattern 1b = true

-- Finite binary sequences
FBS : Set
FBS = List Bool

-- Empty sequence
ϕ : FBS
ϕ = []

-- Infinite binary sequences
IBS : Set
IBS = Stream Bool

-- Length
∣_∣ : FBS → ℕ
∣_∣ = List.length

-- Correspond to the N set and the E set
-- TODO: rewrite using original def?
N : FBS → Set
N [] = ⊥
N (0b ∷ []) = ⊤
N (0b ∷ u) = N u
N (1b ∷ _) = ⊥

E : FBS → Set
E [] = ⊥
E (0b ∷ _) = ⊥
E (1b ∷ []) = ⊤
E (1b ∷ u) = E u

-- Restrictions

resFBS : ∀ (w : FBS) n → n ℕ.≤ ∣ w ∣ → FBS
resFBS _ zero _ = []
resFBS (x ∷ w) (suc n) le = x ∷ resFBS w n (≤-pred le)

resIBS : IBS → ℕ → FBS
resIBS α zero = []
resIBS α (suc n) = Stream.head α ∷ resIBS (Stream.tail α) n

-- Lexicographical ordering

_≺_ : Rel FBS 0ℓ
u ≺ v = ∣ u ∣ ≡ ∣ v ∣ × Lex-< _≡_ Bool._<_ u v

-- Set of finite binary sequences

SFBS : ∀ ℓ → Set (Level.suc ℓ)
SFBS ℓ = FBS → Set ℓ

-- Implicit variables

private
  variable
    ℓ ℓ' : Level

-- Operations on such sets (interior, closure and derivative)

_° : SFBS ℓ → SFBS ℓ
A ° = λ u → ∀ w → u List.++ w ∈ A
