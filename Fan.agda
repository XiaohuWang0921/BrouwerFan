{-# OPTIONS --without-K --safe --guardedness #-}

module Fan where

open import Data.List as List
open import Data.List.Properties as Listᵖ
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
∣_∣ = length

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
SFBS ℓ = Pred FBS ℓ

-- Implicit variables

private
  variable
    ℓ ℓ' : Level

-- Operations on such sets (interior, closure and Brzozowski derivative)

_° : SFBS ℓ → SFBS ℓ
A ° = λ u → ∀ w → u List.++ w ∈ A

cl : SFBS ℓ → SFBS ℓ
cl A = λ v → ∃[ u ] ∃[ w ] v ≡ u List.++ w × u ∈ A

der : SFBS ℓ → FBS → SFBS ℓ
der A u = λ w → u List.++ w ∈ A

-- Paths

IsPath : IBS → SFBS ℓ → Set ℓ
IsPath α A = ∀ n → resIBS α n ∈ A

Has≤1Path : SFBS ℓ → Set ℓ
Has≤1Path A = ∀ α β → (∃[ n ] Stream.lookup α n ≢ Stream.lookup β n) →
                      ∃[ n ] (resIBS α n ∉ A ⊎ resIBS β n ∉ A)

IsLongestPath : IBS → SFBS ℓ → Set ℓ
IsLongestPath α A = ∀ u → u ∈ A → resIBS α ∣ u ∣ ∈ A

-- Trivial lemma: Every path is a longest path

pathIsLongestPath : ∀ α (A : SFBS ℓ) → IsPath α A → IsLongestPath α A
pathIsLongestPath α A isPath u _ = isPath _

-- Other properties of SFBS

Detachable ClEx ClRes IsTree Infinite IsBar IsUniformBar Convex Coconvex :
  SFBS ℓ → Set ℓ
IsCSet : SFBS ℓ → Set (Level.suc ℓ)

Detachable = Decidable

IsCSet A = ∃[ D ] Detachable D × A ≐ cl D

ClEx A = ∀ u w → u ∈ A → u List.++ w ∈ A

ClRes A = ∀ u w → u List.++ w ∈ A → u ∈ A

IsTree = Detachable ∩ ClRes

Infinite A = ∀ n → ∃[ u ] ∣ u ∣ ≡ n × u ∈ A

IsBar A = ∀ α → ∃[ n ] resIBS α n ∈ A

IsUniformBar A = ∃[ N ] ∀ α → ∃[ n ] n ℕ.≤ N × resIBS α n ∈ A

Convex A = ∀ u v w → u ∈ A → w ∈ A → u ≺ v → v ≺ w → v ∈ A

Coconvex A = Convex (∁ A)
