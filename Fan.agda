{-# OPTIONS --without-K --safe --guardedness #-}

module Fan where

open import Data.List as List
open import Data.List.Properties as Listᵖ
open import Codata.Guarded.Stream as Stream
open import Codata.Guarded.Stream.Properties as Streamᵖ
open import Relation.Unary
open import Relation.Binary using (Rel; Trichotomous; Tri; tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality
open import Data.List.Relation.Binary.Lex.Strict
open import Data.List.Relation.Binary.Pointwise hiding (refl)
open import Data.Bool as Bool
open import Data.Bool.Properties as Boolᵖ
open import Data.Nat as ℕ
open import Data.Nat.Properties as ℕᵖ
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product as Product
open import Data.Product.Properties as Productᵖ
open import Data.Sum as Sum
open import Level
open import Function.Bundles
open import Relation.Nullary
open import Function.Base

open ≡-Reasoning

--------------------------------------------------------
-- Section 25.2 Basic concepts and notations

pattern 0b = false
pattern 1b = true
pattern ϕ = []

-- Finite binary sequences
FBS : Set
FBS = List Bool

-- Infinite binary sequences
IBS : Set
IBS = Stream Bool

-- Length
∣_∣ : FBS → ℕ
∣_∣ = length

-- Correspond to the N set and the E set
-- TODO: rewrite using original def?
N : FBS → Set
N ϕ = ⊥
N (0b ∷ u) = N u
N (1b ∷ _) = ⊥

E : FBS → Set
E ϕ = ⊥
E (0b ∷ _) = ⊥
E (1b ∷ u) = E u

-- Restrictions

resFBS : ∀ (w : FBS) n → .(n ℕ.≤ ∣ w ∣) → FBS
resFBS _ 0 _ = ϕ
resFBS (b ∷ w) (suc n) le = b ∷ resFBS w n (≤-pred le)

resIBS : IBS → ℕ → FBS
resIBS α 0 = ϕ
resIBS α (suc n) = Stream.head α ∷ resIBS (Stream.tail α) n

-- Lexicographical ordering

_≺_ : Rel FBS 0ℓ
u ≺ v = ∣ u ∣ ≡ ∣ v ∣ × Lex-< _≡_ Bool._<_ u v

_⊏_ : Rel FBS 0ℓ
u ⊏ v = ∣ u ∣ ℕ.< ∣ v ∣ ⊎ u ≺ v

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

ClRes A = ∀ u n .n≤∣u∣ → u ∈ A → resFBS u n n≤∣u∣ ∈ A

IsTree = Detachable ∩ ClRes

Infinite A = ∀ n → ∃[ u ] u ∈ A × ∣ u ∣ ≡ n

IsBar A = ∀ α → ∃[ n ] resIBS α n ∈ A

IsUniformBar A = ∃[ N ] ∀ α → ∃[ n ] n ℕ.≤ N × resIBS α n ∈ A

Convex A = ∀ u v w → u ∈ A → w ∈ A → u ≺ v → v ≺ w → v ∈ A

Coconvex A = Convex (∁ A)

-----------------------------------------------------------
-- Section 25.3 Weak König Lemma

WKL : (ℓ : Level) → Set (Level.suc ℓ)
WKL ℓ = (S : SFBS ℓ) → S ∈ IsTree ∩ Infinite → ∃[ α ] IsPath α S

decFixLen : {A : SFBS ℓ} → Detachable A → ∀ n → Dec (∃[ u ] u ∈ A × ∣ u ∣ ≡ n)
decFixLen dec 0 with dec ϕ
... | yes ϕ∈A = yes (ϕ , ϕ∈A , refl)
... | no ϕ∉A = no (λ where
  (ϕ , ϕ∈A , _) → ϕ∉A ϕ∈A)
decFixLen dec (suc n) with decFixLen (dec ∘ (0b ∷_)) n
... | yes (u , 0∷u∈A , ∣u∣≡n) = yes (0b ∷ u , 0∷u∈A , cong ℕ.suc ∣u∣≡n)
... | no ∄0b with decFixLen (dec ∘ (1b ∷_)) n
... | yes (u , 1∷u∈A , ∣u∣≡n) = yes (1b ∷ u , 1∷u∈A , cong ℕ.suc ∣u∣≡n)
... | no ∄1b = no (λ where
  (0b ∷ u , 0∷u∈A , ∣0∷u∣≡sn) → ∄0b (u , 0∷u∈A , suc-injective ∣0∷u∣≡sn)
  (1b ∷ u , 1∷u∈A , ∣1∷u∣≡sn) → ∄1b (u , 1∷u∈A , suc-injective ∣1∷u∣≡sn))

∣resFBS∣ : ∀ u n .n≤∣u∣ → ∣ resFBS u n n≤∣u∣ ∣ ≡ n
∣resFBS∣ _ 0 _ = refl
∣resFBS∣ (b ∷ u) (suc n) sn≤∣b∷u∣ = cong ℕ.suc (∣resFBS∣ u n (≤-pred sn≤∣b∷u∣))

∣resIBS∣ : ∀ α n → ∣ resIBS α n ∣ ≡ n
∣resIBS∣ α 0 = refl
∣resIBS∣ α (suc n) = cong ℕ.suc (∣resIBS∣ (Stream.tail α) n)

resFBS-++ : ∀ u v →
  resFBS (u List.++ v) ∣ u ∣
    (subst (∣ u ∣ ℕ.≤_) (sym (length-++ u)) (m≤m+n _ _)) ≡
  u
resFBS-++ ϕ _ = refl
resFBS-++ (b ∷ u) v = cong (b ∷_) (resFBS-++ u v)

resIBS-++ : ∀ u α → resIBS (u Stream.++ α) ∣ u ∣ ≡ u
resIBS-++ ϕ _ = refl
resIBS-++ (b ∷ u) α = cong (b ∷_) (resIBS-++ u α)

resFBS-idem : ∀ u n m .n≤∣u∣ .m≤∣res-n∣ →
  resFBS (resFBS u n n≤∣u∣) m m≤∣res-n∣ ≡
  resFBS u m (ℕᵖ.≤-trans (subst (m ℕ.≤_) (∣resFBS∣ u n n≤∣u∣) m≤∣res-n∣) n≤∣u∣)
resFBS-idem _ _ 0 _ _ = refl
resFBS-idem (b ∷ u) (suc n) (suc m) sn≤∣b∷u∣ sm≤∣res-sn∣ =
  cong (b ∷_) (resFBS-idem u n m (≤-pred sn≤∣b∷u∣) (≤-pred sm≤∣res-sn∣))

resIBS-idem : ∀ α n m .m≤∣res-n∣ →
  resFBS (resIBS α n) m m≤∣res-n∣ ≡ resIBS α m
resIBS-idem α _ 0 _ = refl
resIBS-idem α (suc n) (suc m) sm≤∣res-sn∣ =
  let b = Stream.head α
      β = Stream.tail α
  in cong (b ∷_) (resIBS-idem β n m (≤-pred sm≤∣res-sn∣))

lem25-1 : (S : SFBS ℓ) → IsTree S →
  Infinite S ⇔ ∀ α → IsLongestPath α S → IsPath α S
lem25-1 S (dec , clRes) = mk⇔ a→b b→a
  where
    a→b : Infinite S → ∀ α → IsLongestPath α S → IsPath α S
    a→b inf α lp n with inf n
    ... | u , u∈S , refl = lp u u∈S

    boundLen : ∀ n → ∄[ u ] u ∈ S × ∣ u ∣ ≡ n → ∀ u → u ∈ S → ∣ u ∣ ℕ.< n
    boundLen n ∄n u u∈S with ∣ u ∣ ℕ.<? n
    ... | yes ∣u∣<n = ∣u∣<n
    ... | no ∣u∣≮n = let ∣u∣≥n = ≮⇒≥ ∣u∣≮n in
      ⊥-elim (∄n (resFBS u n ∣u∣≥n , clRes u n ∣u∣≥n u∈S , ∣resFBS∣ u n ∣u∣≥n))
    
    maxLen : ∀ n →
      ∄[ u ] u ∈ S × ∣ u ∣ ≡ n →
      ∄[ u ] u ∈ S ⊎ ∃[ u ] u ∈ S × ∀ v → v ∈ S → ∣ v ∣ ℕ.≤ ∣ u ∣
    maxLen 0 ∄0 = inj₁ λ (u , u∈S) →
      ∄0 (resFBS u 0 z≤n , clRes u 0 z≤n u∈S , refl)
    maxLen (suc n) ∄sn with decFixLen dec n
    ... | yes (u , u∈S , ∣u∣≡n) = inj₂ (u , u∈S , λ v v∈S →
      subst (∣ v ∣ ℕ.≤_) (sym ∣u∣≡n) (≤-pred (boundLen (ℕ.suc n) ∄sn v v∈S)))
    ... | no ∄n = maxLen n ∄n

    LP : ∀ n → ∄[ u ] u ∈ S × ∣ u ∣ ≡ n → ∃[ α ] IsLongestPath α S
    LP n ∄n with maxLen n ∄n
    ... | inj₁ S≐∅ = repeat 0b , λ u u∈S → ⊥-elim (S≐∅ (u , u∈S))
    ... | inj₂ (u , u∈S , bound) =
      let α = u Stream.++ repeat 1b in α , λ v v∈S →
      let
        leq = bound v v∈S
        eq = begin
          resFBS u (∣ v ∣) leq ≡˘⟨
            cong {A = ∃[ w ] ∣ v ∣ ℕ.≤ ∣ w ∣} (λ (w , ∣v∣≤∣w∣) → resFBS w _ ∣v∣≤∣w∣)
              {x = resIBS α ∣ u ∣ , subst (∣ v ∣ ℕ.≤_) (sym (∣resIBS∣ α ∣ u ∣)) leq} {y = u , leq}
              (Σ-≡,≡→≡ ((resIBS-++ u (repeat 1b)) , ℕᵖ.≤-irrelevant _ _))
          ⟩ resFBS (resIBS α ∣ u ∣) (∣ v ∣)
            (subst (∣ v ∣ ℕ.≤_) (sym (∣resIBS∣ α ∣ u ∣)) leq) ≡⟨
            resIBS-idem α ∣ u ∣ ∣ v ∣ (subst (∣ v ∣ ℕ.≤_)
              (sym (∣resIBS∣ α ∣ u ∣)) leq)
          ⟩ resIBS α ∣ v ∣ ∎
      in subst S eq (clRes u ∣ v ∣ (bound v v∈S) u∈S)

    b→a : (∀ α → IsLongestPath α S → IsPath α S) → Infinite S
    b→a assm n with decFixLen dec n
    ... | yes ∃n = ∃n
    ... | no ∄n with LP n ∄n
    ... | (α , lp) = resIBS α n , assm α lp n , ∣resIBS∣ α n

LPL : (ℓ : Level) → Set (Level.suc ℓ)
LPL ℓ = (S : SFBS ℓ) → IsTree S → ∃[ α ] IsLongestPath α S

L[_] : SFBS ℓ → SFBS ℓ
L[ A ] = λ u → u ∈ A × (∀ w → u ⊏ w → w ∉ A) ⊎ ϕ ∉ A × u ≡ ϕ

_′ : SFBS ℓ → SFBS ℓ
A ′ = λ u → u ∈ A ⊎ ∃[ v ] ∃[ w ] v ∈ L[ A ] × w ∈ N × u ≡ v List.++ w

⊏-compare : Trichotomous _≡_ _⊏_
⊏-compare u v with ℕ.<-cmp ∣ u ∣ ∣ v ∣
... | tri< ∣u∣<∣v∣ ∣u∣≢∣v∣ ∣u∣≯∣v∣ =
      tri< (inj₁ ∣u∣<∣v∣) (λ u≡v → ∣u∣≢∣v∣ (cong ∣_∣ u≡v)) λ where
        (inj₁ ∣u∣>∣v∣) → ∣u∣≯∣v∣ ∣u∣>∣v∣
        (inj₂ (∣u∣≡∣v∣ , _)) → ∣u∣≢∣v∣ (sym ∣u∣≡∣v∣)
... | tri> ∣u∣≮∣v∣ ∣u∣≢∣v∣ ∣u∣>∣v∣ =
      flip (flip tri> λ u≡v → ∣u∣≢∣v∣ (cong ∣_∣ u≡v)) (inj₁ ∣u∣>∣v∣) λ where
        (inj₁ ∣u∣<∣v∣) → ∣u∣≮∣v∣ ∣u∣<∣v∣
        (inj₂ (∣u∣≡∣v∣ , _)) → ∣u∣≢∣v∣ ∣u∣≡∣v∣
... | tri≈ ∣u∣≮∣v∣ ∣u∣≡∣v∣ ∣u∣≯∣v∣ with <-compare sym Boolᵖ.<-cmp u v
... | tri< u<v u≢v u≯v =
      tri< (inj₂ (∣u∣≡∣v∣ , u<v)) (u≢v ∘ ≡⇒Pointwise-≡) λ where
        (inj₁ ∣u∣>∣v∣) → ∣u∣≯∣v∣ ∣u∣>∣v∣
        (inj₂ (_ , u>v)) → u≯v u>v
... | tri> u≮v u≢v u>v =
      flip (flip tri> (u≢v ∘ ≡⇒Pointwise-≡)) (inj₂ (sym ∣u∣≡∣v∣ , u>v)) λ where
        (inj₁ ∣u∣<∣v∣) → ∣u∣≮∣v∣ ∣u∣<∣v∣
        (inj₂ (_ , u<v)) → u≮v u<v
... | tri≈ u≮v u≡v u≯v =
      flip tri≈ (Pointwise-≡⇒≡ u≡v) (λ where
        (inj₁ ∣u∣<∣v∣) → ∣u∣≮∣v∣ ∣u∣<∣v∣
        (inj₂ (_ , u<v)) → u≮v u<v) λ where
        (inj₁ ∣u∣>∣v∣) → ∣u∣≯∣v∣ ∣u∣>∣v∣
        (inj₂ (_ , u>v)) → u≯v u>v
      
module Prop25-2 (S : SFBS ℓ) (t : IsTree S) where
  dec = t .proj₁
  clRes = t .proj₂

  a : S ⊆ S ′
  a = inj₁

  b : Infinite S → S ≐ S ′
  b inf = a , (λ where
    (inj₁ u∈S) → u∈S
    (inj₂ (v , _ , inj₁ (_ , v-max) , _ , _)) →
      let x , x∈S , ∣x∣≡s∣v∣ = inf (ℕ.suc ∣ v ∣)
      in ⊥-elim
         (v-max x (inj₁ (resp (∣ v ∣ ℕ.<_) (sym ∣x∣≡s∣v∣) (n<1+n _))) x∈S)
    (inj₂ (_ , _ , inj₂ (ϕ∉S , _) , _ , _)) →
      ⊥-elim (ϕ∉S (inf 0 |> λ where
        (ϕ , ϕ∈S , _) → ϕ∈S)))

  LS-unique : ∀ u v → u ∈ L[ S ] → v ∈ L[ S ] → u ≡ v
  LS-unique u v (inj₁ (u∈S , u-max)) (inj₁ (v∈S , v-max)) with ⊏-compare u v
  ... | tri< u⊏v _   _   = ⊥-elim (u-max v u⊏v v∈S)
  ... | tri> u⋢v u≢v u⊐v = ⊥-elim (v-max u u⊐v u∈S)
  ... | tri≈ _   u≡v _   = u≡v
  LS-unique u v (inj₁ (u∈S , _)) (inj₂ (ϕ∉S , _)) =
    ⊥-elim (ϕ∉S (clRes u 0 z≤n u∈S))
  LS-unique u v (inj₂ (ϕ∉S , _)) (inj₁ (v∈S , _)) =
    ⊥-elim (ϕ∉S (clRes v 0 z≤n v∈S))
  LS-unique .ϕ .ϕ (inj₂ (_ , refl)) (inj₂ (_ , refl)) = refl

  S′-sameLen : ∀ {u v} → u ∈ (S ′) → v ∈ (S ′) → ∣ u ∣ ≡ ∣ v ∣ → u ∈ S × v ∈ S
  S′-sameLen (inj₁ u∈S) (inj₁ v∈S) _ = u∈S , v∈S
  S′-sameLen (inj₁ u∈S) (inj₂ (w , [] , inj₁ (w∈S , _) , _ , refl)) ∣u∣≡∣w++ϕ∣
    rewrite ++-identityʳ w = u∈S , w∈S
  S′-sameLen {u} (inj₁ u∈S) (inj₂ (w , (_ ∷ _) , inj₁ (w∈S , w-max) , _ , refl)) ∣u∣≡∣w++0b∷x∣ =
    ⊥-elim (w-max u (inj₁ {!!}) u∈S)
  
  c : Convex S → Convex (S ′)
  c conv u v w u∈S′ w∈S′ u≺v v≺w = {!!}
