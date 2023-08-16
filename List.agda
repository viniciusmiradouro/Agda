open import Prelude
open import Data.Nat
open import Data.List

variable A : Set

l1 : List ℕ
l1 =  1 ∷ 2 ∷ 3 ∷ []

snoc : List A → A → List A
snoc [] a = a ∷ []
snoc (x ∷ xs) a = x ∷ (snoc xs a)

rev : List A → List A
rev [] = []
rev (x ∷ xs) = snoc (rev xs) x

rev∘rev≡id : ∀ (L : List A) → rev (rev L) ≡ L
rev∘rev≡id [] = refl
rev∘rev≡id (x ∷ xs) = ?
