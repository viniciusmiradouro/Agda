module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-neturalˡ : ∀ (n : ℕ) -> (0 + n) ≡ n
+-neturalˡ 0       = refl
+-neturalˡ (suc n) = cong suc (+-neturalˡ n)

+-neturalʳ : ∀ (n : ℕ) -> (n + 0) ≡ n
+-neturalʳ 0       = refl
+-neturalʳ (suc n) = cong suc (+-neturalʳ n)

+-suc : ∀ (m n : ℕ) -> m + (suc n) ≡ suc (m + n)
+-suc 0       _ = refl
+-suc (suc n) m = cong suc (+-suc n m)

+-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
+-comm m 0       = +-neturalʳ m
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-suc m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assoc : ∀ (m n o : ℕ) -> (m + n) + o ≡ m + (n + o)
+-assoc 0       n o = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q
  ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q
  ≡⟨⟩
    m + (n + p) + q
  ∎
