module Naturals where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)

+-left-netural : ∀ (n : ℕ) -> (0 + n) ≡ n
+-left-netural _ = refl
+-left-netural (suc n) = cong suc (+-left-netural n)

+-right-netural : ∀ (n : ℕ) -> (n + 0) ≡ n
+-right-netural 0 = refl
+-right-netural (suc n) = cong suc (+-right-netural n)
postulate
  +-lemma₁ : ∀ (n : ℕ) -> (n + 0) ≡ n
  +-lemma₂ : ∀ (m n : ℕ) -> m + (suc n) ≡ (suc m) + n

+-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
+-comm m 0 = +-lemma₁ m
+-comm m (suc n) =
  begin
    m + suc n
  ≡⟨ +-lemma₂ m n ⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨⟩
    suc n + m
  ∎

+-assoc : ∀ (m n o : ℕ) -> (m + n) + o ≡ m + (n + o)
+-assoc 0 n o =
  begin
    (0 + n) + o
  ≡⟨⟩
    n + o
  ≡⟨⟩
    0 + (n + o)
  ∎
+-assoc (suc m) n o =
  begin
    (suc m + n) + o
  ≡⟨⟩
    suc (m + n) + o
  ≡⟨⟩
    suc ((m + n) + o)
  ≡⟨ cong suc (+-assoc m n o) ⟩
    suc (m + (n + o))
  ≡⟨⟩
    suc m + (n + o)
  ∎
