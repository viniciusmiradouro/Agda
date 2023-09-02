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

n+succm≡succ-m+n : ∀ (m n : ℕ) -> m + (suc n) ≡ suc (m + n)
n+succm≡succ-m+n 0 _ = refl
n+succm≡succ-m+n (suc n) m = cong suc (n+succm≡succ-m+n n m)

postulate
  +-lemma₂ : ∀ (m n : ℕ) -> m + (suc n) ≡ (suc m) + n

n+succm≡succn+m : ∀ (m n : ℕ) -> m + (suc n) ≡ (suc m) + n
n+succm≡succn+m zero zero = refl
n+succm≡succn+m zero (suc n) = ?
n+succm≡succn+m (suc m) n = ?

+-comm : ∀ (m n : ℕ) -> (m + n) ≡ (n + m)
+-comm m 0 = +-right-netural m
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
