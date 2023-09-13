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
+-rearrange m n p q = begin
    (m + n) + (p + q) ≡⟨ sym (+-assoc (m + n) p q) ⟩
    ((m + n) + p) + q ≡⟨ cong (_+ q) (+-assoc m n p) ⟩
    (m + (n + p)) + q ≡⟨⟩
    m + (n + p) + q   ∎

+-swap : ∀ (m n p : ℕ) -> m + (n + p) ≡ n + (m + p)
+-swap m n p = begin
    m + (n + p) ≡⟨ sym (+-assoc m n p) ⟩
    (m + n) + p ≡⟨ cong (_+ p) (+-comm m n) ⟩
    (n + m) + p ≡⟨ +-assoc n m p ⟩
    n + (m + p) ∎

*-nullaryˡ : ∀ (n : ℕ) -> 0 * n ≡ 0
*-nullaryˡ n = refl

*-nullaryʳ : ∀ (n : ℕ) -> n * 0 ≡ 0
*-nullaryʳ 0       = refl
*-nullaryʳ (suc n) = *-nullaryʳ n

*-neuturalˡ : ∀ (n : ℕ) -> 1 * n ≡ n
*-neuturalˡ n = begin
    1 * n       ≡⟨⟩
    n + (0 * n) ≡⟨⟩
    n + 0       ≡⟨ +-neturalʳ n ⟩
    n           ∎

*-neutralʳ : ∀ (n : ℕ) -> n * 1 ≡ n
*-neutralʳ 0       = refl
*-neutralʳ (suc n) = begin
    suc n * 1 ≡⟨ cong suc (*-neutralʳ n) ⟩
    suc n     ∎

*-suc : ∀ m n → m * suc n ≡ m + m * n
*-suc zero    n = refl
*-suc (suc m) n = begin
  suc m * suc n         ≡⟨⟩
  suc n + m * suc n     ≡⟨ cong (suc n +_) (*-suc m n) ⟩
  suc n + (m + m * n)   ≡⟨⟩
  suc (n + (m + m * n)) ≡⟨ cong suc (sym (+-assoc n m (m * n))) ⟩
  suc (n + m + m * n)   ≡⟨ cong (λ x → suc (x + m * n)) (+-comm n m) ⟩
  suc (m + n + m * n)   ≡⟨ cong suc (+-assoc m n (m * n)) ⟩
  suc (m + (n + m * n)) ≡⟨⟩
  suc m + suc m * n     ∎

*-distrib-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distrib-+ = ?
