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
+-comm m (suc n) = begin
    m + suc n   ≡⟨ +-suc m n ⟩
    suc (m + n) ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m) ≡⟨⟩
    suc n + m   ∎

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

postulate
  *-suc : ∀ m n → m * suc n ≡ m + m * n

*-comm : ∀ (m n : ℕ) -> (m * n) ≡ (n * m)
*-comm 0 n = sym (*-nullaryʳ n)
*-comm (suc m) n = begin
  suc m * n   ≡⟨⟩
  n + (m * n) ≡⟨ cong (n +_) (*-comm m n) ⟩
  n + (n * m) ≡⟨ sym (*-suc n m) ⟩
  n * suc m   ∎

*-distribʳ-+ : ∀ (m n p : ℕ) -> (m + n) * p ≡ m * p + n * p
*-distribʳ-+ 0 _ _        = refl
*-distribʳ-+ (suc m) n p  = begin
  (suc m + n) * p         ≡⟨⟩
  suc (m + n) * p         ≡⟨⟩
  p + ((m + n) * p)       ≡⟨ cong (p +_) (*-distribʳ-+ m n p) ⟩
  p + (m * p + n * p)     ≡⟨ sym (+-assoc p (m * p) (n * p)) ⟩
  (p + m * p) + (n * p)   ≡⟨⟩
  (suc m * p) + (n * p)   ∎

*-distribˡ-+ : ∀ (m n o : ℕ) -> m * (n + o) ≡ m * n + m * o
*-distribˡ-+ m n o = begin
  m * (n + o)   ≡⟨ *-comm m (n + o) ⟩
  (n + o) * m   ≡⟨ *-distribʳ-+ n o m ⟩
  n * m + o * m ≡⟨ cong (_+ (o * m)) (*-comm n m) ⟩
  m * n + o * m ≡⟨ cong ((m * n) +_) (*-comm o m) ⟩
  m * n + m * o ∎

*-assoc : ∀ (m n p : ℕ) -> (m * n) * p ≡ m * (n * p)
*-assoc 0       _ _ = refl
*-assoc (suc m) n p = begin
  (suc m * n) * p       ≡⟨⟩
  (n + m * n) * p       ≡⟨ *-distribʳ-+ n (m * n) p ⟩
  n * p + (m * n) * p   ≡⟨ cong ((n * p) +_) (*-assoc m n p) ⟩
  n * p + m * (n * p)   ≡⟨⟩
  suc m * (n * p)       ∎

data _≤_ : ℕ -> ℕ -> Set where
  0≤n   : ∀ {n : ℕ} -> 0 ≤ n
  sm≤sn : ∀ {m n : ℕ} -> m ≤ n -> suc m ≤ suc n

infix 4 _≤_

inv-m≤n : ∀ {m n : ℕ} -> suc m ≤ suc n -> m ≤ n
inv-m≤n (sm≤sn m≤n) = m≤n

≤-refl : ∀ {n : ℕ} -> n ≤ n
≤-refl {0}     = 0≤n
≤-refl {suc n} = sm≤sn ≤-refl

≤-trans : ∀ {m n o : ℕ} -> m ≤ n -> n ≤ o -> m ≤ o
≤-trans 0≤n         _           = 0≤n
≤-trans (sm≤sn m≤n) (sm≤sn n≤o) = sm≤sn (≤-trans m≤n n≤o)
