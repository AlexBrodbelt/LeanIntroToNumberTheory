import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Basic

open Nat

open Finset

open BigOperators

variable {a b x q n : ℕ}

theorem question_1 (hn : 2 ≤ n)(hx : 1 ≤ x) : x^n - 1 = (x - 1) * (∑ k in range n , x^k) := by
  induction' n, hn using Nat.le_induction with n _hn ih
  · simp
    rw [Nat.mul_sub_right_distrib, mul_comm 1]
    nth_rewrite 1 [add_mul]
    rw [← tsub_tsub, ← Nat.mul_sub_left_distrib, Nat.add_sub_assoc, Nat.sub_self, add_zero, sq, one_mul]
    apply le_refl
  have h₁ : 1 ≤ 1 := by exact le_refl 1
  have h₂ : 1 ≤ x^n := by apply one_le_pow; linarith [hx]
  rw [← succ_eq_add_one]
  calc
    x^(succ n) - 1 = (x^n*x - x^n*1) + (x^n - 1) := by
      rw [Nat.pow_succ]
      nth_rewrite 2 [← add_zero x]
      rw [← Nat.sub_self 1, ← Nat.add_sub_assoc h₁, Nat.mul_sub_left_distrib, tsub_tsub, Nat.mul_add, mul_one, ← tsub_add_tsub_comm]
      · nth_rewrite 1 [← mul_one (x^n)]; apply mul_le_mul; repeat' linarith
      · apply h₂
    _ = (x - 1) * x^n + (x - 1) * (∑ k in range n , x^k) := by
      rw [ih, ← Nat.mul_sub_left_distrib, Nat.mul_comm]
    _ = (x - 1) * ((∑ k in range n , x^k) + x^n) := by rw [← Nat.mul_add, Nat.add_comm]
    _ = (x - 1) * (∑ k in range (succ n) , x^k) := by rw [Finset.sum_range_succ]

lemma finsum_eq_n (n : ℕ): n = ∑ k in range n, 1 := by
  induction' n with n ih
  · rfl
  · rw [succ_eq_add_one, Finset.sum_range_succ, ← ih]


theorem question_2 (hn : 2 ≤ n)(hd : 2 ≤ d)(hprime: Nat.Prime (d^n - 1) ) : 2 = d := by
  by_contra h
  have h₁ : 1 ≤ d := by linarith
  rw [question_1 hn h₁] at hprime
  -- We now show 1 < d - 1 and 1 < ∑ k in range n, d^k, which would show we have found both factors are neither 1 nor d^n - 1
  have h₂ : 1 < d - 1 := by
    apply lt_sub_of_add_lt
    apply lt_iff_le_and_ne.mpr
    constructor
    · apply hd
    · rw [ne_eq]
      apply h
  have h₃ : 1 < ∑ k in range n, d^k := by
    apply lt_trans (b := n)
    · linarith
    · nth_rewrite 1 [finsum_eq_n (n)]
      apply Finset.sum_lt_sum
      · intro i _h'
        apply one_le_pow
        linarith
      · use 1
        constructor
        · rw [mem_range]
          linarith
        · linarith
  have hnotprime : ¬ Nat.Prime ((d - 1) * ∑ k in range n, d ^ k) := by
    apply not_prime_mul
    · exact h₂
    · exact h₃
  absurd hnotprime hprime
  trivial

theorem question_3 {a b : ℕ} (a1 : 1 < a) (b1 : 1 < b)(neqamulb : n = a * b) : ¬ (Nat.Prime (2^n - 1)) := by
  intro hprime
  rw [neqamulb, pow_mul', question_1] at hprime
  have h₀ : 1 < (2 ^ b - 1) := by
    apply lt_sub_of_add_lt
    rw [one_add_one_eq_two, ← pow_one 2]
    apply pow_lt_pow_right _ b1
    linarith
  have h₁ : 1 < ∑ k in range a, (2 ^ b) ^ k := by
    apply lt_trans (b := a)
    · linarith
    · nth_rewrite 1 [finsum_eq_n (a)]
      apply Finset.sum_lt_sum
      · intro i _h'
        apply one_le_pow
        apply Nat.pos_pow_of_pos
        linarith
      · use 1
        constructor
        · rw [mem_range]
          linarith
        · rw [pow_one, ← Nat.pow_zero 2]
          apply pow_lt_pow_right
          repeat linarith
  · apply not_prime_mul h₀ h₁ hprime
  · linarith
  · apply one_le_pow; linarith


theorem question_4 (hn: 2 ≤ n): Nat.Prime (2^n - 1) → Nat.Prime n := by
  contrapose
  intro nnotprime
  rcases exists_dvd_of_not_prime2 hn nnotprime with ⟨a, advdn, ha, altn⟩
  rcases advdn with ⟨b, neqamulb⟩
  have b1 : 1 < b := by
    rw [neqamulb] at altn
    nth_rewrite 1 [ ← mul_one a] at altn
    apply lt_of_mul_lt_mul_left' altn
  have a1 : 1 < a := by linarith
  apply question_3 a1 b1 neqamulb

lemma computation_helper (hx : 1 ≤ x): x + (1 + (x ^ 2 - x)) = 1 + x^2 := by
  have h₁ : x ≤ x^2 := by
    rw [sq]
    nth_rewrite 1 [← one_mul x]
    apply Nat.mul_le_mul_right
    exact hx
  have h₂ : x ≤ x := by apply le_refl
  rw [← add_assoc, add_comm x 1, add_assoc, ← Nat.add_sub_assoc h₁, add_comm x (x^2), Nat.add_sub_assoc h₂, Nat.sub_self, add_zero]

theorem question_5 (nodd : Odd n)(hx : 1 ≤ x)(hn : 2 ≤ n) : x^n + 1 = (x + 1) * (1 + ∑ k in range ((n - 1) / 2), x^(k + 1) * (x - 1)  ) := by
  rcases nodd with ⟨w, hn'⟩
  rw [hn']
  have hw : 1 ≤ w := by
    rw [hn'] at hn
    linarith
  -- ask on zulip the difference on modifying the induction and clearing hypotheses
  clear hn'
  clear hn
  -- Simplify (2 * w + 1 - 1) / 2 to be w
  rw [Nat.add_sub_assoc, Nat.sub_self, add_zero]
  nth_rewrite 2 [mul_comm 2 w]
  rw [Nat.mul_div_cancel]
  repeat' linarith
  induction' w, hw using Nat.le_induction with w _hw ih
  · simp
    rw [
      ← succ_eq_add_one 2, add_comm, Nat.mul_sub_left_distrib, ← sq, mul_one,
      add_mul, one_mul, mul_add, Nat.mul_sub_left_distrib, add_assoc,
      ← sq, ← Nat.pow_succ', add_comm (x^(succ 2) - x^2), mul_one, ← add_assoc,
      computation_helper, ← Nat.add_sub_assoc, add_assoc, add_comm (x^2), ← add_assoc,
      Nat.add_sub_assoc, Nat.sub_self, add_zero
      ]
    · exact le_refl (x^2)
    · apply pow_le_pow_right hx
      linarith
    · exact hx
  · rw [mul_add 2, mul_one]
    rw [Finset.sum_range_succ, ← add_assoc 1, add_comm _ (x ^ (w + 1) * (x - 1)), mul_add (x + 1), ← ih]
    sorry




theorem question_6 (hprime : Nat.Prime (2^n + 1))(nodd: Odd n): n = 1 := by sorry

theorem question_7 (hprime : Nat.Prime (2^n + 1))(qodd: Odd q) : ¬ (q ∣ n) := by sorry

theorem question_8 (hprime : Nat.Prime (2^n + 1)) : ∃ m : ℕ, n = 2^m := by sorry
