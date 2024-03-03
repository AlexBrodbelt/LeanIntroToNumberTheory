import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Algebra.Group.Basic


open Nat

open Finset

open BigOperators

variable {a b x q n : ℕ}

lemma difference_of_squares : x^2 - 1 = (x - 1)*(x + 1) := by
  rw [Nat.mul_sub_right_distrib, mul_comm 1]
  nth_rewrite 1 [add_mul]
  rw [← tsub_tsub, ← Nat.mul_sub_left_distrib, Nat.add_sub_assoc, Nat.sub_self, add_zero, sq, one_mul]
  apply le_refl

theorem question_1 (hn : 2 ≤ n)(hx : 1 ≤ x) : x^n - 1 = (x - 1) * (∑ k in range n , x^k) := by
  induction' n, hn using Nat.le_induction with n _hn ih
  · simp; rw [difference_of_squares]
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

lemma computation_helper_q5 (hx : 1 ≤ x): x + (1 + (x ^ 2 - x)) = 1 + x^2 := by
  have h₁ : x ≤ x^2 := by
    rw [sq]
    nth_rewrite 1 [← one_mul x]
    apply Nat.mul_le_mul_right
    exact hx
  have h₂ : x ≤ x := by apply le_refl
  rw [← add_assoc, add_comm x 1, add_assoc, ← Nat.add_sub_assoc h₁, add_comm x (x^2), Nat.add_sub_assoc h₂, Nat.sub_self, add_zero]

theorem question_5 (nodd : Odd n)(hx : 1 ≤ x)(hn : 2 ≤ n) : x^n + 1 = (x + 1) * (1 + ∑ k in range ((n - 1) / 2), x^(2*k + 1) * (x - 1)  ) := by
  rcases nodd with ⟨w, hn'⟩
  rw [hn']
  have hx' : 1 ≤ x^2 := by
    rw [← one_mul 1, sq]
    apply mul_le_mul'
    repeat' exact hx
  have hw : 1 ≤ w := by
    rw [hn'] at hn
    linarith
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
      computation_helper_q5, ← Nat.add_sub_assoc, add_assoc, add_comm (x^2), ← add_assoc,
      Nat.add_sub_assoc, Nat.sub_self, add_zero
      ]
    · exact le_refl (x^2)
    · apply pow_le_pow_right hx
      linarith
    · exact hx
    -- Modify LHS
  · rw [mul_add 2, mul_one]
    -- Modify RHS
    rw [
      Finset.sum_range_succ, ← add_assoc 1, mul_add (x + 1), ← ih,
      mul_comm (x + 1), mul_assoc, ← difference_of_squares, add_assoc _ 1, add_comm 1,
      ← add_assoc]
    nth_rewrite 1 [← mul_one (x^(2*w + 1))]
    rw [
      ← mul_add, ← Nat.add_sub_assoc, add_comm 1, Nat.add_sub_assoc, Nat.sub_self,
      add_zero,← pow_add, add_assoc (2*w) 1 2 ,add_comm 1 2, ← add_assoc
      ]
    · linarith
    · exact hx'


lemma computation_helper_q6 : 2*w + 1 = 1 ↔ w = 0 := by
  constructor
  · intro h
    nth_rewrite 2 [← zero_add 1] at h
    have h₁ : 2*w  = 0 := by rw [add_right_cancel h]
    cases Nat.mul_eq_zero.mp h₁
    case inl h' => contradiction
    case inr h' => exact h'
  · intro h
    rw [h, mul_zero, zero_add]


theorem question_6 (hprime : Nat.Prime (2^n + 1))(nodd: Odd n): n = 1 := by
  by_contra h
  rcases nodd with ⟨w, hn'⟩
  have hw' : 0 < w := by
    rw [hn', computation_helper_q6, ← ne_eq, ← zero_lt_iff] at h
    exact h
  have hn : 2 ≤ n := by
    rw [hn']
    nth_rewrite 1 [← one_add_one_eq_two]
    apply add_le_add_right
    apply one_le_mul
    repeat' linarith
  have hnotprime : ¬ (Nat.Prime (2^n + 1)) := by
    rw [question_5 ⟨w, hn'⟩ _  hn]
    apply not_prime_mul
    · linarith
    · nth_rewrite 1 [← add_zero 1]
      apply add_lt_add_of_le_of_lt
      apply le_refl
      rw [hn']; simp
      apply Finset.sum_pos'
      · intro _i _imem
        apply le_trans (b := 1)
        · linarith
        · apply one_le_pow
          linarith
      · use 0
        constructor
        · simp; exact hw'
        · apply pow_pos; linarith
    · linarith
  contradiction


theorem question_7 (hn : 2 ≤ n)(hq: 2 ≤ q)(hprime : Nat.Prime (2^n + 1))(qodd: Odd q) : ¬ (q ∣ n) := by
  by_contra h
  rcases h with ⟨w, hn'⟩
  rcases qodd with ⟨m, hq'⟩
  have h₀ : w ≠ 0 := by
    apply Nat.ne_zero_of_mul_ne_zero_right (n := q)
    rw [← zero_lt_iff]
    linarith
  have h₁ : 1 ≤ 2^w := by apply one_le_pow; linarith
  have h₂ : 1 ≤ m := by
    rw [hq'] at hq
    linarith [hq]
  have h₃ : 1 < (2 ^ w + 1) := by
      nth_rewrite 1 [← zero_add 1]
      apply add_lt_add_right
      apply pow_pos; linarith
  have h₄ : 1 < 1 + ∑ k in range ((q - 1) / 2), (2 ^ w) ^ (2*k + 1) * (2 ^ w - 1) := by
      nth_rewrite 1 [← add_zero 1]
      apply add_lt_add_left
      rw [hq']; simp
      apply Finset.sum_pos'
      · intro i _hi
        rw [mul_comm, mul_nonneg_iff_of_pos_right]
        · apply le_sub_of_add_le
          apply one_le_pow; linarith
        · apply pow_pos
          apply pow_pos
          linarith
      · use 0
        constructor
        · simp
          exact h₂
        · apply mul_pos
          · apply pow_pos
            apply pow_pos
            linarith
          · apply lt_sub_of_add_lt
            apply Nat.one_lt_pow
            · exact h₀
            · linarith
  have hnotprime : ¬ (Nat.Prime (2^n + 1)) := by
    rw [hn', pow_mul', question_5 ⟨m, hq'⟩ h₁ hq]
    apply not_prime_mul h₃ h₄
  absurd hnotprime hprime
  trivial

theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  cases m; contradiction
  case succ m =>
    cases m; contradiction
    repeat' apply Nat.succ_le_succ
    apply Nat.zero_le

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  . rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn

lemma exists_odd_factor_or_is_power_of_two (hn : 2 ≤ n): (∃ q, Odd q ∧ q ∣ n) ∨ (∃ m, n = 2^m) := by
  have nnezero: n ≠ 0 := by linarith
  have ngt1 : 1 < n := by linarith
  by_cases h : ∃ p ∈ Nat.primeFactors n, Odd p
  · left
    rcases h with ⟨q, qprimefac , qodd⟩
    rw [Nat.mem_primeFactors] at qprimefac
    rcases qprimefac with ⟨qprime, qdvdn, neqzero⟩
    exact ⟨q, qodd, qdvdn⟩
  · right
    push_neg at h
    simp only [← Nat.even_iff_not_odd] at h
    have h' : ∀ p ∈ n.primeFactors, p = 2 := by
      intro p hp
      have evenp : Even p := h _ hp
      rw [mem_primeFactors] at hp
      rw [← Nat.Prime.even_iff hp.1]
      exact evenp

    have factorseq2 : {2} = n.primeFactors := by
      ext r; constructor
      · intro hr; rw [mem_singleton] at hr
        rcases nonempty_primeFactors.mpr ngt1 with ⟨p, hp⟩
        rw [hr, ← h' p hp]
        exact hp
      · intro hr
        rw [mem_singleton]
        exact h' _ hr
    -- apply factorization_prod_pow_eq_self
    rcases n.factorization with ⟨prime_factors, multiplicity, h'⟩
    use multiplicity 2
    rw [← factorization_prod_pow_eq_self nnezero]
    -- rw [Finsupp.onFinset_prod]
    sorry

    -- Nat.mem_primeFactors_of_ne_zero nnezero
    -- []
    -- rcases exists_prime_factor hn with ⟨q, hq⟩
    -- have : Even q := by apply h _ hq

theorem question_8 (hn : 2 ≤ n)(hprime : Nat.Prime (2^n + 1)) : ∃ m : ℕ, n = 2^m := by
  cases exists_odd_factor_or_is_power_of_two hn
  case inl h => sorry
    -- rcases h with ⟨q, qodd, qdvdn⟩
    -- have pnotprime : ¬ (Nat.Prime 2^n + 1) := by
  case inr h => exact h
