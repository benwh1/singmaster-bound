module

public import Mathlib

@[expose] public section

/-!
# Lemma 2.2: Bernoulli polynomials

`P_{2j}(z) = (B_{2j+1}((z+1)/2) - B_{2j+1}((1-z)/2))/(2j+1)` (`powSumPoly`) is a polynomial in `z`.
At every integer `m ≥ 1` it equals the symmetric power sum `∑_{i<m} (i - (m-1)/2)^{2j}`
(`powSumPoly_eval_nat`, Lemma 2.2(a)). For `p ≤ π|y|` we have `|B_p(y)| ≤ 8 |y|^p`
(`bernC_eval_norm_le`, Lemma 2.2(b)), and consequently `|P_{2j}(z)|` is bounded like
`|z/2|^{2j+1}` as long as `2j + 1 ≲ |z|` (`powSumPoly_norm_le`).
-/

open Polynomial Real

namespace Singmaster

/-- The Bernoulli polynomial `B_p` over `ℂ`. -/
noncomputable def bernC (p : ℕ) : ℂ[X] := (Polynomial.bernoulli p).map (algebraMap ℚ ℂ)

/-- `P_{2j}(z) = (B_{2j+1}((z+1)/2) - B_{2j+1}((1-z)/2))/(2j+1)`. -/
noncomputable def powSumPoly (j : ℕ) : ℂ[X] :=
  C ((2 * (j : ℂ) + 1)⁻¹) * ((bernC (2 * j + 1)).comp (C (1 / 2 : ℂ) * (X + 1)) -
    (bernC (2 * j + 1)).comp (C (1 / 2 : ℂ) * (1 - X)))

/-! ### Helpers -/

lemma bern_bernoulli_abs_le (j : ℕ) : |((bernoulli j : ℚ) : ℝ)| ≤ 4 * (j.factorial : ℝ) / (2 * π) ^ j := by
  rcases Nat.even_or_odd j with ⟨k, hk⟩ | hodd
  · rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp at hk; subst hk; simp
    · have hk' : j = 2 * k := by omega
      subst hk'
      have hS := hasSum_zeta_nat (k := k) (by omega)
      have hle := hasSum_le (fun n : ℕ => ?_) hS hasSum_zeta_two
      swap
      · rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp [hkpos.ne']
        · have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
          apply one_div_le_one_div_of_le (by positivity)
          exact pow_le_pow_right₀ h1 (by omega)
      have hpos := hS.nonneg (fun n => by positivity)
      have hpi := pi_lt_d2
      have hpi0 := pi_pos
      have hT : |(-1 : ℝ) ^ (k + 1) * (2 : ℝ) ^ (2 * k - 1) * π ^ (2 * k) *
          ((bernoulli (2 * k) : ℚ) : ℝ) / ((2 * k).factorial : ℝ)| ≤ 2 := by
        rw [abs_of_nonneg hpos]
        nlinarith
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (by positivity : (0:ℝ) < 2 ^ (2 * k - 1)), abs_of_pos (by positivity : (0:ℝ) < π ^ (2 * k)),
        abs_of_pos (by positivity : (0:ℝ) < ((2 * k).factorial : ℝ))] at hT
      have h2 : (2 * π) ^ (2 * k) = 2 * (2 ^ (2 * k - 1) * π ^ (2 * k)) := by
        rw [mul_pow, ← mul_assoc, ← pow_succ']
        congr 2
        omega
      rw [h2]
      have hA : (0 : ℝ) < 2 ^ (2 * k - 1) * π ^ (2 * k) := by positivity
      have hF : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
      rw [div_le_iff₀ hF] at hT
      rw [le_div_iff₀ (by positivity)]
      nlinarith
  · rcases Nat.lt_or_ge 1 j with h | h
    · rw [bernoulli_eq_zero_of_odd hodd h]; simp; positivity
    · have : j = 1 := by obtain ⟨k, rfl⟩ := hodd; omega
      subst this
      rw [_root_.bernoulli_one]
      have := pi_le_four
      have := pi_pos
      rw [le_div_iff₀ (by positivity)]
      norm_num
      nlinarith

lemma bern_bernC_eval (p : ℕ) (y : ℂ) : (bernC p).eval y =
    ∑ i ∈ Finset.range (p + 1), ((_root_.bernoulli i * p.choose i : ℚ) : ℂ) * y ^ (p - i) := by
  simp [bernC, Polynomial.bernoulli, Polynomial.map_sum, eval_finsetSum, eval_monomial]

lemma bern_term_le {y : ℂ} {p i : ℕ} (hi : i ≤ p) (hp : (p : ℝ) ≤ π * ‖y‖) :
    ‖((_root_.bernoulli i * p.choose i : ℚ) : ℂ) * y ^ (p - i)‖ ≤ 4 * ‖y‖ ^ p * (1 / 2 : ℝ) ^ i := by
  have hy0 : 0 ≤ ‖y‖ := norm_nonneg _
  have hpi0 := pi_pos
  rw [norm_mul, Complex.norm_ratCast, Rat.cast_mul, abs_mul, Rat.cast_natCast, Nat.abs_cast,
    norm_pow]
  have hB := bern_bernoulli_abs_le i
  have hdesc : ((i.factorial * p.choose i : ℕ) : ℝ) ≤ (p : ℝ) ^ i := by
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    exact_mod_cast Nat.descFactorial_le_pow p i
  have hpow : (p : ℝ) ^ i ≤ (π * ‖y‖) ^ i := pow_le_pow_left₀ (by positivity) hp i
  have hsplit : ‖y‖ ^ p = ‖y‖ ^ i * ‖y‖ ^ (p - i) := (pow_mul_pow_sub _ hi).symm
  calc |((_root_.bernoulli i : ℚ) : ℝ)| * (p.choose i : ℝ) * ‖y‖ ^ (p - i)
      ≤ 4 * (i.factorial : ℝ) / (2 * π) ^ i * (p.choose i : ℝ) * ‖y‖ ^ (p - i) := by gcongr
    _ = 4 * ((i.factorial * p.choose i : ℕ) : ℝ) / (2 * π) ^ i * ‖y‖ ^ (p - i) := by
        push_cast; ring
    _ ≤ 4 * (π * ‖y‖) ^ i / (2 * π) ^ i * ‖y‖ ^ (p - i) := by gcongr; exact hdesc.trans hpow
    _ = 4 * ‖y‖ ^ p * (1 / 2 : ℝ) ^ i := by
        rw [hsplit, mul_pow, mul_pow, div_pow]
        field_simp; ring

/-- **Lemma 2.2(b).** For `p ≤ π|y|`, `|B_p(y)| ≤ 8 |y|^p`. -/
theorem bernC_eval_norm_le {y : ℂ} {p : ℕ} (hp : (p : ℝ) ≤ π * ‖y‖) :
    ‖(bernC p).eval y‖ ≤ 8 * ‖y‖ ^ p := by
  rw [bern_bernC_eval]
  calc ‖∑ i ∈ Finset.range (p + 1), ((_root_.bernoulli i * p.choose i : ℚ) : ℂ) * y ^ (p - i)‖
      ≤ ∑ i ∈ Finset.range (p + 1), ‖((_root_.bernoulli i * p.choose i : ℚ) : ℂ) * y ^ (p - i)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (p + 1), 4 * ‖y‖ ^ p * (1 / 2 : ℝ) ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact bern_term_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hp
    _ = 4 * ‖y‖ ^ p * ∑ i ∈ Finset.range (p + 1), (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]
    _ ≤ 4 * ‖y‖ ^ p * 2 := by gcongr; exact sum_geometric_two_le _
    _ = 8 * ‖y‖ ^ p := by ring

lemma bern_bernC_eval_one_add (n : ℕ) (x : ℂ) :
    (bernC n).eval (1 + x) = (bernC n).eval x + n * x ^ (n - 1) := by
  have h := congrArg (fun q => (q.map (algebraMap ℚ ℂ)).eval x) (Polynomial.bernoulli_comp_one_add_X n)
  simpa [Polynomial.map_comp, bernC, eval_comp] using h

lemma bern_powSumPoly_eval (j : ℕ) (z : ℂ) : (powSumPoly j).eval z =
    (2 * (j : ℂ) + 1)⁻¹ * ((bernC (2 * j + 1)).eval ((z + 1) / 2) -
      (bernC (2 * j + 1)).eval ((1 - z) / 2)) := by
  simp only [powSumPoly, eval_mul, eval_C, eval_sub, eval_comp, eval_add, eval_X, eval_one]
  congr 3 <;> ring

/-- **Lemma 2.2(a).** `P_{2j}(m)` is the symmetric power sum `∑_{i<m} (i - (m-1)/2)^{2j}`. -/
theorem powSumPoly_eval_nat (j m : ℕ) :
    (powSumPoly j).eval (m : ℂ) = ∑ i ∈ Finset.range m, ((i : ℂ) - ((m : ℂ) - 1) / 2) ^ (2 * j) := by
  rw [bern_powSumPoly_eval]
  set f : ℕ → ℂ := fun i => (bernC (2 * j + 1)).eval ((i : ℂ) - ((m : ℂ) - 1) / 2) with hf
  have htel := Finset.sum_range_sub f m
  have hstep : ∀ i, f (i + 1) - f i = (2 * (j : ℂ) + 1) * ((i : ℂ) - ((m : ℂ) - 1) / 2) ^ (2 * j) := by
    intro i
    simp only [hf]
    rw [show ((i + 1 : ℕ) : ℂ) - ((m : ℂ) - 1) / 2 = 1 + ((i : ℂ) - ((m : ℂ) - 1) / 2) by
      push_cast; ring, bern_bernC_eval_one_add]
    push_cast
    simp
  simp_rw [hstep, ← Finset.mul_sum] at htel
  have h1 : f m = (bernC (2 * j + 1)).eval (((m : ℂ) + 1) / 2) := by
    simp only [hf]; congr 1; ring
  have h0 : f 0 = (bernC (2 * j + 1)).eval ((1 - (m : ℂ)) / 2) := by
    simp only [hf]; congr 1; push_cast; ring
  rw [← h1, ← h0, ← htel, ← mul_assoc, inv_mul_cancel₀, one_mul]
  have : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  exact_mod_cast this.ne'

/-- **Growth bound for `P_{2j}`.** If `2j+1 ≤ π |(z+1)/2|` and `2j+1 ≤ π |(1-z)/2|`, then
`|P_{2j}(z)| ≤ 16 (|z|/2 + 1/2)^{2j+1}/(2j+1)`. -/
theorem powSumPoly_norm_le {z : ℂ} {j : ℕ}
    (hp1 : (2 * j + 1 : ℝ) ≤ π * ‖(z + 1) / 2‖) (hp2 : (2 * j + 1 : ℝ) ≤ π * ‖(1 - z) / 2‖) :
    ‖(powSumPoly j).eval z‖ ≤ 16 * (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) / (2 * j + 1) := by
  rw [bern_powSumPoly_eval]
  have hj : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  have hnorm : ‖(2 * (j : ℂ) + 1)⁻¹‖ = (2 * (j : ℝ) + 1)⁻¹ := by
    rw [norm_inv]
    congr 1
    rw [show (2 * (j : ℂ) + 1) = ((2 * (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg hj.le]
  have hc : ((2 * j + 1 : ℕ) : ℝ) = 2 * (j : ℝ) + 1 := by push_cast; ring
  have hb1 := bernC_eval_norm_le (y := (z + 1) / 2) (p := 2 * j + 1) (by rw [hc]; exact hp1)
  have hb2 := bernC_eval_norm_le (y := (1 - z) / 2) (p := 2 * j + 1) (by rw [hc]; exact hp2)
  have hn1 : ‖(z + 1) / 2‖ ≤ ‖z‖ / 2 + 1 / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_add_le z 1
    rw [norm_one] at this
    linarith
  have hn2 : ‖(1 - z) / 2‖ ≤ ‖z‖ / 2 + 1 / 2 := by
    rw [norm_div, Complex.norm_two]
    have := norm_sub_le 1 z
    rw [norm_one] at this
    linarith
  have hq1 : ‖(z + 1) / 2‖ ^ (2 * j + 1) ≤ (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hn1 _
  have hq2 : ‖(1 - z) / 2‖ ^ (2 * j + 1) ≤ (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hn2 _
  rw [norm_mul, hnorm, inv_mul_eq_div]
  gcongr
  calc _ ≤ _ := norm_sub_le _ _
    _ ≤ 8 * ‖(z + 1) / 2‖ ^ (2 * j + 1) + 8 * ‖(1 - z) / 2‖ ^ (2 * j + 1) := add_le_add hb1 hb2
    _ ≤ 16 * (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) := by linarith

end Singmaster
