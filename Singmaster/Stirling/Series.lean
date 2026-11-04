module

public import Singmaster.Stirling.Term

@[expose] public section

/-!
# Stirling's formula: Gudermann's series

Convergence and holomorphy of `J`, and Binet's bound `|J(z)| ≤ 4/(9|z|)` for `Re z > 0` and
`|z| ≥ 1`.
-/

open Complex

namespace Singmaster

/-- `|z + x|² = |z|² + 2 x Re z + x²` for real `x`. -/
lemma st_sq_norm_add (z : ℂ) (x : ℝ) : ‖z + x‖ ^ 2 = ‖z‖ ^ 2 + 2 * x * z.re + x ^ 2 := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
  ring

lemma st_re_add_pos {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) : 0 < (z + x).re := by
  simp only [add_re, ofReal_re]; linarith

lemma st_le_norm_add {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) : x ≤ ‖z + x‖ := by
  have h := Complex.abs_re_le_norm (z + x)
  rw [abs_of_pos (st_re_add_pos hz hx)] at h
  simp only [add_re, ofReal_re] at h
  linarith

lemma st_norm_le_norm_add {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) : ‖z‖ ≤ ‖z + x‖ := by
  have h := st_sq_norm_add z x
  have h2 : ‖z‖ ^ 2 ≤ ‖z + x‖ ^ 2 := by rw [h]; nlinarith
  nlinarith [norm_nonneg z, norm_nonneg (z + x)]

lemma st_sq_le {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 ≤ x) :
    (‖z‖ + x) ^ 2 ≤ 2 * ‖z + x‖ ^ 2 := by
  rw [st_sq_norm_add]; nlinarith [sq_nonneg (‖z‖ - x)]

/-- For `x ≥ 1`, `|j(z + x)| ≤ 1/x²`. -/
lemma st_term_le_inv_sq {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 1 ≤ x) :
    ‖binetTerm (z + x)‖ ≤ 1 / x ^ 2 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hn := st_le_norm_add hz hx0
  have h := binetTerm_norm_le (st_re_add_pos hz hx0) (hx.trans hn)
  refine h.trans ?_
  have hp : 0 < ‖z + x‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [pow_le_pow_left₀ hx0 hn 2, sq_nonneg x]

/-- For `|z| ≥ 1`, `|j(z + x)| ≤ 2/(9(|z| + x)²)`. -/
lemma st_term_le_shift {z : ℂ} (hz : 0 < z.re) (hz1 : 1 ≤ ‖z‖) {x : ℝ} (hx : 0 ≤ x) :
    ‖binetTerm (z + x)‖ ≤ 2 / (9 * (‖z‖ + x) ^ 2) := by
  have hn := st_norm_le_norm_add hz hx
  have h := binetTerm_norm_le (st_re_add_pos hz hx) (hz1.trans hn)
  refine h.trans ?_
  have := st_sq_le hz hx
  have hp : 0 < ‖z + x‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- `1/t² ≤ 1/(t - 1/2) - 1/(t + 1/2)` for `t ≥ 1`. -/
lemma st_inv_sq_le_telescope {t : ℝ} (ht : 1 ≤ t) :
    1 / t ^ 2 ≤ 1 / (t - 1 / 2) - 1 / (t + 1 / 2) := by
  have h1 : 0 < t - 1 / 2 := by linarith
  have h2 : 0 < t + 1 / 2 := by linarith
  rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma st_summable_norm {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => ‖binetTerm (z + n)‖) := by
  rw [← summable_nat_add_iff 1]
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hs
  have h := st_term_le_inv_sq hz (x := ((n + 1 : ℕ) : ℝ)) (by simp)
  simpa using h

theorem binetJ_summable {z : ℂ} (hz : 0 < z.re) : Summable (fun n : ℕ => binetTerm (z + n)) :=
  (st_summable_norm hz).of_norm

theorem binetJ_norm_le {z : ℂ} (hz : 0 < z.re) (hz1 : 1 ≤ ‖z‖) :
    ‖binetJ z‖ ≤ 4 / (9 * ‖z‖) := by
  set y := ‖z‖ with hy
  have hy0 : 0 < y := by linarith
  refine (norm_tsum_le_tsum_norm (st_summable_norm hz)).trans ?_
  refine Real.tsum_le_of_sum_range_le (fun _ => norm_nonneg _) (fun N => ?_)
  have hterm : ∀ n : ℕ, ‖binetTerm (z + n)‖ ≤
      (2 / 9) * (1 / (y + n - 1 / 2) - 1 / (y + (n + 1 : ℕ) - 1 / 2)) := by
    intro n
    have h := st_term_le_shift hz hz1 (x := (n : ℝ)) (Nat.cast_nonneg n)
    have ht := st_inv_sq_le_telescope (t := y + n) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    simp only [ofReal_natCast] at h
    refine h.trans ?_
    have e1 : y + ((n + 1 : ℕ) : ℝ) - 1 / 2 = y + n + 1 / 2 := by push_cast; ring
    rw [e1]
    have : 2 / (9 * (y + n) ^ 2) = (2 / 9) * (1 / (y + n) ^ 2) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left ht (by norm_num)
  refine (Finset.sum_le_sum (fun n _ => hterm n)).trans ?_
  rw [← Finset.mul_sum, Finset.sum_range_sub' (fun n : ℕ => 1 / (y + n - 1 / 2)) N]
  simp only [Nat.cast_zero, add_zero]
  have hN : 0 < 1 / (y + N - 1 / 2) := by
    have := Nat.cast_nonneg (α := ℝ) N
    apply div_pos one_pos; linarith
  have h3 : 1 / (y - 1 / 2) ≤ 2 / y := by
    rw [div_le_div_iff₀ (by linarith) hy0]; linarith
  calc 2 / 9 * (1 / (y - 1 / 2) - 1 / (y + N - 1 / 2)) ≤ 2 / 9 * (2 / y) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num); linarith
    _ = 4 / (9 * y) := by field_simp; ring

theorem binetJ_differentiableOn : DifferentiableOn ℂ binetJ {z : ℂ | 0 < z.re} := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  -- the tail `∑' n, j(z + (n + 1))`
  have hs : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)).mpr
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hmaps : ∀ c : ℝ, 0 ≤ c → Set.MapsTo (fun w : ℂ => w + c) U U := by
    intro c hc w hw
    exact st_re_add_pos hw hc
  have hF : ∀ n : ℕ, DifferentiableOn ℂ (fun w : ℂ => binetTerm (w + ((n + 1 : ℕ) : ℝ))) U := by
    intro n
    exact binetTerm_differentiableOn.comp (differentiableOn_id.add_const _)
      (hmaps _ (Nat.cast_nonneg _))
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ U →
      ‖binetTerm (w + ((n + 1 : ℕ) : ℝ))‖ ≤ 1 / ((n + 1 : ℕ) : ℝ) ^ 2 := by
    intro n w hw
    exact st_term_le_inv_sq hw (by simp)
  have htail := Complex.differentiableOn_tsum_of_summable_norm hs hF hUo hFle
  have hhead : DifferentiableOn ℂ binetTerm U := binetTerm_differentiableOn
  refine (hhead.add htail).congr ?_
  intro z hz
  rw [binetJ, (binetJ_summable hz).tsum_eq_zero_add]
  simp

end Singmaster
