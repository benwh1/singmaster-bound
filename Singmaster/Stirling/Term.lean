module

public import Singmaster.Stirling.Defs

@[expose] public section

/-!
# Stirling's formula: the size of one term of Gudermann's series

For `Re w > 0` we have `j(w) = ∫₀^{1/2} 2s² / ((w + 1/2)² - s²) ds`. Since
`|(w+1/2)² - s²| ≥ |w+1/2|² - 1/4 ≥ (3/4)|w|²` when `|w| ≥ 1`, this gives `|j(w)| ≤ 1/(9|w|²)`.
-/

open Complex

namespace Singmaster

lemma st_hasDerivAt {a : ℂ} (ha : 1 / 2 < a.re) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
    HasDerivAt (fun t : ℝ => -2 * (t : ℂ) + a * (Complex.log (a + t) - Complex.log (a - t)))
      (2 * (s : ℂ) ^ 2 / (a ^ 2 - (s : ℂ) ^ 2)) s := by
  have hid : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 s := by
    simpa using (hasDerivAt_id s).ofReal_comp
  have hp : 0 < (a + s).re := by simp; linarith
  have hm : 0 < (a - s).re := by simp; linarith
  have hp0 : a + s ≠ 0 := fun h => by simp [h] at hp
  have hm0 : a - s ≠ 0 := fun h => by simp [h] at hm
  have h1 := (hid.const_add a).clog_real (mem_slitPlane_iff.mpr (Or.inl hp))
  have h2 := (hid.const_sub a).clog_real (mem_slitPlane_iff.mpr (Or.inl hm))
  have h3 := ((hid.const_mul (-2)).add ((h1.sub h2).const_mul a))
  convert h3 using 1
  have hq : a ^ 2 - (s : ℂ) ^ 2 = (a + s) * (a - s) := by ring
  rw [hq]
  field_simp
  ring

lemma st_integral_eq {w : ℂ} (hw : 0 < w.re) :
    binetTerm w = ∫ t in (0 : ℝ)..(1 / 2),
      2 * (t : ℂ) ^ 2 / ((w + 1 / 2) ^ 2 - (t : ℂ) ^ 2) := by
  have ha : 1 / 2 < (w + 1 / 2).re := by simp; linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun t : ℝ => -2 * (t : ℂ) + (w + 1 / 2) *
      (Complex.log ((w + 1 / 2) + t) - Complex.log ((w + 1 / 2) - t)))]
  · have e1 : (w + 1 / 2) + ((1 / 2 : ℝ) : ℂ) = w + 1 := by push_cast; ring
    have e2 : (w + 1 / 2) - ((1 / 2 : ℝ) : ℂ) = w := by push_cast; ring
    simp only [e1, e2, binetTerm]
    push_cast
    simp only [add_zero, sub_zero, sub_self, mul_zero]
    ring
  · intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    exact st_hasDerivAt ha hx.1 hx.2
  · apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by norm_num)]
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x hx
    have hp : 0 < ((w + 1 / 2) + x).re := by simp; linarith [hx.1]
    have hm : 0 < ((w + 1 / 2) - x).re := by simp; linarith [hx.2]
    have hq : (w + 1 / 2) ^ 2 - (x : ℂ) ^ 2 = ((w + 1 / 2) + x) * ((w + 1 / 2) - x) := by ring
    rw [hq]
    exact mul_ne_zero (fun h => by rw [h] at hp; simp at hp) (fun h => by rw [h] at hm; simp at hm)

lemma st_denom_ge {w : ℂ} (hw : 0 < w.re) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2) :
    ‖w‖ ^ 2 ≤ ‖(w + 1 / 2) ^ 2 - (t : ℂ) ^ 2‖ := by
  have h1 : ‖(w + 1 / 2) ^ 2‖ - ‖(t : ℂ) ^ 2‖ ≤ ‖(w + 1 / 2) ^ 2 - (t : ℂ) ^ 2‖ :=
    norm_sub_norm_le _ _
  have h2 : ‖(w + 1 / 2) ^ 2‖ = ‖w‖ ^ 2 + w.re + 1 / 4 := by
    rw [norm_pow, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    ring
  have h3 : ‖(t : ℂ) ^ 2‖ = t ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have h4 : t ^ 2 ≤ 1 / 4 := by nlinarith
  linarith

theorem binetTerm_norm_le {w : ℂ} (hw : 0 < w.re) (hw1 : 1 ≤ ‖w‖) :
    ‖binetTerm w‖ ≤ 1 / (9 * ‖w‖ ^ 2) := by
  have hwpos : 0 < ‖w‖ := by linarith
  have hw2 : 0 < ‖w‖ ^ 2 := by positivity
  rw [st_integral_eq hw]
  have hb : ‖∫ t in (0 : ℝ)..(1 / 2), 2 * (t : ℂ) ^ 2 / ((w + 1 / 2) ^ 2 - (t : ℂ) ^ 2)‖ ≤
      ∫ t in (0 : ℝ)..(1 / 2), 2 * t ^ 2 / ‖w‖ ^ 2 := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by norm_num)
    · refine Filter.Eventually.of_forall (fun t ht => ?_)
      rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp only [Complex.norm_ofNat]
      apply div_le_div_of_nonneg_left (by positivity) hw2
      exact st_denom_ge hw ht.1.le ht.2
    · apply Continuous.intervalIntegrable
      fun_prop
  have hI : ∫ t in (0 : ℝ)..(1 / 2), 2 * t ^ 2 / ‖w‖ ^ 2 = 1 / (12 * ‖w‖ ^ 2) := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_const_mul, integral_pow]
    field_simp
    norm_num
  rw [hI] at hb
  refine hb.trans ?_
  apply one_div_le_one_div_of_le (by positivity)
  linarith

/-- Each term is holomorphic on the right half-plane. -/
theorem binetTerm_differentiableOn :
    DifferentiableOn ℂ binetTerm {w : ℂ | 0 < w.re} := by
  intro w hw
  have hw : 0 < w.re := hw
  have h1 : (w + 1) ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (by simp; linarith))
  have h0 : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
  apply DifferentiableAt.differentiableWithinAt
  unfold binetTerm
  have d1 : DifferentiableAt ℂ (fun z : ℂ => Complex.log (z + 1)) w :=
    (differentiableAt_id.add_const 1).clog h1
  have d0 : DifferentiableAt ℂ (fun z : ℂ => Complex.log z) w :=
    differentiableAt_id.clog h0
  exact ((differentiableAt_id.add_const _).mul (d1.sub d0)).sub_const _

end Singmaster
