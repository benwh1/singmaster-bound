module

public import Mathlib

@[expose] public section

/-!
# A holomorphic fixed point

The equation `v = ∑_{j=1}^N a_j(z) e^{-2j v}` with small holomorphic coefficients `a_j` has a
unique small solution `v(z)`. It is holomorphic in `z`, as a uniform limit of holomorphic
iterates, and stable: any `w` with a small defect `w - Φ_z(w)` is close to `v(z)`
(`analytic_fixed_point`). This is the fixed-point step in the proof of Proposition 3.1.
-/

open Complex Metric

namespace Singmaster

/-- The map `Φ_z(w) = ∑_{j=1}^N a_j(z) e^{-2jw}`. -/
noncomputable def fp_Phi (N : ℕ) (a : ℕ → ℂ → ℂ) (z w : ℂ) : ℂ :=
  ∑ j ∈ Finset.Icc 1 N, a j z * cexp (-(2 * (j : ℂ)) * w)

/-- The Picard iterates `v_0 = 0`, `v_{n+1}(z) = Φ_z(v_n(z))`. -/
noncomputable def fp_iter (N : ℕ) (a : ℕ → ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => fun _ => 0
  | n + 1 => fun z => fp_Phi N a z (fp_iter N a n z)

lemma fp_norm_neg_two_mul (j : ℕ) : ‖-(2 * (j : ℂ))‖ = 2 * j := by
  simp

lemma fp_norm_cexp_le (j : ℕ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖cexp (-(2 * (j : ℂ)) * w)‖ ≤ Real.exp (2 * j) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc (-(2 * (j : ℂ)) * w).re ≤ ‖-(2 * (j : ℂ)) * w‖ := Complex.re_le_norm _
    _ = 2 * j * ‖w‖ := by rw [norm_mul, fp_norm_neg_two_mul]
    _ ≤ 2 * j := mul_le_of_le_one_right (by positivity) hw

lemma fp_cexp_lip (j : ℕ) {w w' : ℂ} (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) :
    ‖cexp (-(2 * (j : ℂ)) * w) - cexp (-(2 * (j : ℂ)) * w')‖
      ≤ 2 * j * Real.exp (2 * j) * ‖w - w'‖ := by
  have hderiv : ∀ x ∈ closedBall (0 : ℂ) 1,
      HasDerivWithinAt (fun x => cexp (-(2 * (j : ℂ)) * x))
        (cexp (-(2 * (j : ℂ)) * x) * (-(2 * (j : ℂ)) * 1)) (closedBall 0 1) x := by
    intro x _
    exact (((hasDerivAt_id x).const_mul (-(2 * (j : ℂ)))).cexp).hasDerivWithinAt
  have hb : ∀ x ∈ closedBall (0 : ℂ) 1,
      ‖cexp (-(2 * (j : ℂ)) * x) * (-(2 * (j : ℂ)) * 1)‖ ≤ 2 * j * Real.exp (2 * j) := by
    intro x hx
    rw [mul_one, norm_mul, mul_comm, fp_norm_neg_two_mul]
    exact mul_le_mul_of_nonneg_left (fp_norm_cexp_le j (by simpa using hx)) (by positivity)
  exact (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hb
    (by simpa using hw') (by simpa using hw)

lemma fp_sum_le_half {N : ℕ} {a : ℕ → ℂ → ℂ} {z : ℂ} {q : ℝ}
    (hb : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q) :
    ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * Real.exp (2 * j) ≤ q / 2 := by
  have h : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * Real.exp (2 * j) * 2
      ≤ ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) := by
    apply Finset.sum_le_sum
    intro j hj
    have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast (Finset.mem_Icc.mp hj).1
    have h0 : 0 ≤ ‖a j z‖ * Real.exp (2 * j) :=
      mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
    have := mul_le_mul_of_nonneg_left (by linarith : (2 : ℝ) ≤ 2 * j) h0
    linarith
  rw [← Finset.sum_mul] at h
  linarith

lemma fp_Phi_norm_le {N : ℕ} {a : ℕ → ℂ → ℂ} {z w : ℂ} {q : ℝ}
    (hb : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q) (hw : ‖w‖ ≤ 1) :
    ‖fp_Phi N a z w‖ ≤ q / 2 := by
  unfold fp_Phi
  calc _ ≤ ∑ j ∈ Finset.Icc 1 N, ‖a j z * cexp (-(2 * (j : ℂ)) * w)‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * Real.exp (2 * j) := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (fp_norm_cexp_le j hw) (norm_nonneg _)
    _ ≤ q / 2 := fp_sum_le_half hb

lemma fp_Phi_lip {N : ℕ} {a : ℕ → ℂ → ℂ} {z w w' : ℂ} {q : ℝ}
    (hb : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q)
    (hw : ‖w‖ ≤ 1) (hw' : ‖w'‖ ≤ 1) :
    ‖fp_Phi N a z w - fp_Phi N a z w'‖ ≤ q * ‖w - w'‖ := by
  unfold fp_Phi
  rw [← Finset.sum_sub_distrib]
  calc _ ≤ ∑ j ∈ Finset.Icc 1 N,
        ‖a j z * cexp (-(2 * (j : ℂ)) * w) - a j z * cexp (-(2 * (j : ℂ)) * w')‖ :=
        norm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) * ‖w - w'‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub, norm_mul, mul_assoc, mul_assoc, ← mul_assoc (2 * (j : ℝ))]
        exact mul_le_mul_of_nonneg_left (fp_cexp_lip j hw hw') (norm_nonneg _)
    _ = (∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j)) * ‖w - w'‖ := by
        rw [Finset.sum_mul]
    _ ≤ q * ‖w - w'‖ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)

lemma fp_Phi_continuous (N : ℕ) (a : ℕ → ℂ → ℂ) (z : ℂ) :
    Continuous (fun w => fp_Phi N a z w) := by
  unfold fp_Phi
  fun_prop

lemma fp_Phi_diff {U : Set ℂ} {N : ℕ} {a : ℕ → ℂ → ℂ} (ha : ∀ j, DifferentiableOn ℂ (a j) U)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun z => fp_Phi N a z (g z)) U := by
  unfold fp_Phi
  apply DifferentiableOn.fun_sum
  intro j _
  exact (ha j).mul ((hg.const_mul _).cexp)

lemma fp_iter_diff {U : Set ℂ} {N : ℕ} {a : ℕ → ℂ → ℂ} (ha : ∀ j, DifferentiableOn ℂ (a j) U)
    (n : ℕ) : DifferentiableOn ℂ (fp_iter N a n) U := by
  induction n with
  | zero => exact differentiableOn_const _
  | succ n ih => exact fp_Phi_diff ha ih

lemma fp_iter_norm {N : ℕ} {a : ℕ → ℂ → ℂ} {z : ℂ} {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (hb : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q) (n : ℕ) :
    ‖fp_iter N a n z‖ ≤ q / 2 := by
  induction n with
  | zero => simp [fp_iter]; linarith
  | succ n ih => exact fp_Phi_norm_le hb (by linarith)

lemma fp_iter_step {N : ℕ} {a : ℕ → ℂ → ℂ} {z : ℂ} {q : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ 1 / 4)
    (hb : ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q) (n : ℕ) :
    dist (fp_iter N a n z) (fp_iter N a (n + 1) z) ≤ q / 2 * q ^ n := by
  induction n with
  | zero =>
      rw [dist_comm, dist_eq_norm]
      simp only [fp_iter, sub_zero, pow_zero, mul_one]
      exact fp_Phi_norm_le hb (by simp)
  | succ n ih =>
      rw [dist_comm, dist_eq_norm]
      rw [dist_comm, dist_eq_norm] at ih
      have h1 := fp_iter_norm hq0 hq hb (n + 1)
      have h2 := fp_iter_norm hq0 hq hb n
      calc ‖fp_iter N a (n + 1 + 1) z - fp_iter N a (n + 1) z‖
          = ‖fp_Phi N a z (fp_iter N a (n + 1) z) - fp_Phi N a z (fp_iter N a n z)‖ := rfl
        _ ≤ q * ‖fp_iter N a (n + 1) z - fp_iter N a n z‖ :=
            fp_Phi_lip hb (by linarith) (by linarith)
        _ ≤ q * (q / 2 * q ^ n) := mul_le_mul_of_nonneg_left ih hq0
        _ = q / 2 * q ^ (n + 1) := by ring

/-- **Analytic fixed point.** -/
theorem analytic_fixed_point {U : Set ℂ} (hU : IsOpen U) (N : ℕ) (a : ℕ → ℂ → ℂ)
    (ha : ∀ j, DifferentiableOn ℂ (a j) U) {q : ℝ} (hq : q ≤ 1 / 4)
    (hbound : ∀ z ∈ U, ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) ≤ q) :
    ∃ v : ℂ → ℂ, DifferentiableOn ℂ v U ∧
      (∀ z ∈ U, v z = ∑ j ∈ Finset.Icc 1 N, a j z * cexp (-(2 * (j : ℂ)) * v z)) ∧
      (∀ z ∈ U, ‖v z‖ ≤ q) ∧
      (∀ z ∈ U, ∀ w : ℂ, ‖w‖ ≤ 1 →
        ‖w - v z‖ ≤ 2 * ‖w - ∑ j ∈ Finset.Icc 1 N, a j z * cexp (-(2 * (j : ℂ)) * w)‖) := by
  by_cases hq0 : 0 ≤ q
  swap
  · have hUe : U = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      have h1 := hbound z hz
      have h2 : 0 ≤ ∑ j ∈ Finset.Icc 1 N, ‖a j z‖ * (2 * j) * Real.exp (2 * j) :=
        Finset.sum_nonneg (fun j _ => by positivity)
      linarith
    subst hUe
    exact ⟨0, differentiableOn_empty, by simp, by simp, by simp⟩
  have hq1 : q < 1 := by linarith
  set u := fp_iter N a with hu
  let v : ℂ → ℂ := fun z => Filter.limUnder Filter.atTop (fun n => u n z)
  have hlim : ∀ z ∈ U, Filter.Tendsto (fun n => u n z) Filter.atTop (nhds (v z)) := by
    intro z hz
    exact (cauchySeq_of_le_geometric q (q / 2) hq1
      (fp_iter_step hq0 hq (hbound z hz))).tendsto_limUnder
  have hrate : ∀ z ∈ U, ∀ n, dist (u n z) (v z) ≤ q / 2 * q ^ n / (1 - q) := fun z hz n =>
    dist_le_of_le_geometric_of_tendsto q (q / 2) hq1 (fp_iter_step hq0 hq (hbound z hz))
      (hlim z hz) n
  have hunif : TendstoUniformlyOn u v Filter.atTop U := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have ht : Filter.Tendsto (fun n : ℕ => q / 2 * q ^ n / (1 - q)) Filter.atTop (nhds 0) := by
      simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (q / 2)).div_const
        (1 - q)
    filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
    intro z hz
    rw [dist_comm]
    exact (hrate z hz n).trans_lt hn
  have hdiff : DifferentiableOn ℂ v U :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn
      (Filter.Eventually.of_forall fun n => fp_iter_diff ha n) hU
  have hfix : ∀ z ∈ U, v z = fp_Phi N a z (v z) := by
    intro z hz
    have h1 : Filter.Tendsto (fun n => u (n + 1) z) Filter.atTop (nhds (v z)) :=
      (hlim z hz).comp (Filter.tendsto_add_atTop_nat 1)
    have h2 : Filter.Tendsto (fun n => u (n + 1) z) Filter.atTop
        (nhds (fp_Phi N a z (v z))) :=
      ((fp_Phi_continuous N a z).tendsto _).comp (hlim z hz)
    exact tendsto_nhds_unique h1 h2
  have hvnorm : ∀ z ∈ U, ‖v z‖ ≤ q / 2 := fun z hz =>
    le_of_tendsto' (hlim z hz).norm (fun n => fp_iter_norm hq0 hq (hbound z hz) n)
  refine ⟨v, hdiff, fun z hz => hfix z hz, fun z hz => by linarith [hvnorm z hz], ?_⟩
  intro z hz w hw
  show ‖w - v z‖ ≤ 2 * ‖w - fp_Phi N a z w‖
  have hv1 : ‖v z‖ ≤ 1 := by linarith [hvnorm z hz]
  have hL := fp_Phi_lip (hbound z hz) hw hv1
  rw [← hfix z hz] at hL
  have htri : ‖w - v z‖ ≤ ‖w - fp_Phi N a z w‖ + ‖fp_Phi N a z w - v z‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hqx : q * ‖w - v z‖ ≤ 1 / 4 * ‖w - v z‖ := mul_le_mul_of_nonneg_right hq (norm_nonneg _)
  linarith [norm_nonneg (w - fp_Phi N a z w)]

end Singmaster
