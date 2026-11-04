module

public import Mathlib

@[expose] public section

/-!
# Proposition 6.1: Taylor truncation and a zero count from Jensen's formula

`taylor_trunc` gives the bounds (6.4) for the Taylor polynomials of a function close to `1`, and
`card_zeros_le_of_jensen` bounds the number of zeros of a holomorphic function in a disc by
Jensen's formula.
-/

open Complex Metric

namespace Singmaster

/-- Cauchy estimate for the Taylor coefficients of `g` with `|g - 1| ≤ 1/10`. -/
lemma an_coeff_bound {g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hg : DifferentiableOn ℂ g (closedBall 0 R))
    (hg1 : ∀ s ∈ closedBall (0 : ℂ) R, ‖g s - 1‖ ≤ 1 / 10) {m : ℕ} (hm : 0 < m) (s : ℂ)
    (hs : ‖s‖ ≤ 5) :
    ‖((m.factorial : ℂ)⁻¹ * iteratedDeriv m g 0) * s ^ m‖ ≤ (1 / 10) * (5 / R) ^ m := by
  have hd : DifferentiableOn ℂ (fun z => (-1 : ℂ) + g z) (closedBall 0 R) :=
    (differentiableOn_const _).add hg
  have hC : ∀ z ∈ sphere (0 : ℂ) R, ‖(fun z => (-1 : ℂ) + g z) z‖ ≤ 1 / 10 := by
    intro z hz
    simp only [neg_add_eq_sub]
    exact hg1 z (sphere_subset_closedBall hz)
  have h1 := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hR
    (hd.diffContOnCl_ball subset_rfl) hC
  rw [iteratedDeriv_const_add hm] at h1
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc (m.factorial : ℝ)⁻¹ * ‖iteratedDeriv m g 0‖ * ‖s‖ ^ m
      ≤ (m.factorial : ℝ)⁻¹ * (m.factorial * (1 / 10) / R ^ m) * 5 ^ m := by
        gcongr
    _ = (1 / 10) * (5 / R) ^ m := by
        rw [div_pow]
        field_simp

/-- **Taylor truncation.** If `g` is analytic on `|s| ≤ R` (`R ≥ 20`) with `|g - 1| ≤ 1/10`
there, then on `|s| ≤ 5` its degree-`J` Taylor polynomial `Π` satisfies
`|g - Π| ≤ (1/5) (5/R)^{J+1}` and `|Π| ≥ 1/2`. -/
theorem taylor_trunc {g : ℂ → ℂ} {R : ℝ} (hR : 20 ≤ R)
    (hg : DifferentiableOn ℂ g (closedBall 0 R))
    (hg1 : ∀ s ∈ closedBall (0 : ℂ) R, ‖g s - 1‖ ≤ 1 / 10) (J : ℕ) (s : ℂ) (hs : ‖s‖ ≤ 5) :
    ‖g s - ∑ n ∈ Finset.range (J + 1), ((n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0) * s ^ n‖ ≤
        (1 / 5) * (5 / R) ^ (J + 1) ∧
      1 / 2 ≤ ‖∑ n ∈ Finset.range (J + 1), ((n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0) * s ^ n‖ := by
  have hR0 : 0 < R := by linarith
  set a : ℕ → ℂ := fun n => ((n.factorial : ℂ)⁻¹ * iteratedDeriv n g 0) * s ^ n with ha
  have hsR : s ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff]; linarith
  have hsum : HasSum a (g s) := by
    have := Complex.hasSum_taylorSeries_on_ball (hg.mono ball_subset_closedBall) hsR
    convert this using 2 with n
    simp only [ha, sub_zero, smul_eq_mul]
    ring
  have htail : HasSum (fun n => a (n + (J + 1))) (g s - ∑ i ∈ Finset.range (J + 1), a i) :=
    (hasSum_nat_add_iff' (J + 1)).2 hsum
  set q : ℝ := 5 / R with hq
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q ≤ 1 / 4 := by
    rw [hq, div_le_iff₀ hR0]; linarith
  have hgeom : HasSum (fun n => (1 / 10) * q ^ (J + 1) * q ^ n)
      ((1 / 10) * q ^ (J + 1) * (1 - q)⁻¹) :=
    (hasSum_geometric_of_lt_one hq0 (by linarith)).mul_left _
  have hbd := htail.norm_le_of_bounded hgeom (fun n => by
    have := an_coeff_bound hR0 hg hg1 (m := n + (J + 1)) (by omega) s hs
    calc ‖a (n + (J + 1))‖ ≤ (1 / 10) * q ^ (n + (J + 1)) := this
      _ = (1 / 10) * q ^ (J + 1) * q ^ n := by ring)
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have hqJ : 0 ≤ q ^ (J + 1) := pow_nonneg hq0 _
  have h1 : ‖g s - ∑ i ∈ Finset.range (J + 1), a i‖ ≤ (1 / 5) * q ^ (J + 1) := by
    refine hbd.trans ?_
    calc (1 / 10) * q ^ (J + 1) * (1 - q)⁻¹ ≤ (1 / 10) * q ^ (J + 1) * 2 := by gcongr
      _ = (1 / 5) * q ^ (J + 1) := by ring
  refine ⟨h1, ?_⟩
  have hqJ1 : q ^ (J + 1) ≤ 1 := pow_le_one₀ hq0 (by linarith)
  have hgs : 9 / 10 ≤ ‖g s‖ := by
    have h := hg1 s (ball_subset_closedBall hsR)
    have := norm_sub_norm_le (1 : ℂ) (g s)
    rw [norm_sub_rev] at h
    simp at this
    linarith
  have := norm_sub_norm_le (g s) (∑ i ∈ Finset.range (J + 1), a i)
  have h2 : ‖g s‖ - ‖∑ i ∈ Finset.range (J + 1), a i‖ ≤ 1 / 5 := by
    linarith
  linarith

/-- Each zero of an analytic function on a closed ball, which is nonzero at the centre,
contributes at least `1` to the divisor. -/
lemma an_one_le_divisor {f : ℂ → ℂ} {c : ℂ} {r R : ℝ} (hrR : r ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hc : f c ≠ 0) {z : ℂ}
    (hz : z ∈ closedBall c r) (hz0 : f z = 0) :
    1 ≤ MeromorphicOn.divisor f (closedBall c r) z := by
  have hzR : z ∈ closedBall c R := closedBall_subset_closedBall hrR hz
  have hr0 : 0 ≤ r := by
    have := mem_closedBall.1 hz
    exact dist_nonneg.trans this
  have hcR : c ∈ closedBall c R := mem_closedBall_self (hr0.trans hrR)
  have hfr : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono (closedBall_subset_closedBall hrR)
  have hne_top : analyticOrderAt f z ≠ ⊤ :=
    hf.analyticOrderAt_ne_top_of_isPreconnected (convex_closedBall c R).isPreconnected hcR hzR
      (by rw [(hf c hcR).analyticOrderAt_eq_zero.2 hc]; exact ENat.zero_ne_top)
  have hne_zero : analyticOrderAt f z ≠ 0 := (hf z hzR).analyticOrderAt_ne_zero.2 hz0
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hfr hz]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 hne_top
  rw [← hn] at hne_zero ⊢
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; exact absurd rfl hne_zero
    · exact h
  simp
  exact_mod_cast hn1

/-- Finset cardinality is bounded by the finsum of a nonnegative integer function which is
at least `1` on the finset. -/
lemma an_card_le_finsum {f : ℂ → ℤ} (Z : Finset ℂ) (hfin : (Function.support f).Finite)
    (h0 : ∀ u, 0 ≤ f u) (h1 : ∀ z ∈ Z, 1 ≤ f z) : (Z.card : ℤ) ≤ ∑ᶠ u, f u := by
  classical
  rw [finsum_eq_sum_of_support_subset f (s := Z ∪ hfin.toFinset)
    (by intro u hu; simp [hu])]
  calc (Z.card : ℤ) = ∑ z ∈ Z, (1 : ℤ) := by simp
    _ ≤ ∑ z ∈ Z, f z := Finset.sum_le_sum h1
    _ ≤ ∑ u ∈ Z ∪ hfin.toFinset, f u :=
        Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun u _ _ => h0 u)

/-- **Jensen zero count.** If `G` is analytic near `|s - c| ≤ 3`, `G(c) ≠ 0` and `|G| ≤ M` on
`|s - c| = 3`, then `G` has at most `log(M/|G(c)|)/log 2` distinct zeros in `|s - c| ≤ 3/2`. -/
theorem card_zeros_le_of_jensen {G : ℂ → ℂ} {c : ℂ} {M : ℝ}
    (hG : AnalyticOnNhd ℂ G (closedBall c 3)) (hc : G c ≠ 0)
    (hM : ∀ z ∈ sphere c 3, ‖G z‖ ≤ M) (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, z ∈ closedBall c (3 / 2) ∧ G z = 0) :
    (Z.card : ℝ) ≤ Real.log (M / ‖G c‖) / Real.log 2 := by
  set a : ℝ := ‖G c‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 hc
  -- maximum modulus: `‖G c‖ ≤ M`
  have hGcM : a ≤ M := by
    have hd : DiffContOnCl ℂ G (ball c 3) :=
      (hG.differentiableOn).diffContOnCl_ball subset_rfl
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd ?_ ?_
    · intro z hz
      rw [frontier_ball c (by norm_num : (3 : ℝ) ≠ 0)] at hz
      exact hM z hz
    · rw [closure_ball c (by norm_num : (3 : ℝ) ≠ 0)]
      exact mem_closedBall_self (by norm_num)
  set f : ℂ → ℂ := fun z => (a⁻¹ : ℂ) * G z with hf
  have hfa : AnalyticOnNhd ℂ f (closedBall c |3|) := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact fun z hz => analyticAt_const.mul (hG z hz)
  have hfc : f c ≠ 0 := by
    simp only [hf]
    exact mul_ne_zero (inv_ne_zero (by exact_mod_cast ha0.ne')) hc
  have hfcn : ‖f c‖ = 1 := by
    simp only [hf, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    rw [← ha]; field_simp
  have hfM : ∀ z ∈ sphere c |3|, ‖f z‖ ≤ M / a := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    intro z hz
    simp only [hf, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_right (hM z hz) ha0.le
  have hM1 : 1 ≤ M / a := by rw [le_div_iff₀ ha0]; linarith
  have J := AnalyticOnNhd.sum_divisor_le (r := 3 / 2) (R := 3) (by norm_num)
    (by norm_num [abs_of_pos]) hM1 hfa hfc hfM
  rw [hfcn, div_one, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at J
  have h32 : (3 : ℝ) / (3 / 2) = 2 := by norm_num
  rw [h32] at J
  have hfa' : AnalyticOnNhd ℂ f (closedBall c 3) := by
    simpa [abs_of_pos (by norm_num : (0 : ℝ) < 3)] using hfa
  have hcard := an_card_le_finsum Z
    ((MeromorphicOn.divisor f (closedBall c (3 / 2))).finiteSupport (isCompact_closedBall _ _))
    (fun u => MeromorphicOn.AnalyticOnNhd.divisor_nonneg
      (hfa'.mono (closedBall_subset_closedBall (by norm_num : (3 / 2 : ℝ) ≤ 3))) u)
    (fun z hz => an_one_le_divisor (by norm_num) hfa' hfc (hZ z hz).1
      (by simp only [hf, (hZ z hz).2, mul_zero]))
  have : (Z.card : ℝ) ≤ ((∑ᶠ u, MeromorphicOn.divisor f (closedBall c (3 / 2)) u : ℤ) : ℝ) := by
    exact_mod_cast hcard
  exact this.trans J

end Singmaster
