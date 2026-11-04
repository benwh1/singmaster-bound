module

public import Singmaster.ExpPoly.ChiBounds
public import Singmaster.ExpPoly.Contour
public import Singmaster.ExpPoly.PolyIdentity

@[expose] public section

/-!
# Lemma 5.1: growth of exponential polynomials

Let `G₀(s) = ∑_{j ≤ k} R_j(s) e^{jTs}` with `deg R_j < ν_j`, `ν = ∑ ν_j`, and suppose that
`|G₀| ≤ m₀` on `|s| ≤ 1/2`. Then (`expPoly_bound`)

* (a) `|G₀(s)| ≤ C_a m₀` for `|s| ≤ 5`, where `C_a = ν 3^ν e^{5ϱ}` and `ϱ = max(2kT, 2ν)`;
* (b) `|R_j(s) e^{jTs}| ≤ C_b m₀` for `|s| ≤ 4`, where
  `C_b = 2 ν ((k+1) 2^{4k+2})^{ν_max} e^{(4k+2)T} max(1, (4ν/T)^ν)`.

The proof is by Laplace inversion. With `y_m = G₀^{(m)}(0)` and
`Y(w) = ∑_{m<ν} y_m χ_m(w)/χ(w)`, the identity `poly_laplace_identity` gives
`Y(w) = ∑_{j,p} r_{jp} p!/(w - jT)^{p+1}`. Then `circleIntegral_exp_div_sub_pow` shows that
`(2πi)⁻¹ ∮ e^{sw} Y(w) dw` over a circle is the sum of the components `R_j e^{jTs}` whose
frequency `jT` lies inside, which is (5.1). The bounds come from Cauchy's estimate
`|y_m| ≤ m! 2^m m₀` and from `chiPoly_bound_big` and `chiPoly_bound_small`.
-/

open Complex Polynomial Metric Real Finset

namespace Singmaster

/-- The exponential polynomial `∑_j R_j(s) e^{jTs}`. -/
noncomputable def expPoly (k : ℕ) (T : ℝ) (R : Fin (k + 1) → ℂ[X]) (s : ℂ) : ℂ :=
  ∑ j : Fin (k + 1), (R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)

lemma ep_eval_eq {P : ℂ[X]} {n : ℕ} (h : P.degree < n) (s : ℂ) :
    P.eval s = ∑ p ∈ range n, P.coeff p * s ^ p := by
  by_cases hP : P = 0
  · simp [hP]
  · exact eval_eq_sum_range' ((natDegree_lt_iff_degree_lt hP).2 h) s

lemma ep_expPoly_eq {k : ℕ} {T : ℝ} {R : Fin (k + 1) → ℂ[X]} {n : Fin (k + 1) → ℕ}
    (hR : ∀ j, (R j).degree < n j) (s : ℂ) :
    expPoly k T R s = ∑ j : Fin (k + 1), ∑ p ∈ range (n j),
      (R j).coeff p * (s ^ p * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)) := by
  unfold expPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ep_eval_eq (hR j), Finset.sum_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

lemma ep_differentiable (k : ℕ) (T : ℝ) (R : Fin (k + 1) → ℂ[X]) :
    Differentiable ℂ (expPoly k T R) := by
  unfold expPoly
  fun_prop

/-- The derivatives `y_m = G₀^{(m)}(0)`. -/
lemma ep_iteratedDeriv {k : ℕ} {T : ℝ} {R : Fin (k + 1) → ℂ[X]} {n : Fin (k + 1) → ℕ}
    (hR : ∀ j, (R j).degree < n j) (m : ℕ) :
    iteratedDeriv m (expPoly k T R) 0 = ∑ j : Fin (k + 1), ∑ p ∈ range (n j),
      (R j).coeff p * ((m.descFactorial p : ℂ) * (((j : ℕ) : ℂ) * (T : ℂ)) ^ (m - p)) := by
  rw [show expPoly k T R = fun s => ∑ j : Fin (k + 1), ∑ p ∈ range (n j),
      (R j).coeff p * (s ^ p * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)) from
    funext (ep_expPoly_eq hR)]
  rw [iteratedDeriv_fun_sum (fun j _ => by fun_prop)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iteratedDeriv_fun_sum (fun p _ => by fun_prop)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow_mul_exp_zero]

/-- The Cauchy estimate `|y_m| ≤ m! 2^m M`. -/
lemma ep_cauchy {k : ℕ} {T : ℝ} {R : Fin (k + 1) → ℂ[X]} {M : ℝ}
    (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly k T R s‖ ≤ M) (m : ℕ) :
    ‖iteratedDeriv m (expPoly k T R) 0‖ ≤ m.factorial * 2 ^ m * M := by
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := 1 / 2)
    (C := M) m (by norm_num) (ep_differentiable k T R).diffContOnCl
    (fun z hz => hM z (by rw [mem_sphere_zero_iff_norm] at hz; linarith))
  calc ‖iteratedDeriv m (expPoly k T R) 0‖ ≤ m.factorial * M / (1 / 2) ^ m := h
    _ = m.factorial * 2 ^ m * M := by
      rw [show ((1 : ℝ) / 2) ^ m = ((2 : ℝ) ^ m)⁻¹ by rw [one_div, inv_pow], div_inv_eq_mul]
      ring

lemma ep_chi_eval_ne_zero {k : ℕ} {T : ℝ} (n : Fin (k + 1) → ℕ) {w : ℂ}
    (hw : ∀ j : Fin (k + 1), w ≠ ((j : ℕ) : ℂ) * (T : ℂ)) : (chiPoly k T n).eval w ≠ 0 := by
  unfold chiPoly
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro j _
  simp only [eval_pow, eval_sub, eval_X, eval_C]
  exact pow_ne_zero _ (sub_ne_zero.2 (hw j))

lemma ep_chi_natDegree {k : ℕ} {T : ℝ} (n : Fin (k + 1) → ℕ) :
    (chiPoly k T n).natDegree ≤ ∑ j, n j := by
  unfold chiPoly
  refine (natDegree_prod_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  refine (natDegree_pow_le).trans ?_
  rw [natDegree_X_sub_C, mul_one]

lemma ep_chi_dvd {k : ℕ} {T : ℝ} (n : Fin (k + 1) → ℕ) (j : Fin (k + 1)) {p : ℕ}
    (hp : p < n j) : (X - C (((j : ℕ) : ℂ) * (T : ℂ))) ^ (p + 1) ∣ chiPoly k T n := by
  unfold chiPoly
  exact (pow_dvd_pow _ hp).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))

/-- The Laplace transform `Y(w) = ∑_{m<N} y_m χ_m(w)/χ(w)`. -/
noncomputable def laplaceY (k : ℕ) (T : ℝ) (R : Fin (k + 1) → ℂ[X]) (n : Fin (k + 1) → ℕ)
    (w : ℂ) : ℂ :=
  ∑ m ∈ range (∑ j, n j), iteratedDeriv m (expPoly k T R) 0 *
    ((divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w)

/-- Partial fractions: `Y(w) = ∑_{j,p} r_{jp} p!/(w - jT)^{p+1}` away from the roots. -/
lemma ep_laplaceY_eq {k : ℕ} {T : ℝ} {R : Fin (k + 1) → ℂ[X]} {n : Fin (k + 1) → ℕ}
    (hR : ∀ j, (R j).degree < n j) {w : ℂ}
    (hw : ∀ j : Fin (k + 1), w ≠ ((j : ℕ) : ℂ) * (T : ℂ)) :
    laplaceY k T R n w = ∑ j : Fin (k + 1), ∑ p ∈ range (n j),
      (R j).coeff p * ((p.factorial : ℂ) / (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1)) := by
  have hχ := ep_chi_eval_ne_zero (T := T) n hw
  -- the identity for one `(j, p)`
  have key : ∀ j : Fin (k + 1), ∀ p ∈ range (n j),
      ∑ m ∈ range (∑ j, n j), ((m.descFactorial p : ℂ) * (((j : ℕ) : ℂ) * (T : ℂ)) ^ (m - p)) *
          ((divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w) =
        (p.factorial : ℂ) / (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1) := by
    intro j p hp
    have hp' := Finset.mem_range.1 hp
    have hid := congrArg (eval w) (poly_laplace_identity (((j : ℕ) : ℂ) * (T : ℂ)) p
      (∑ j, n j) (chiPoly k T n) (ep_chi_dvd n j hp') (ep_chi_natDegree n))
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, eval_finsetSum] at hid
    have hne : (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (hw j))
    rw [show (∑ m ∈ range (∑ j, n j), ((m.descFactorial p : ℂ) * (((j : ℕ) : ℂ) * (T : ℂ)) ^ (m - p)) *
          ((divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w)) =
        (∑ m ∈ range (∑ j, n j), ((m.descFactorial p : ℂ) * (((j : ℕ) : ℂ) * (T : ℂ)) ^ (m - p)) *
          (divX^[m + 1] (chiPoly k T n)).eval w) / (chiPoly k T n).eval w by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun m _ => by ring]
    rw [eq_div_iff hne, div_mul_eq_mul_div, div_eq_iff hχ]
    linear_combination hid
  unfold laplaceY
  simp_rw [ep_iteratedDeriv hR, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← key j p hp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

lemma ep_circleIntegrable_sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → ℂ} {c : ℂ} {r : ℝ}
    (h : ∀ i ∈ s, CircleIntegrable (f i) c r) :
    CircleIntegrable (fun z => ∑ i ∈ s, f i z) c r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

open Classical in
/-- Laplace inversion over a circle: `∮ e^{sw} Y(w) dw = 2πi ∑_{jT inside} R_j(s) e^{jTs}`. -/
lemma ep_circleIntegral {k : ℕ} {T : ℝ} {R : Fin (k + 1) → ℂ[X]} {n : Fin (k + 1) → ℕ}
    (hR : ∀ j, (R j).degree < n j) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hfr : ∀ j : Fin (k + 1), ((j : ℕ) : ℂ) * (T : ℂ) ∈ ball c r ∨
      ((j : ℕ) : ℂ) * (T : ℂ) ∉ closedBall c r) (s : ℂ) :
    (∮ w in C(c, r), cexp (s * w) * laplaceY k T R n w) =
      2 * π * I * ∑ j ∈ univ.filter (fun j : Fin (k + 1) => ((j : ℕ) : ℂ) * (T : ℂ) ∈ ball c r),
        (R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s) := by
  -- no frequency lies on the circle
  have hsph : ∀ w ∈ sphere c r, ∀ j : Fin (k + 1), w ≠ ((j : ℕ) : ℂ) * (T : ℂ) := by
    intro w hw j hj
    rcases hfr j with h | h
    · have h1 := mem_sphere.1 hw
      rw [← hj, mem_ball] at h; linarith
    · rw [← hj] at h; exact h (sphere_subset_closedBall hw)
  have hcongr : Set.EqOn (fun w => cexp (s * w) * laplaceY k T R n w)
      (fun w => ∑ j : Fin (k + 1), ∑ p ∈ range (n j), ((R j).coeff p * (p.factorial : ℂ)) *
        (cexp (s * w) / (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1))) (sphere c r) := by
    intro w hw
    simp only
    rw [ep_laplaceY_eq hR (hsph w hw), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring
  have hint : ∀ (j : Fin (k + 1)) (p : ℕ), CircleIntegrable
      (fun w => ((R j).coeff p * (p.factorial : ℂ)) *
        (cexp (s * w) / (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1))) c r := by
    intro j p
    apply ContinuousOn.circleIntegrable hr.le
    intro w hw
    have : w - ((j : ℕ) : ℂ) * (T : ℂ) ≠ 0 := sub_ne_zero.2 (hsph w hw j)
    have hc : ContinuousAt (fun w => ((R j).coeff p * (p.factorial : ℂ)) *
        (cexp (s * w) / (w - ((j : ℕ) : ℂ) * (T : ℂ)) ^ (p + 1))) w :=
      continuousAt_const.mul ((by fun_prop : ContinuousAt (fun w => cexp (s * w)) w).div
        (by fun_prop) (pow_ne_zero _ this))
    exact hc.continuousWithinAt
  rw [circleIntegral.integral_congr hr.le hcongr, circleIntegral.integral_fun_sum
    (fun j _ => ?_)]
  swap
  · exact ep_circleIntegrable_sum _ fun p _ => hint j p
  rw [Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleIntegral.integral_fun_sum (fun p _ => hint j p)]
  simp_rw [circleIntegral.integral_const_mul]
  split_ifs with hin
  · rw [ep_eval_eq (hR j), Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [circleIntegral_exp_div_sub_pow hr hin]
    have : (p.factorial : ℂ) ≠ 0 := by exact_mod_cast p.factorial_ne_zero
    field_simp
  · have hout := (hfr j).resolve_left hin
    simp [circleIntegral_exp_div_sub_pow_of_notMem hr hout]

lemma ep_norm_freq {T : ℝ} (hT : 0 ≤ T) (j : ℕ) : ‖((j : ℂ)) * (T : ℂ)‖ = j * T := by
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hT]

lemma ep_norm_freq_sub {T : ℝ} (hT : 0 ≤ T) (i j : ℕ) :
    ‖(i : ℂ) * (T : ℂ) - (j : ℂ) * (T : ℂ)‖ = |(i : ℝ) - j| * T := by
  rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hT]
  congr 1
  rw [show (i : ℂ) - (j : ℂ) = (((i : ℝ) - j : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs]

lemma ep_norm_exp_le {s w : ℂ} {a b : ℝ} (hs : ‖s‖ ≤ a) (hw : ‖w‖ ≤ b) (ha : 0 ≤ a) :
    ‖cexp (s * w)‖ ≤ Real.exp (a * b) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  calc (s * w).re ≤ ‖s * w‖ := Complex.re_le_norm _
    _ = ‖s‖ * ‖w‖ := norm_mul _ _
    _ ≤ a * b := mul_le_mul hs hw (norm_nonneg _) ha

/-- `∑_{m<N} m! (c/N)^m ≤ N · max(1, …)`-type bound: each term of `∑_{m<N} m! x^m` is at most
`max 1 ((N x)^N)`. -/
lemma ep_factorial_sum_le {N : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    ∑ m ∈ range N, (m.factorial : ℝ) * x ^ m ≤ N * max 1 ((N * x) ^ N) := by
  have hterm : ∀ m ∈ range N, (m.factorial : ℝ) * x ^ m ≤ max 1 ((N * x) ^ N) := by
    intro m hm
    have hmN := Finset.mem_range.1 hm
    have h1 : (m.factorial : ℝ) ≤ (N : ℝ) ^ m := by
      have := Nat.factorial_le_pow m
      calc (m.factorial : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast this
        _ ≤ (N : ℝ) ^ m := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hmN.le) _
    calc (m.factorial : ℝ) * x ^ m ≤ (N : ℝ) ^ m * x ^ m :=
          mul_le_mul_of_nonneg_right h1 (pow_nonneg hx _)
      _ = (N * x) ^ m := (mul_pow _ _ _).symm
      _ ≤ max 1 ((N * x) ^ N) := by
          rcases le_or_gt (N * x) 1 with h | h
          · exact (pow_le_one₀ (by positivity) h).trans (le_max_left _ _)
          · exact (pow_le_pow_right₀ h.le hmN.le).trans (le_max_right _ _)
  calc ∑ m ∈ range N, (m.factorial : ℝ) * x ^ m ≤ ∑ _m ∈ range N, max 1 ((N * x) ^ N) :=
        Finset.sum_le_sum hterm
    _ = N * max 1 ((N * x) ^ N) := by simp

/-- **Lemma 5.1.** -/
theorem expPoly_bound {k : ℕ} {T : ℝ} (hT : 0 < T) (n : Fin (k + 1) → ℕ) (R : Fin (k + 1) → ℂ[X])
    (hR : ∀ j, (R j).degree < n j) {M : ℝ}
    (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly k T R s‖ ≤ M) :
    (∀ s : ℂ, ‖s‖ ≤ 5 → ‖expPoly k T R s‖ ≤
      ((∑ j, n j : ℕ) : ℝ) * 3 ^ (∑ j, n j) *
        Real.exp (5 * max (2 * k * T) (2 * ((∑ j, n j : ℕ) : ℝ))) * M) ∧
    (∀ j : Fin (k + 1), ∀ s : ℂ, ‖s‖ ≤ 4 →
      ‖(R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)‖ ≤
        2 * ((∑ j, n j : ℕ) : ℝ) * (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ (Finset.univ.sup n) *
          Real.exp ((4 * k + 2) * T) *
          max 1 ((4 * ((∑ j, n j : ℕ) : ℝ) / T) ^ (∑ j, n j)) * M) := by
  classical
  set N := ∑ j, n j with hNdef
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hy := ep_cauchy hM
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have hn : ∀ j, n j = 0 := fun j => by
      have := Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ j)
      omega
    have hRz : ∀ j, R j = 0 := fun j => by
      have h := hR j
      rw [hn j, Nat.cast_zero] at h
      exact Polynomial.degree_eq_bot.1 (Nat.WithBot.lt_zero_iff.1 h)
    refine ⟨fun s _ => ?_, fun j s _ => ?_⟩
    · simp [expPoly, hRz, hN0]
    · simp [hRz j, hN0]
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hT0 := hT.le
  -- the integrand bound shared by both parts
  have hYbound : ∀ w : ℂ, ∀ B : ℕ → ℝ,
      (∀ m, ‖(divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w‖ ≤ B m) →
      ‖laplaceY k T R n w‖ ≤ ∑ m ∈ range N, m.factorial * 2 ^ m * M * B m := by
    intro w B hB
    unfold laplaceY
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (hy m) (hB m) (norm_nonneg _) (by positivity)
  constructor
  · -- (a): the big circle
    intro s hs
    set ϱ := max (2 * k * T) (2 * (N : ℝ)) with hϱdef
    have hϱN : 2 * (N : ℝ) ≤ ϱ := le_max_right _ _
    have hϱk : 2 * k * T ≤ ϱ := le_max_left _ _
    have hϱ0 : 0 < ϱ := by linarith
    have hmem : ∀ j : Fin (k + 1), ((j : ℕ) : ℂ) * (T : ℂ) ∈ ball (0 : ℂ) ϱ := by
      intro j
      rw [mem_ball_zero_iff, ep_norm_freq hT0]
      have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
      nlinarith
    have hint := ep_circleIntegral hR hϱ0 (fun j => Or.inl (hmem j)) s
    rw [Finset.filter_true_of_mem (fun j _ => hmem j)] at hint
    have hbd : ∀ w ∈ sphere (0 : ℂ) ϱ, ‖cexp (s * w) * laplaceY k T R n w‖ ≤
        Real.exp (5 * ϱ) * ∑ m ∈ range N, m.factorial * 2 ^ m * M * (3 ^ N / ϱ ^ (m + 1)) := by
      intro w hw
      have hwn : ‖w‖ = ϱ := by simpa using hw
      rw [norm_mul]
      exact mul_le_mul (ep_norm_exp_le hs hwn.le (by norm_num))
        (hYbound w _ fun m => chiPoly_bound_big hT0 n hϱk hϱ0 hwn m) (norm_nonneg _)
        (Real.exp_pos _).le
    have h1 := circleIntegral.norm_integral_le_of_norm_le_const hϱ0.le hbd
    rw [hint, norm_mul, show ‖2 * (π : ℂ) * I‖ = 2 * π by
      simp [abs_of_pos Real.pi_pos]] at h1
    have hsum : ∑ m ∈ range N, (m.factorial : ℝ) * 2 ^ m * M * (3 ^ N / ϱ ^ (m + 1)) ≤
        3 ^ N * M / ϱ * N := by
      have h2 : ∑ m ∈ range N, (m.factorial : ℝ) * 2 ^ m * M * (3 ^ N / ϱ ^ (m + 1)) =
          3 ^ N * M / ϱ * ∑ m ∈ range N, (m.factorial : ℝ) * (2 / ϱ) ^ m := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [div_pow, pow_succ]; field_simp
      have h3 : ∑ m ∈ range N, (m.factorial : ℝ) * (2 / ϱ) ^ m ≤ N := by
        have := ep_factorial_sum_le (N := N) (x := 2 / ϱ) (by positivity)
        have h4 : (N : ℝ) * (2 / ϱ) ≤ 1 := by rw [mul_div_assoc', div_le_one hϱ0]; linarith
        have h5 : (N * (2 / ϱ)) ^ N ≤ 1 := pow_le_one₀ (by positivity) h4
        rw [max_eq_left h5, mul_one] at this
        exact this
      rw [h2]
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hfin : 2 * π * ‖expPoly k T R s‖ ≤ 2 * π * (ϱ * (Real.exp (5 * ϱ) * (3 ^ N * M / ϱ * N))) := by
      calc 2 * π * ‖expPoly k T R s‖ ≤ 2 * π * ϱ * (Real.exp (5 * ϱ) *
            ∑ m ∈ range N, m.factorial * 2 ^ m * M * (3 ^ N / ϱ ^ (m + 1))) := h1
        _ ≤ 2 * π * ϱ * (Real.exp (5 * ϱ) * (3 ^ N * M / ϱ * N)) := by gcongr
        _ = _ := by ring
    have := le_of_mul_le_mul_left hfin (by positivity)
    calc ‖expPoly k T R s‖ ≤ ϱ * (Real.exp (5 * ϱ) * (3 ^ N * M / ϱ * N)) := this
      _ = N * 3 ^ N * Real.exp (5 * ϱ) * M := by field_simp
  · -- (b): the small circles
    intro j s hs
    set Q := (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ (Finset.univ.sup n) with hQ
    have hQ1 : 1 ≤ Q := one_le_pow₀ (by
      have : (1 : ℝ) ≤ 2 ^ (4 * k + 2) := one_le_pow₀ (by norm_num)
      nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    have hT2 : 0 < T / 2 := by linarith
    have hfr : ∀ i : Fin (k + 1), ((i : ℕ) : ℂ) * (T : ℂ) ∈ ball (((j : ℕ) : ℂ) * (T : ℂ)) (T / 2) ∨
        ((i : ℕ) : ℂ) * (T : ℂ) ∉ closedBall (((j : ℕ) : ℂ) * (T : ℂ)) (T / 2) := by
      intro i
      by_cases hij : i = j
      · left; rw [hij]; exact mem_ball_self hT2
      · right
        rw [mem_closedBall, dist_eq_norm, ep_norm_freq_sub hT0, not_le]
        have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
        have : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
          rcases Nat.lt_or_gt_of_ne hne with h | h
          · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
            rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
            rw [abs_of_nonneg (by linarith)]; linarith
        nlinarith
    have hint := ep_circleIntegral hR hT2 hfr s
    have hfilt : univ.filter (fun i : Fin (k + 1) =>
        ((i : ℕ) : ℂ) * (T : ℂ) ∈ ball (((j : ℕ) : ℂ) * (T : ℂ)) (T / 2)) = {j} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        by_contra hij
        rcases hfr i with h' | h'
        · rw [mem_ball, dist_eq_norm, ep_norm_freq_sub hT0] at h'
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
          have : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)| := by
            rcases Nat.lt_or_gt_of_ne hne with h | h
            · have : ((i : ℕ) : ℝ) + 1 ≤ (j : ℕ) := by exact_mod_cast h
              rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
            · have : ((j : ℕ) : ℝ) + 1 ≤ (i : ℕ) := by exact_mod_cast h
              rw [abs_of_nonneg (by linarith)]; linarith
          nlinarith
        · exact h' (ball_subset_closedBall h)
      · rintro rfl; exact mem_ball_self hT2
    rw [hfilt, Finset.sum_singleton] at hint
    have hj : ((j : ℕ) : ℝ) ≤ k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
    have hbd : ∀ w ∈ sphere (((j : ℕ) : ℂ) * (T : ℂ)) (T / 2),
        ‖cexp (s * w) * laplaceY k T R n w‖ ≤
          Real.exp ((4 * k + 2) * T) * ∑ m ∈ range N, m.factorial * 2 ^ m * M *
            (2 * Q * (2 / T) ^ (m + 1)) := by
      intro w hw
      have hwn : ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ = T / 2 := by simpa [dist_eq_norm] using hw
      have hw' : ‖w‖ ≤ (k + 1 / 2) * T := by
        calc ‖w‖ = ‖(w - ((j : ℕ) : ℂ) * (T : ℂ)) + ((j : ℕ) : ℂ) * (T : ℂ)‖ := by ring_nf
          _ ≤ ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ + ‖((j : ℕ) : ℂ) * (T : ℂ)‖ := norm_add_le _ _
          _ = T / 2 + (j : ℕ) * T := by rw [hwn, ep_norm_freq hT0]
          _ ≤ (k + 1 / 2) * T := by nlinarith
      rw [norm_mul]
      refine mul_le_mul ((ep_norm_exp_le hs hw' (by norm_num)).trans (le_of_eq ?_))
        (hYbound w _ fun m => chiPoly_bound_small hT n j hwn m) (norm_nonneg _)
        (Real.exp_pos _).le
      congr 1; ring
    have h1 := circleIntegral.norm_integral_le_of_norm_le_const hT2.le hbd
    rw [hint, norm_mul, show ‖2 * (π : ℂ) * I‖ = 2 * π by
      simp [abs_of_pos Real.pi_pos]] at h1
    have hsum : T / 2 * ∑ m ∈ range N, (m.factorial : ℝ) * 2 ^ m * M * (2 * Q * (2 / T) ^ (m + 1)) ≤
        2 * Q * M * (N * max 1 ((4 * N / T) ^ N)) := by
      have h2 : T / 2 * ∑ m ∈ range N, (m.factorial : ℝ) * 2 ^ m * M * (2 * Q * (2 / T) ^ (m + 1)) =
          2 * Q * M * ∑ m ∈ range N, (m.factorial : ℝ) * (4 / T) ^ m := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [div_pow, div_pow, pow_succ, show (4 : ℝ) ^ m = 2 ^ m * 2 ^ m by
          rw [← mul_pow]; norm_num]
        field_simp
        ring
      have h3 := ep_factorial_sum_le (N := N) (x := 4 / T) (by positivity)
      rw [h2, show (N : ℝ) * (4 / T) = 4 * N / T by ring] at *
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have hfin : 2 * π * ‖(R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)‖ ≤
        2 * π * (Real.exp ((4 * k + 2) * T) * (2 * Q * M * (N * max 1 ((4 * N / T) ^ N)))) := by
      calc 2 * π * ‖(R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)‖
          ≤ 2 * π * (T / 2) * (Real.exp ((4 * k + 2) * T) * ∑ m ∈ range N,
              m.factorial * 2 ^ m * M * (2 * Q * (2 / T) ^ (m + 1))) := h1
        _ = 2 * π * (Real.exp ((4 * k + 2) * T) * (T / 2 * ∑ m ∈ range N,
              m.factorial * 2 ^ m * M * (2 * Q * (2 / T) ^ (m + 1)))) := by ring
        _ ≤ _ := by gcongr
    have := le_of_mul_le_mul_left hfin (by positivity)
    calc ‖(R j).eval s * cexp ((((j : ℕ) : ℂ) * (T : ℂ)) * s)‖
        ≤ Real.exp ((4 * k + 2) * T) * (2 * Q * M * (N * max 1 ((4 * N / T) ^ N))) := this
      _ = _ := by ring

end Singmaster
