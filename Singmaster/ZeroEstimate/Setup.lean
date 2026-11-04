module

public import Singmaster.ExpPoly.Main
public import Singmaster.ZeroEstimate.Analytic
public import Singmaster.ZeroEstimate.ChangeVar
public import Singmaster.ZeroEstimate.Numerics

@[expose] public section

/-!
# Proposition 6.1: the functions `G` and `G₀`

The data of Proposition 6.1, except `F` and the set `Z`, is bundled in `ZeroData`. With
`a₀ = a₀ k`, `u₀ = 1/x₀`, `ρ = u₀/a₀` and `T = L/(a₀ x₀) = L ρ`, we put `u(s) = u₀ + ρ s`,
`K(s) = e^{κ(u(s)) - κ(u₀)}`, `q_j(s) = e^{j(L u₀ + κ(u₀))} Q_j(u(s))` (`Q_j = cvP k d A j`) and
`G(s) = ∑_j q_j(s) e^{jTs} K(s)^j`, as in (6.2). Truncating `K^j` to its Taylor polynomial `Π_j`
of degree `J = ⌈2T⌉` gives the exponential polynomial `G₀ = ∑_j q_j Π_j e^{jTs}` of Lemma 5.1.
This file proves (6.4) and (6.7): `G₀` is close to `G` on `|s| ≤ 4`.
-/

open Complex Polynomial Metric Real Finset

namespace Singmaster

/-! ## The data -/

/-- The data of Proposition 6.1, except `F` and the set `Z`. -/
structure ZeroData where
  k : ℕ
  d : ℕ
  L : ℝ
  x₀ : ℝ
  η : ℝ
  κ : ℂ → ℂ
  A : Fin (k + 1) → ℂ[X]
  hk : 1 ≤ k
  hx : 1 ≤ x₀
  hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ L / (a₀ k * x₀)
  hd : (d : ℝ) ≤ 2 * (L / (a₀ k * x₀))
  hη : k * η ≤ 0.09
  hκd : DifferentiableOn ℂ κ (Metric.closedBall ((x₀ : ℂ)⁻¹) (x₀⁻¹ / 2))
  hκb : ∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) (x₀⁻¹ / 2), ‖κ u - κ (x₀ : ℂ)⁻¹‖ ≤ η
  hA : ∃ b, A b ≠ 0
  hAd : ∀ b, (A b).natDegree ≤ d

namespace ZeroData

variable (D : ZeroData)

/-- `T = L/(a₀ x₀)`. -/
noncomputable def T : ℝ := D.L / (a₀ D.k * D.x₀)

/-- `ρ = x₀⁻¹/a₀`. -/
noncomputable def ρ : ℝ := D.x₀⁻¹ / a₀ D.k

/-- `u₀ = 1/x₀`. -/
noncomputable def u₀ : ℂ := (D.x₀ : ℂ)⁻¹

/-- `K(s) = e^{κ(u₀ + ρ s) - κ(u₀)}`. -/
noncomputable def K (s : ℂ) : ℂ := cexp (D.κ (D.u₀ + (D.ρ : ℂ) * s) - D.κ D.u₀)

/-- `c_j = e^{j (L u₀ + κ(u₀))}`. -/
noncomputable def cc (j : ℕ) : ℂ := cexp ((j : ℂ) * ((D.L : ℂ) * D.u₀ + D.κ D.u₀))

/-- The affine map `s ↦ u₀ + ρ s`. -/
noncomputable def lin : ℂ[X] := C D.u₀ + C (D.ρ : ℂ) * X

/-- `q_j(s) = c_j Q_j(u₀ + ρ s)`. -/
noncomputable def q (j : Fin (D.k + 1)) : ℂ[X] := C (D.cc j) * (cvP D.k D.d D.A j).comp D.lin

/-- The truncation degree `J = ⌈2T⌉`. -/
noncomputable def J : ℕ := ⌈2 * D.T⌉₊

/-- `δ' = (1/5) (10/a₀)^{J+1}`. -/
noncomputable def δ' : ℝ := (1 / 5) * (10 / a₀ D.k) ^ (D.J + 1)

/-- `Π_j`: `1` for `j = 0`, the degree-`J` Taylor polynomial of `K^j` otherwise. -/
noncomputable def Pi (j : Fin (D.k + 1)) : ℂ[X] :=
  if (j : ℕ) = 0 then 1 else
    ∑ n ∈ range (D.J + 1),
      C (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun s => D.K s ^ (j : ℕ)) 0) * X ^ n

/-- The polynomials `R_j = q_j Π_j` of `G₀`. -/
noncomputable def R (j : Fin (D.k + 1)) : ℂ[X] := D.q j * D.Pi j

/-- The degree bounds `ν_j` of Lemma 5.1. -/
noncomputable def n (j : Fin (D.k + 1)) : ℕ := if (j : ℕ) = 0 then D.d + D.k + 1 else D.d + D.k + D.J + 1

/-- `G(s) = ∑_j q_j(s) e^{jTs} K(s)^j`. -/
noncomputable def G (s : ℂ) : ℂ :=
  ∑ j : Fin (D.k + 1), (D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s) * D.K s ^ (j : ℕ)

/-! ## Basic facts -/

lemma k_ge : (1 : ℝ) ≤ D.k := by exact_mod_cast D.hk

lemma a_ge : (280 : ℝ) ≤ a₀ D.k := by
  have := a₀_ge D.k
  have := D.k_ge
  linarith

lemma a_pos : 0 < a₀ D.k := a₀_pos D.k

lemma x₀_pos : 0 < D.x₀ := by linarith [D.hx]

lemma T_ge : 10 * ((D.k : ℝ) + 1) ^ 2 ≤ D.T := D.hT

lemma T_ge40 : (40 : ℝ) ≤ D.T := by
  have h1 := D.k_ge
  have h2 : (2 : ℝ) ^ 2 ≤ ((D.k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  linarith [D.T_ge]

lemma T_pos : 0 < D.T := by linarith [D.T_ge40]

lemma d_le : (D.d : ℝ) ≤ 2 * D.T := D.hd

lemma ρ_pos : 0 < D.ρ := by
  unfold ρ
  have := D.x₀_pos
  have := D.a_pos
  positivity

lemma T_eq : D.T = D.L * D.ρ := by
  unfold T ρ
  have := D.x₀_pos.ne'
  have := D.a_pos.ne'
  field_simp

lemma ρ_mul_a : D.ρ * (a₀ D.k / 2) = D.x₀⁻¹ / 2 := by
  unfold ρ
  have := D.a_pos.ne'
  field_simp

lemma η_nonneg : 0 ≤ D.η := by
  have h := D.hκb ((D.x₀ : ℂ)⁻¹) (mem_closedBall_self (by
    have := D.x₀_pos
    positivity))
  simpa using (norm_nonneg _).trans h

/-! ## The function `K` -/

lemma u_mem {s : ℂ} (hs : s ∈ closedBall (0 : ℂ) (a₀ D.k / 2)) :
    D.u₀ + (D.ρ : ℂ) * s ∈ closedBall ((D.x₀ : ℂ)⁻¹) (D.x₀⁻¹ / 2) := by
  rw [mem_closedBall, dist_eq_norm, u₀, add_sub_cancel_left, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg D.ρ_pos.le, ← D.ρ_mul_a]
  rw [mem_closedBall_zero_iff] at hs
  exact mul_le_mul_of_nonneg_left hs D.ρ_pos.le

lemma K_diff : DifferentiableOn ℂ D.K (closedBall 0 (a₀ D.k / 2)) := by
  have h1 : DifferentiableOn ℂ (fun s : ℂ => D.κ (D.u₀ + (D.ρ : ℂ) * s))
      (closedBall 0 (a₀ D.k / 2)) :=
    D.hκd.comp (by fun_prop) (fun s hs => D.u_mem hs)
  unfold K
  exact (h1.sub_const _).cexp

lemma Kpow_eq (s : ℂ) (j : ℕ) :
    D.K s ^ j = cexp ((j : ℂ) * (D.κ (D.u₀ + (D.ρ : ℂ) * s) - D.κ D.u₀)) := by
  rw [Complex.exp_nat_mul]; rfl

lemma _root_.Singmaster.ze_exp_near_one {x : ℂ} (hx : ‖x‖ ≤ 0.09) : ‖cexp x - 1‖ ≤ 1 / 10 := by
  have h := Complex.norm_exp_sub_one_sub_id_le (x := x) (by linarith)
  have h2 : ‖cexp x - 1‖ ≤ ‖cexp x - 1 - x‖ + ‖x‖ := by
    calc ‖cexp x - 1‖ = ‖(cexp x - 1 - x) + x‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  have h3 : ‖x‖ ^ 2 ≤ 0.09 * 0.09 := by
    have := norm_nonneg x
    nlinarith
  linarith

lemma Kpow_near (j : Fin (D.k + 1)) {s : ℂ} (hs : s ∈ closedBall (0 : ℂ) (a₀ D.k / 2)) :
    ‖D.K s ^ (j : ℕ) - 1‖ ≤ 1 / 10 := by
  rw [D.Kpow_eq]
  apply ze_exp_near_one
  rw [norm_mul, Complex.norm_natCast]
  have h1 := D.hκb _ (D.u_mem hs)
  have hj : ((j : ℕ) : ℝ) ≤ D.k := by exact_mod_cast Nat.lt_succ_iff.1 j.isLt
  have := D.η_nonneg
  calc ((j : ℕ) : ℝ) * ‖D.κ (D.u₀ + (D.ρ : ℂ) * s) - D.κ D.u₀‖ ≤ D.k * D.η :=
        mul_le_mul hj h1 (norm_nonneg _) (Nat.cast_nonneg _)
    _ ≤ 0.09 := D.hη

/-! ## Taylor truncation -/

lemma Pi_eval_taylor (j : Fin (D.k + 1)) (hj : (j : ℕ) ≠ 0) (s : ℂ) :
    (D.Pi j).eval s = ∑ n ∈ range (D.J + 1),
      (((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun s => D.K s ^ (j : ℕ)) 0) * s ^ n := by
  unfold Pi
  simp [hj, eval_finsetSum]

lemma δ'_nonneg : 0 ≤ D.δ' := by
  unfold δ'; have := D.a_pos; positivity

lemma Pi_bounds (j : Fin (D.k + 1)) {s : ℂ} (hs : ‖s‖ ≤ 5) :
    ‖D.K s ^ (j : ℕ) - (D.Pi j).eval s‖ ≤ D.δ' ∧ 1 / 2 ≤ ‖(D.Pi j).eval s‖ := by
  by_cases hj : (j : ℕ) = 0
  · have : D.Pi j = 1 := by unfold Pi; simp [hj]
    rw [this, hj, eval_one, pow_zero, sub_self, norm_zero, norm_one]
    exact ⟨D.δ'_nonneg, by norm_num⟩
  · have hR : (20 : ℝ) ≤ a₀ D.k / 2 := by linarith [D.a_ge]
    have hdiff : DifferentiableOn ℂ (fun s => D.K s ^ (j : ℕ)) (closedBall 0 (a₀ D.k / 2)) :=
      D.K_diff.pow _
    have h := taylor_trunc hR hdiff (fun s hs => D.Kpow_near j hs) D.J s hs
    rw [D.Pi_eval_taylor j hj]
    have e : (5 : ℝ) / (a₀ D.k / 2) = 10 / a₀ D.k := by
      have := D.a_pos.ne'; field_simp; norm_num
    rw [e] at h
    exact h

/-! ## Degrees -/

lemma lin_natDegree : D.lin.natDegree ≤ 1 := by
  unfold lin; compute_degree

lemma q_natDegree (j : Fin (D.k + 1)) : (D.q j).natDegree ≤ D.d + D.k := by
  unfold q
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_comp_le.trans ?_
  have h1 := cvP_natDegree_le D.A D.hAd j
  have h2 := D.lin_natDegree
  calc _ ≤ (D.d + D.k) * 1 := Nat.mul_le_mul h1 h2
    _ = _ := mul_one _

lemma Pi_natDegree (j : Fin (D.k + 1)) :
    (D.Pi j).natDegree ≤ if (j : ℕ) = 0 then 0 else D.J := by
  unfold Pi
  split_ifs with hj
  · simp
  · exact natDegree_sum_le_of_forall_le _ _ fun n hn => (natDegree_C_mul_X_pow_le _ _).trans
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))

lemma R_degree (j : Fin (D.k + 1)) : (D.R j).degree < D.n j := by
  have h : (D.R j).natDegree < D.n j := by
    have h1 := natDegree_mul_le (p := D.q j) (q := D.Pi j)
    have h2 := D.q_natDegree j
    have h3 := D.Pi_natDegree j
    unfold R n
    split_ifs at h3 ⊢ <;> omega
  exact degree_le_natDegree.trans_lt (by exact_mod_cast h)

lemma N_eq : ∑ j, D.n j = (D.d + D.k + 1) + D.k * (D.d + D.k + D.J + 1) := by
  rw [Fin.sum_univ_succ]
  have h0 : D.n 0 = D.d + D.k + 1 := by unfold n; simp
  have hs : ∀ i : Fin D.k, D.n i.succ = D.d + D.k + D.J + 1 := by
    intro i; unfold n; simp
  rw [h0, Finset.sum_congr rfl (fun i _ => hs i), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

lemma J_ge : 2 * D.T ≤ D.J := Nat.le_ceil _

lemma J_le : (D.J : ℝ) ≤ 2 * D.T + 1 := (Nat.ceil_lt_add_one (by linarith [D.T_pos])).le

lemma N_le : ((∑ j, D.n j : ℕ) : ℝ) ≤ (4 * D.k + 3) * D.T := by
  rw [D.N_eq]; push_cast
  have hk := D.k_ge
  have hd := D.d_le
  have hJ := D.J_le
  have hT := D.T_ge
  have h1 : (D.k : ℝ) * D.d ≤ D.k * (2 * D.T) := mul_le_mul_of_nonneg_left hd (by linarith)
  have h2 : (D.k : ℝ) * D.J ≤ D.k * (2 * D.T + 1) := mul_le_mul_of_nonneg_left hJ (by linarith)
  have h3 : (D.k : ℝ) ^ 2 + 3 * D.k + 1 ≤ D.T := by nlinarith
  nlinarith

lemma N_ge : 2 * D.k * D.T ≤ ((∑ j, D.n j : ℕ) : ℝ) := by
  rw [D.N_eq]; push_cast
  have hJ := D.J_ge
  have h1 : (D.k : ℝ) * (2 * D.T) ≤ D.k * D.J := mul_le_mul_of_nonneg_left hJ (Nat.cast_nonneg _)
  have : (0 : ℝ) ≤ D.d := Nat.cast_nonneg _
  have : (0 : ℝ) ≤ D.k := Nat.cast_nonneg _
  nlinarith

lemma nmax_le : ((Finset.univ.sup D.n : ℕ) : ℝ) ≤ 5 * D.T := by
  have h : Finset.univ.sup D.n ≤ D.d + D.k + D.J + 1 :=
    Finset.sup_le fun j _ => by unfold n; split_ifs <;> omega
  have h' : ((Finset.univ.sup D.n : ℕ) : ℝ) ≤ D.d + D.k + D.J + 1 := by exact_mod_cast h
  have hd := D.d_le
  have hJ := D.J_le
  have hT := D.T_ge
  have hk := D.k_ge
  nlinarith

/-! ## `G` in terms of the `Q_j` -/

lemma exp_identity (j : ℕ) (s : ℂ) :
    D.cc j * cexp (((j : ℂ) * (D.T : ℂ)) * s) * D.K s ^ j =
      cexp ((D.L : ℂ) * (D.u₀ + (D.ρ : ℂ) * s) + D.κ (D.u₀ + (D.ρ : ℂ) * s)) ^ j := by
  rw [D.Kpow_eq, ← Complex.exp_nat_mul, cc, ← Complex.exp_add, ← Complex.exp_add, D.T_eq]
  congr 1
  push_cast
  ring

lemma q_eval (j : Fin (D.k + 1)) (s : ℂ) :
    (D.q j).eval s = D.cc j * (cvP D.k D.d D.A j).eval (D.u₀ + (D.ρ : ℂ) * s) := by
  simp [q, lin, eval_comp]

lemma G_eq (s : ℂ) : D.G s = ∑ j : Fin (D.k + 1),
    (cvP D.k D.d D.A j).eval (D.u₀ + (D.ρ : ℂ) * s) *
      cexp ((D.L : ℂ) * (D.u₀ + (D.ρ : ℂ) * s) + D.κ (D.u₀ + (D.ρ : ℂ) * s)) ^ (j : ℕ) := by
  unfold G
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [D.q_eval, ← D.exp_identity]
  ring

/-! ## The zeros -/

/-- The point `s_z = (1/z - u₀)/ρ`. -/
noncomputable def sz (z : ℂ) : ℂ := (z⁻¹ - D.u₀) / (D.ρ : ℂ)

lemma u_sz (z : ℂ) : D.u₀ + (D.ρ : ℂ) * D.sz z = z⁻¹ := by
  have : (D.ρ : ℂ) ≠ 0 := by exact_mod_cast D.ρ_pos.ne'
  unfold sz; field_simp; ring

lemma sz_inj {z w : ℂ} (h : D.sz z = D.sz w) : z = w := by
  have := congrArg (fun s => D.u₀ + (D.ρ : ℂ) * s) h
  simp only [D.u_sz] at this
  exact inv_injective this

lemma z_norm {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) : 3 * D.x₀ / 4 ≤ ‖z‖ := by
  have h1 : ‖(D.x₀ : ℂ)‖ ≤ ‖z‖ + ‖z - (D.x₀ : ℂ)‖ := by
    calc ‖(D.x₀ : ℂ)‖ = ‖z - (z - (D.x₀ : ℂ))‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  rw [Complex.norm_real, Real.norm_of_nonneg D.x₀_pos.le] at h1
  have h2 : D.x₀ / (4 * a₀ D.k) ≤ D.x₀ / 4 :=
    div_le_div_of_nonneg_left D.x₀_pos.le (by norm_num) (by linarith [D.a_ge])
  linarith

lemma z_ne_zero {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) : z ≠ 0 := by
  have hzn := D.z_norm hz
  have hx := D.x₀_pos
  intro h; rw [h, norm_zero] at hzn; linarith

lemma inv_sub_le {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) :
    ‖z⁻¹ - D.u₀‖ ≤ D.ρ / 3 := by
  have hzn := D.z_norm hz
  have hx := D.x₀_pos
  have hz0 := D.z_ne_zero hz
  have hx0 : (D.x₀ : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have e : z⁻¹ - D.u₀ = ((D.x₀ : ℂ) - z) / (z * D.x₀) := by unfold u₀; field_simp
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  rw [e, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hx.le, norm_sub_rev,
    div_le_iff₀ (by positivity)]
  have ha := D.a_pos
  calc ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k) := hz
    _ = D.ρ / 3 * (3 * D.x₀ / 4 * D.x₀) := by unfold ρ; field_simp
    _ ≤ D.ρ / 3 * (‖z‖ * D.x₀) := by
        have := D.ρ_pos
        gcongr

lemma sz_norm {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) : ‖D.sz z‖ ≤ 1 / 3 := by
  unfold sz
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg D.ρ_pos.le, div_le_iff₀ D.ρ_pos]
  have := D.inv_sub_le hz
  linarith

/-! ## `G - G₀` is small -/

lemma G_sub (s : ℂ) : D.G s - expPoly D.k D.T D.R s =
    ∑ j : Fin (D.k + 1), ((D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)) *
      (D.K s ^ (j : ℕ) - (D.Pi j).eval s) := by
  unfold G expPoly R
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul]; ring

lemma _root_.Singmaster.ze_fin_sum_le {k : ℕ} (f : Fin (k + 1) → ℝ) (C : ℝ) (h0 : f 0 ≤ 0)
    (h : ∀ i : Fin k, f i.succ ≤ C) : ∑ j, f j ≤ k * C := by
  rw [Fin.sum_univ_succ]
  have : ∑ i : Fin k, f i.succ ≤ ∑ _i : Fin k, C := Finset.sum_le_sum fun i _ => h i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  linarith

lemma G_sub_le {M : ℝ} (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M) {s : ℂ}
    (hs : ‖s‖ ≤ 4) : ‖D.G s - expPoly D.k D.T D.R s‖ ≤ M / 2 := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have L4 := (expPoly_bound D.T_pos D.n D.R D.R_degree hM).2
  set N := ∑ j, D.n j with hN
  set X : ℝ := 2 * (N : ℝ) * (((D.k : ℝ) + 1) * 2 ^ (4 * D.k + 2)) ^ (Finset.univ.sup D.n) *
      Real.exp ((4 * D.k + 2) * D.T) * max 1 ((4 * (N : ℝ) / D.T) ^ N) with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  have hXM : 0 ≤ 2 * (X * M) := by have := mul_nonneg hX0 hM0; linarith
  have hs5 : ‖s‖ ≤ 5 := by linarith
  have hterm : ∀ i : Fin D.k,
      ‖((D.q i.succ).eval s * cexp ((((i.succ : ℕ) : ℂ) * (D.T : ℂ)) * s)) *
        (D.K s ^ (i.succ : ℕ) - (D.Pi i.succ).eval s)‖ ≤ 2 * (X * M) * D.δ' := by
    intro i
    obtain ⟨hb1, hb2⟩ := D.Pi_bounds i.succ hs5
    have hR := L4 i.succ s hs
    rw [R, eval_mul, mul_right_comm, norm_mul] at hR
    rw [norm_mul]
    have hqe : ‖(D.q i.succ).eval s * cexp ((((i.succ : ℕ) : ℂ) * (D.T : ℂ)) * s)‖ ≤
        2 * (X * M) := by
      have := norm_nonneg ((D.q i.succ).eval s * cexp ((((i.succ : ℕ) : ℂ) * (D.T : ℂ)) * s))
      nlinarith
    exact mul_le_mul hqe hb1 (norm_nonneg _) hXM
  have h0 : ‖((D.q 0).eval s * cexp (((((0 : Fin (D.k + 1)) : ℕ) : ℂ) * (D.T : ℂ)) * s)) *
      (D.K s ^ ((0 : Fin (D.k + 1)) : ℕ) - (D.Pi 0).eval s)‖ ≤ 0 := by
    have : D.Pi 0 = 1 := by unfold Pi; simp
    simp [this]
  rw [D.G_sub]
  refine (norm_sum_le _ _).trans ?_
  refine (ze_fin_sum_le _ (2 * (X * M) * D.δ') h0 hterm).trans ?_
  have hnum := num_trunc D.hk D.T_ge D.N_le D.nmax_le D.J_ge
  have e : (D.k : ℝ) * (2 * (X * M) * D.δ') = (4 * D.k * N *
      (((D.k : ℝ) + 1) * 2 ^ (4 * D.k + 2)) ^ (Finset.univ.sup D.n) *
      Real.exp ((4 * D.k + 2) * D.T) * max 1 ((4 * N / D.T) ^ N) *
      ((1 / 5) * (10 / a₀ D.k) ^ (D.J + 1))) * M := by
    rw [hX, δ']; ring
  rw [e]
  have := mul_le_mul_of_nonneg_right hnum hM0
  linarith

/-! ## Analyticity of `G` -/

lemma G_diff : DifferentiableOn ℂ D.G (ball 0 (a₀ D.k / 2)) := by
  have hK : DifferentiableOn ℂ D.K (ball 0 (a₀ D.k / 2)) := D.K_diff.mono ball_subset_closedBall
  unfold G
  fun_prop

lemma G_analytic {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) : AnalyticOnNhd ℂ D.G (closedBall c 3) := by
  refine (D.G_diff.analyticOnNhd isOpen_ball).mono ?_
  intro s hs
  rw [mem_closedBall, dist_eq_norm] at hs
  rw [mem_ball_zero_iff]
  have : ‖s‖ ≤ ‖s - c‖ + ‖c‖ := by
    calc ‖s‖ = ‖(s - c) + c‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  linarith [D.a_ge]

/-! ## Nonvanishing of `G₀` -/

lemma _root_.Singmaster.ze_poly_eq_zero (p : ℂ[X]) (h : ∀ s : ℂ, ‖s‖ ≤ 1 → p.eval s = 0) :
    p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℂ) + 1)⁻¹) ?_ ?_
  · intro m n hmn
    simpa only [inv_inj, add_left_inj, Nat.cast_inj] using hmn
  · intro n
    apply h
    rw [norm_inv]
    have : ‖(n : ℂ) + 1‖ = (n : ℝ) + 1 := by
      rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [this]
    apply inv_le_one_of_one_le₀
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith

lemma R_ne_zero : ∃ j, D.R j ≠ 0 := by
  obtain ⟨j, hj⟩ := cvP_exists_ne_zero (d := D.d) D.A D.hA
  refine ⟨j, ?_⟩
  unfold R q
  refine mul_ne_zero (mul_ne_zero ?_ ?_) ?_
  · rw [Ne, C_eq_zero]; exact Complex.exp_ne_zero _
  · intro h
    rw [comp_eq_zero_iff] at h
    rcases h with h | ⟨_, h⟩
    · exact hj h
    · have := congrArg (fun p => p.coeff 1) h
      simp [lin] at this
      exact D.ρ_pos.ne' this
  · intro h
    have := (D.Pi_bounds j (s := 0) (by simp)).2
    rw [h, eval_zero, norm_zero] at this
    norm_num at this

lemma M_pos {M : ℝ} (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M) : 0 < M := by
  refine lt_of_not_ge fun hneg => ?_
  have L4 := (expPoly_bound D.T_pos D.n D.R D.R_degree hM).2
  obtain ⟨j, hj⟩ := D.R_ne_zero
  apply hj
  apply ze_poly_eq_zero
  intro s hs
  have h := L4 j s (by linarith)
  have hX : 0 ≤ 2 * ((∑ j, D.n j : ℕ) : ℝ) *
      (((D.k : ℝ) + 1) * 2 ^ (4 * D.k + 2)) ^ (Finset.univ.sup D.n) *
      Real.exp ((4 * D.k + 2) * D.T) *
      max 1 ((4 * ((∑ j, D.n j : ℕ) : ℝ) / D.T) ^ (∑ j, D.n j)) := by positivity
  have h2 := mul_nonpos_of_nonneg_of_nonpos hX hneg
  have h3 := le_antisymm (h.trans h2) (norm_nonneg _)
  rw [norm_eq_zero, mul_eq_zero] at h3
  exact h3.resolve_right (Complex.exp_ne_zero _)

end ZeroData

end Singmaster
