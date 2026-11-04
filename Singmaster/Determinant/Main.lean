module

public import Singmaster.Determinant.Schwarz

@[expose] public section

/-!
# Proposition 4.1: solutions in a short window lie on a curve

Let `k ≥ 1`, `d ≥ 0`, `x₀ ≥ 2`, `ℓ ≥ 0` and `D = (k+1)(d+1)`, and let `F` be holomorphic on
`|z - x₀| ≤ x₀/2` with `|F| ≤ 3 x₀ e^{2ℓ}` there. If every point `(n, m)` of a finite set `S`
satisfies `|m - x₀| ≤ r` (`windowRadius`) and `|F(m) - n| ≤ δ ≤ δ₃`, then there are polynomials
`A_0, …, A_k` of degree at most `d`, not all zero, with `∑_b A_b(m) n^b = 0` on `S`
(`solutions_on_curve`).

Each `D × D` determinant `det [(m_i - x₀)^a n_i^b]` is an integer. It differs from
`det [(m_i - x₀)^a F(m_i)^b]`, which is at most `e^{-1}` by `interpolation_det_le`, by at most
`1/2`, so it vanishes (`det_minor_zero`). The matrix therefore has a nonzero kernel vector
(`det_exists_mulVec_eq_zero`).
-/

open Real Metric Polynomial

namespace Singmaster

/-- The window radius `r` of Proposition 4.1. -/
noncomputable def windowRadius (x₀ k d : ℕ) (ℓ : ℝ) : ℝ :=
  ((x₀ : ℝ) / 2) ^ ((k : ℝ) / (k + 1)) *
    exp (-(2 * ℓ + log (3 * x₀) + 2 * log (((k : ℝ) + 1) * (d + 1)) + 1) / (d + 1))

/-- Gauss sum over `Fin n`. -/
lemma det_sum_fin (n : ℕ) : ∑ a : Fin n, ((a : ℕ) : ℝ) = n * (n - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (i:ℝ)) n]
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- `r / R` as a single exponential. -/
lemma det_ratio {x₀ k d : ℕ} {ℓ : ℝ} (hx₀ : 2 ≤ x₀) :
    windowRadius x₀ k d ℓ / ((x₀ : ℝ) / 2) =
      exp (log ((x₀ : ℝ) / 2) * ((k : ℝ) / (k + 1)) -
        (2 * ℓ + log (3 * x₀) + 2 * log (((k : ℝ) + 1) * (d + 1)) + 1) / (d + 1) -
        log ((x₀ : ℝ) / 2)) := by
  have hR : (0 : ℝ) < (x₀ : ℝ) / 2 := by
    have : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
    linarith
  rw [sub_eq_add_neg _ ((2 * ℓ + _ + _ + 1) / _), exp_sub, exp_add, exp_log hR, windowRadius,
    rpow_def_of_pos hR, neg_div]

/-- The product of the column bounds `R^a (3x₀e^{2ℓ})^b` as a single exponential. -/
lemma det_prod {x₀ k d : ℕ} {ℓ : ℝ} (hx₀ : 2 ≤ x₀) :
    ∏ j : Fin (d + 1) × Fin (k + 1),
        (((x₀ : ℝ) / 2) ^ (j.1 : ℕ) * (3 * x₀ * exp (2 * ℓ)) ^ (j.2 : ℕ)) =
      exp (log ((x₀ : ℝ) / 2) * ((k + 1) * ((d + 1) * d / 2)) +
        (2 * ℓ + log (3 * x₀)) * ((d + 1) * ((k + 1) * k / 2))) := by
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  have hR : (x₀ : ℝ) / 2 = exp (log ((x₀ : ℝ) / 2)) := (exp_log (by linarith)).symm
  have hE : 3 * (x₀ : ℝ) * exp (2 * ℓ) = exp (2 * ℓ + log (3 * x₀)) := by
    rw [exp_add, exp_log (by linarith)]; ring
  conv_lhs => rw [hE, hR]
  simp_rw [← exp_nat_mul, ← exp_add]
  rw [← exp_sum]
  congr 1
  rw [Finset.sum_add_distrib, Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, det_sum_fin]
  push_cast
  ring
/-- `D(D-1)/2` is computed exactly in `ℕ`. -/
lemma det_W (N : ℕ) (hN : 1 ≤ N) : ((N * (N - 1) / 2 : ℕ) : ℝ) = (N : ℝ) * ((N : ℝ) - 1) / 2 := by
  have h2 : 2 ∣ N * (N - 1) := even_iff_two_dvd.mp (Nat.even_mul_pred_self N)
  rw [Nat.cast_div h2 (by norm_num), Nat.cast_mul, Nat.cast_sub hN]
  push_cast; ring

/-- `N! ≤ N^N = exp (N log N)`. -/
lemma det_fact (N : ℕ) : (N.factorial : ℝ) ≤ exp ((N : ℝ) * log N) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  rw [exp_nat_mul, exp_log (by exact_mod_cast h)]
  exact_mod_cast Nat.factorial_le_pow N
/-- `0 < r`. -/
lemma det_r_pos {x₀ k d : ℕ} {ℓ : ℝ} (hx₀ : 2 ≤ x₀) : 0 < windowRadius x₀ k d ℓ := by
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  exact mul_pos (rpow_pos_of_pos (by linarith) _) (exp_pos _)

/-- `r ≤ R = x₀/2`. -/
lemma det_r_le {x₀ k d : ℕ} {ℓ : ℝ} (hx₀ : 2 ≤ x₀) (hℓ : 0 ≤ ℓ) :
    windowRadius x₀ k d ℓ ≤ (x₀ : ℝ) / 2 := by
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  have hR : (0 : ℝ) < (x₀ : ℝ) / 2 := by linarith
  rw [← div_le_one hR, det_ratio hx₀, exp_le_one_iff]
  have hL : 0 ≤ log ((x₀ : ℝ) / 2) := log_nonneg (by linarith)
  have hk1 : ((k : ℝ) / (k + 1)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h1 : log ((x₀ : ℝ) / 2) * ((k : ℝ) / (k + 1)) ≤ log ((x₀ : ℝ) / 2) :=
    mul_le_of_le_one_right hL hk1
  have h3 : 0 ≤ log (3 * (x₀ : ℝ)) := log_nonneg (by linarith)
  have h4 : 0 ≤ log (((k : ℝ) + 1) * (d + 1)) := log_nonneg (by nlinarith)
  have h5 : 0 ≤ (2 * ℓ + log (3 * x₀) + 2 * log (((k : ℝ) + 1) * (d + 1)) + 1) / (d + 1) := by
    positivity
  linarith

/-- A natural number within real distance `r` of `x₀` lies in the complex closed ball. -/
lemma det_mem_ball (m x₀ : ℕ) (r : ℝ) (h : |(m : ℝ) - x₀| ≤ r) :
    (m : ℂ) ∈ closedBall (x₀ : ℂ) r := by
  rw [mem_closedBall, dist_eq_norm]
  have : ((m : ℂ) - (x₀ : ℂ)) = (((m : ℝ) - x₀ : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.norm_real, Real.norm_eq_abs]; exact h

open Matrix in
/-- If all maximal square minors (rows chosen by any map `n → m`) vanish, then the matrix has
a nonzero kernel vector. -/
lemma det_exists_mulVec_eq_zero {m n K : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    [Field K] (A : Matrix m n K) (h : ∀ e : n → m, (A.submatrix e id).det = 0) :
    ∃ v ≠ 0, A *ᵥ v = 0 := by
  by_contra hne
  push Not at hne
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    by_contra hxy'
    apply hne (x - y) (sub_ne_zero.mpr hxy')
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have hcol : LinearIndependent K A.col := Matrix.mulVec_injective_iff.mp hinj
  have hrank : A.rank = Fintype.card n := by
    rw [A.rank_eq_finrank_span_cols, finrank_span_eq_card hcol]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K A.row
  have : Finite κ := Finite.of_injective a ha
  have := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card n := by
    rw [← hrank, A.rank_eq_finrank_span_row, ← hspan, finrank_span_eq_card hli]
  let σ : n ≃ κ := Fintype.equivOfCardEq hcard.symm
  have hli' : LinearIndependent K (A.submatrix (a ∘ σ) id).row := hli.comp σ σ.injective
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_row_iff_isUnit.mp hli')
  rw [h (a ∘ σ)] at hu
  exact not_isUnit_zero hu

/-- The tolerance `δ₃ = (2 D! D k R^{dD} (B_F+1)^{kD})⁻¹` of Proposition 4.1, where `R = x₀/2`,
`B_F = 3x₀ e^{2ℓ}` and `D = (k+1)(d+1)`. -/
noncomputable def δ₃ (x₀ k d : ℕ) (ℓ : ℝ) : ℝ :=
  (2 * (((k + 1) * (d + 1)).factorial : ℝ) * ((k + 1) * (d + 1) : ℕ) * k *
    ((x₀ : ℝ) / 2) ^ (d * ((k + 1) * (d + 1))) *
    (3 * x₀ * exp (2 * ℓ) + 1) ^ (k * ((k + 1) * (d + 1))))⁻¹

/-- Telescoping bound: `‖∏ x - ∏ y‖ ≤ n β α^{n-1}` when `‖x_i‖, ‖y_i‖ ≤ α`, `‖x_i - y_i‖ ≤ β`. -/
lemma det_prod_sub_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ) {α β : ℝ} (hα : 0 ≤ α)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ α) (hy : ∀ i ∈ s, ‖y i‖ ≤ α) (hxy : ∀ i ∈ s, ‖x i - y i‖ ≤ β) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ s.card * β * α ^ (s.card - 1) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hx' : ∀ i ∈ s, ‖x i‖ ≤ α := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hy' : ∀ i ∈ s, ‖y i‖ ≤ α := fun i hi => hy i (Finset.mem_insert_of_mem hi)
    have hxy' : ∀ i ∈ s, ‖x i - y i‖ ≤ β := fun i hi => hxy i (Finset.mem_insert_of_mem hi)
    have ih := ih hx' hy' hxy'
    have hP : ‖∏ i ∈ s, x i‖ ≤ α ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖x i‖ ≤ ∏ _i ∈ s, α :=
            Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) hx'
        _ = α ^ s.card := Finset.prod_const _
    have hya : ‖y a‖ ≤ α := hy a (Finset.mem_insert_self a s)
    have hxya : ‖x a - y a‖ ≤ β := hxy a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have hsplit : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i =
        (x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) := by ring
    rw [hsplit]
    have hβ : 0 ≤ β := (norm_nonneg _).trans hxya
    calc ‖(x a - y a) * ∏ i ∈ s, x i + y a * (∏ i ∈ s, x i - ∏ i ∈ s, y i)‖
        ≤ ‖x a - y a‖ * ‖∏ i ∈ s, x i‖ + ‖y a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ β * α ^ s.card + α * (s.card * β * α ^ (s.card - 1)) := by
          gcongr
      _ = ((s.card + 1 : ℕ) : ℝ) * β * α ^ (s.card + 1 - 1) := by
          rcases Nat.eq_zero_or_pos s.card with h0 | hpos
          · rw [h0]; simp
          · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
            rw [hm]; simp only [Nat.add_sub_cancel]; push_cast; ring

/-- `‖x^b - y^b‖ ≤ k ‖x - y‖ c^k` for `‖x‖, ‖y‖ ≤ c`, `1 ≤ c`, `b ≤ k`. -/
lemma det_pow_sub_le (x y : ℂ) {c : ℝ} (hc : 1 ≤ c) (hx : ‖x‖ ≤ c) (hy : ‖y‖ ≤ c) {b k : ℕ}
    (hb : b ≤ k) : ‖x ^ b - y ^ b‖ ≤ k * ‖x - y‖ * c ^ k := by
  have h := det_prod_sub_le (Finset.range b) (fun _ => x) (fun _ => y) (by linarith)
    (fun _ _ => hx) (fun _ _ => hy) (fun _ _ => le_rfl)
  simp only [Finset.prod_const, Finset.card_range] at h
  refine h.trans ?_
  have hbk : (b : ℝ) ≤ k := by exact_mod_cast hb
  have hpow : c ^ (b - 1) ≤ c ^ k := pow_le_pow_right₀ hc (by omega)
  have h0 : 0 ≤ ‖x - y‖ := norm_nonneg _
  have h1 : 0 ≤ c ^ (b - 1) := pow_nonneg (by linarith) _
  calc (b : ℝ) * ‖x - y‖ * c ^ (b - 1) ≤ k * ‖x - y‖ * c ^ (b - 1) := by gcongr
    _ ≤ k * ‖x - y‖ * c ^ k := by gcongr

/-- Perturbation of a determinant via the Leibniz formula. -/
lemma det_matrix_sub_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M M' : Matrix ι ι ℂ) {α β : ℝ}
    (hα : 0 ≤ α) (hM : ∀ i j, ‖M i j‖ ≤ α) (hM' : ∀ i j, ‖M' i j‖ ≤ α)
    (hMM' : ∀ i j, ‖M i j - M' i j‖ ≤ β) :
    ‖M.det - M'.det‖ ≤
      (Fintype.card ι).factorial * (Fintype.card ι * β * α ^ (Fintype.card ι - 1)) := by
  rw [Matrix.det_apply', Matrix.det_apply', ← Finset.sum_sub_distrib]
  calc ‖∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i -
        (Equiv.Perm.sign σ : ℂ) * ∏ i, M' (σ i) i)‖
      ≤ ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i -
          (Equiv.Perm.sign σ : ℂ) * ∏ i, M' (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, (Fintype.card ι * β * α ^ (Fintype.card ι - 1)) := by
        apply Finset.sum_le_sum
        intro σ _
        have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [← mul_sub, norm_mul, hs, one_mul]
        have := det_prod_sub_le Finset.univ (fun i => M (σ i) i) (fun i => M' (σ i) i) hα
          (fun i _ => hM _ _) (fun i _ => hM' _ _) (fun i _ => hMM' _ _)
        simpa [Finset.card_univ] using this
    _ = (Fintype.card ι).factorial * (Fintype.card ι * β * α ^ (Fintype.card ι - 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- The exponent inequality in the proof of Proposition 4.1: the exponent is at most `-1`. -/
lemma det_arith (K Dd L Λ ld : ℝ) (hK : 1 ≤ K) (hDd : 0 ≤ Dd) (hL : 0 ≤ L) (hΛ : 0 ≤ Λ)
    (hld : 0 ≤ ld) :
    (Dd + 1) * (K + 1) * ld + (Dd + 1) * (K + 1) * ((Dd + 1) * (K + 1) - 1) / 2 *
        (L * (K / (K + 1)) - (Λ + 2 * ld + 1) / (Dd + 1) - L) +
      (L * ((K + 1) * ((Dd + 1) * Dd / 2)) + Λ * ((Dd + 1) * ((K + 1) * K / 2))) ≤ -1 := by
  have hK1 : (0:ℝ) < K + 1 := by linarith
  have hD1 : (0:ℝ) < Dd + 1 := by linarith
  set D := (Dd + 1) * (K + 1) with hD
  have hD2 : 2 ≤ D := by nlinarith
  have key : (Dd + 1) * (K + 1) * ld + (Dd + 1) * (K + 1) * ((Dd + 1) * (K + 1) - 1) / 2 *
        (L * (K / (K + 1)) - (Λ + 2 * ld + 1) / (Dd + 1) - L) +
      (L * ((K + 1) * ((Dd + 1) * Dd / 2)) + Λ * ((Dd + 1) * ((K + 1) * K / 2))) =
      -((Dd + 1) * K / 2) * L - ((K + 1) * Dd / 2) * Λ +
        (D * ld - (K + 1) * (D - 1) * (2 * ld + 1) / 2) := by
    rw [hD]; field_simp; ring
  rw [key]
  have h1 : 0 ≤ (Dd + 1) * K / 2 * L := by positivity
  have h2 : 0 ≤ (K + 1) * Dd / 2 * Λ := by positivity
  have h3 : 0 ≤ (K - 1) * ((D - 1) * (2 * ld + 1)) := by
    apply mul_nonneg <;> [linarith; (apply mul_nonneg <;> linarith)]
  have h4 : 0 ≤ (D - 2) * ld := mul_nonneg (by linarith) hld
  nlinarith

/-- The Schwarz lemma bound `D! (r/R)^{D(D-1)/2} ∏ B_j` in Proposition 4.1 is at most `e^{-1}`. -/
lemma det_bound {x₀ k d : ℕ} {ℓ : ℝ} (hk : 1 ≤ k) (hx₀ : 2 ≤ x₀) (hℓ : 0 ≤ ℓ) :
    ((Fintype.card (Fin (d + 1) × Fin (k + 1))).factorial : ℝ) *
      (windowRadius x₀ k d ℓ / ((x₀ : ℝ) / 2)) ^ (Fintype.card (Fin (d + 1) × Fin (k + 1)) *
        (Fintype.card (Fin (d + 1) × Fin (k + 1)) - 1) / 2) *
      ∏ j : Fin (d + 1) × Fin (k + 1),
        (((x₀ : ℝ) / 2) ^ (j.1 : ℕ) * (3 * x₀ * exp (2 * ℓ)) ^ (j.2 : ℕ)) ≤ exp (-1) := by
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, det_ratio hx₀, det_prod hx₀,
    ← exp_nat_mul, det_W _ (Nat.mul_pos (Nat.succ_pos d) (Nat.succ_pos k))]
  have hf := det_fact ((d + 1) * (k + 1))
  calc _ ≤ exp ((((d + 1) * (k + 1) : ℕ) : ℝ) * log (((d + 1) * (k + 1) : ℕ) : ℝ)) *
        exp ((((d + 1) * (k + 1) : ℕ) : ℝ) * ((((d + 1) * (k + 1) : ℕ) : ℝ) - 1) / 2 *
          (log ((x₀ : ℝ) / 2) * ((k : ℝ) / (k + 1)) -
            (2 * ℓ + log (3 * x₀) + 2 * log (((k : ℝ) + 1) * (d + 1)) + 1) / (d + 1) -
            log ((x₀ : ℝ) / 2))) *
        exp (log ((x₀ : ℝ) / 2) * ((k + 1) * ((d + 1) * d / 2)) +
          (2 * ℓ + log (3 * x₀)) * ((d + 1) * ((k + 1) * k / 2))) := by gcongr
    _ ≤ exp (-1) := by
      rw [← exp_add, ← exp_add, exp_le_exp]
      have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
      have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
      push_cast
      rw [mul_comm ((d : ℝ) + 1) ((k : ℝ) + 1)]
      have := det_arith (k : ℝ) (d : ℝ) (log ((x₀ : ℝ) / 2)) (2 * ℓ + log (3 * x₀))
        (log (((k : ℝ) + 1) * (d + 1))) hk' (Nat.cast_nonneg d)
        (log_nonneg (by linarith))
        (by have := log_nonneg (show (1:ℝ) ≤ 3 * x₀ by linarith); linarith)
        (log_nonneg (by nlinarith))
      rw [mul_comm ((d : ℝ) + 1) ((k : ℝ) + 1)] at this
      linarith

/-- `e^{-1} < 1/2`. -/
lemma det_exp_neg_one_lt : exp (-1) < 1 / 2 := by
  have h := Real.exp_one_gt_d9
  have hm : exp (-1) * exp 1 = 1 := by rw [← exp_add]; simp
  nlinarith [exp_pos (-1)]

/-- `δ₃ ≤ 1`, so `δ ≤ 1`. -/
lemma det_delta_le_one {x₀ k d : ℕ} {ℓ δ : ℝ} (hk : 1 ≤ k) (hx₀ : 2 ≤ x₀)
    (hδ : δ ≤ δ₃ x₀ k d ℓ) : δ ≤ 1 := by
  refine hδ.trans (inv_le_one_of_one_le₀ ?_)
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  have hR : (1 : ℝ) ≤ (x₀ : ℝ) / 2 := by linarith
  have hE : (1 : ℝ) ≤ 3 * x₀ * exp (2 * ℓ) + 1 := by
    have : 0 ≤ 3 * (x₀ : ℝ) * exp (2 * ℓ) := by positivity
    linarith
  have hF : (1 : ℝ) ≤ (((k + 1) * (d + 1)).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have hN : (1 : ℝ) ≤ (((k + 1) * (d + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos d)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  calc (1 : ℝ) ≤ 2 * 1 * 1 * 1 * 1 * 1 := by norm_num
    _ ≤ _ := by
      gcongr
      · exact one_le_pow₀ hR
      · exact one_le_pow₀ hE

/-- The perturbation `D! · D · β · α^{D-1}` is at most `1/2`. -/
lemma det_delta_le {x₀ k d : ℕ} {ℓ δ : ℝ} (hk : 1 ≤ k) (hx₀ : 2 ≤ x₀)
    (hδ : δ ≤ δ₃ x₀ k d ℓ) :
    (((k + 1) * (d + 1)).factorial : ℝ) * (((k + 1) * (d + 1) : ℕ) *
      (((x₀ : ℝ) / 2) ^ d * (k * δ * (3 * x₀ * exp (2 * ℓ) + 1) ^ k)) *
      (((x₀ : ℝ) / 2) ^ d * (3 * x₀ * exp (2 * ℓ) + 1) ^ k) ^ ((k + 1) * (d + 1) - 1)) ≤
      1 / 2 := by
  unfold δ₃ at hδ
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set N := (k + 1) * (d + 1) with hN
  set R := (x₀ : ℝ) / 2 with hR
  set E := 3 * (x₀ : ℝ) * exp (2 * ℓ) + 1 with hE
  have hR0 : 0 < R := by rw [hR]; linarith
  have hE0 : 0 < E := by rw [hE]; positivity
  have hN0 : 0 < N := Nat.mul_pos (Nat.succ_pos k) (Nat.succ_pos d)
  set Q := (N.factorial : ℝ) * (N : ℝ) * k * R ^ (d * N) * E ^ (k * N) with hQ
  have hQ0 : 0 < Q := by
    have : (0 : ℝ) < N := by exact_mod_cast hN0
    rw [hQ]; positivity
  have heq : (N.factorial : ℝ) * ((N : ℝ) * (R ^ d * (k * δ * E ^ k)) *
      (R ^ d * E ^ k) ^ (N - 1)) = Q * δ := by
    obtain ⟨N', hN'⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    rw [hQ, hN', Nat.add_sub_cancel]
    ring
  have h2Q : 2 * (N.factorial : ℝ) * (N : ℝ) * k * R ^ (d * N) * E ^ (k * N) = 2 * Q := by
    rw [hQ]; ring
  rw [h2Q] at hδ
  rw [heq]
  calc Q * δ ≤ Q * (2 * Q)⁻¹ := mul_le_mul_of_nonneg_left hδ hQ0.le
    _ = 1 / 2 := by field_simp

/-- Every `D × D` determinant `det [(m_i - x₀)^a n_i^b]` vanishes: it is an integer within
`1/2` of the determinant `det [(m_i - x₀)^a F(m_i)^b]`, which is at most `e^{-1}`. -/
lemma det_minor_zero {x₀ k d : ℕ} {ℓ δ : ℝ} (hk : 1 ≤ k) (hx₀ : 2 ≤ x₀) (hℓ : 0 ≤ ℓ)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (closedBall (x₀ : ℂ) (x₀ / 2)))
    (hFb : ∀ z ∈ closedBall (x₀ : ℂ) (x₀ / 2), ‖F z‖ ≤ 3 * x₀ * exp (2 * ℓ))
    (hδ : δ ≤ δ₃ x₀ k d ℓ)
    (P : Fin (d + 1) × Fin (k + 1) → ℕ × ℕ)
    (hP : ∀ i, |((P i).2 : ℝ) - x₀| ≤ windowRadius x₀ k d ℓ ∧ ‖F (P i).2 - (P i).1‖ ≤ δ) :
    (Matrix.of fun i j : Fin (d + 1) × Fin (k + 1) =>
      (((P i).2 : ℂ) - x₀) ^ (j.1 : ℕ) * ((P i).1 : ℂ) ^ (j.2 : ℕ)).det = 0 := by
  set M : Matrix (Fin (d + 1) × Fin (k + 1)) (Fin (d + 1) × Fin (k + 1)) ℂ :=
    Matrix.of fun i j => (((P i).2 : ℂ) - x₀) ^ (j.1 : ℕ) * ((P i).1 : ℂ) ^ (j.2 : ℕ) with hM
  let N : Matrix (Fin (d + 1) × Fin (k + 1)) (Fin (d + 1) × Fin (k + 1)) ℤ :=
    Matrix.of fun i j => (((P i).2 : ℤ) - x₀) ^ (j.1 : ℕ) * ((P i).1 : ℤ) ^ (j.2 : ℕ)
  have hMN : M = (Int.castRingHom ℂ).mapMatrix N := by ext i j; simp [M, N]
  have hdet : M.det = ((N.det : ℤ) : ℂ) := by rw [hMN, ← RingHom.map_det]; rfl
  set M' : Matrix (Fin (d + 1) × Fin (k + 1)) (Fin (d + 1) × Fin (k + 1)) ℂ :=
    Matrix.of fun i j =>
      (fun (j : Fin (d + 1) × Fin (k + 1)) (z : ℂ) => (z - x₀) ^ (j.1 : ℕ) * F z ^ (j.2 : ℕ))
        j (((P i).2 : ℕ) : ℂ) with hM'
  -- The determinant with `F(m_i)` is small, by the Schwarz lemma.
  have h1 : ‖M'.det‖ ≤ exp (-1) := by
    refine le_trans (interpolation_det_le
      (fun (j : Fin (d + 1) × Fin (k + 1)) (z : ℂ) => (z - x₀) ^ (j.1 : ℕ) * F z ^ (j.2 : ℕ))
      (x₀ : ℂ) (det_r_pos hx₀) (det_r_le hx₀ hℓ) ?_
      (fun j : Fin (d + 1) × Fin (k + 1) =>
        ((x₀ : ℝ) / 2) ^ (j.1 : ℕ) * (3 * x₀ * exp (2 * ℓ)) ^ (j.2 : ℕ)) ?_
      (fun i => (((P i).2 : ℕ) : ℂ)) ?_)
      (det_bound hk hx₀ hℓ)
    · intro j
      exact ((differentiableOn_id.sub_const _).pow _).mul (hF.pow _)
    · intro j z hz
      rw [norm_mul, norm_pow, norm_pow]
      have hz' := hz
      rw [mem_closedBall, dist_eq_norm] at hz'
      gcongr
      exact hFb z hz
    · intro i
      exact det_mem_ball _ _ _ (hP i).1
  -- Pointwise bounds.
  have h2 : (2 : ℝ) ≤ x₀ := by exact_mod_cast hx₀
  have hR1 : (1 : ℝ) ≤ (x₀ : ℝ) / 2 := by linarith
  have hE0 : 0 ≤ 3 * (x₀ : ℝ) * exp (2 * ℓ) := by positivity
  have hc1 : (1 : ℝ) ≤ 3 * (x₀ : ℝ) * exp (2 * ℓ) + 1 := by linarith
  have hball : ∀ i, (((P i).2 : ℕ) : ℂ) ∈ closedBall (x₀ : ℂ) (x₀ / 2) := fun i =>
    closedBall_subset_closedBall (det_r_le hx₀ hℓ) (det_mem_ball _ _ _ (hP i).1)
  have hzR : ∀ i, ‖(((P i).2 : ℕ) : ℂ) - x₀‖ ≤ (x₀ : ℝ) / 2 := fun i => by
    have := hball i
    rwa [mem_closedBall, dist_eq_norm] at this
  have hFE : ∀ i, ‖F ((P i).2 : ℂ)‖ ≤ 3 * x₀ * exp (2 * ℓ) + 1 := fun i => by
    have := hFb _ (hball i); linarith
  have hδ1 : δ ≤ 1 := det_delta_le_one hk hx₀ hδ
  have hn : ∀ i, ‖(((P i).1 : ℕ) : ℂ)‖ ≤ 3 * x₀ * exp (2 * ℓ) + 1 := fun i => by
    have h := norm_sub_norm_le (((P i).1 : ℕ) : ℂ) (F ((P i).2 : ℂ))
    rw [norm_sub_rev (((P i).1 : ℕ) : ℂ)] at h
    have := (hP i).2
    have := hFb _ (hball i)
    linarith
  have hza : ∀ i (a : Fin (d + 1)),
      ‖(((P i).2 : ℕ) : ℂ) - x₀‖ ^ (a : ℕ) ≤ ((x₀ : ℝ) / 2) ^ d := fun i a =>
    (pow_le_pow_left₀ (norm_nonneg _) (hzR i) _).trans
      (pow_le_pow_right₀ hR1 (Nat.lt_succ_iff.mp a.2))
  have hyb : ∀ y : ℂ, ‖y‖ ≤ 3 * x₀ * exp (2 * ℓ) + 1 → ∀ b : Fin (k + 1),
      ‖y‖ ^ (b : ℕ) ≤ (3 * x₀ * exp (2 * ℓ) + 1) ^ k := fun y hy b =>
    (pow_le_pow_left₀ (norm_nonneg _) hy _).trans
      (pow_le_pow_right₀ hc1 (Nat.lt_succ_iff.mp b.2))
  have hMb : ∀ i j, ‖M i j‖ ≤ ((x₀ : ℝ) / 2) ^ d * (3 * x₀ * exp (2 * ℓ) + 1) ^ k := by
    intro i j
    simp only [M, Matrix.of_apply, norm_mul, norm_pow]
    exact mul_le_mul (hza i j.1) (hyb _ (hn i) j.2) (by positivity) (by positivity)
  have hM'b : ∀ i j, ‖M' i j‖ ≤ ((x₀ : ℝ) / 2) ^ d * (3 * x₀ * exp (2 * ℓ) + 1) ^ k := by
    intro i j
    simp only [M', Matrix.of_apply, norm_mul, norm_pow]
    exact mul_le_mul (hza i j.1) (hyb _ (hFE i) j.2) (by positivity) (by positivity)
  have hMM'b : ∀ i j, ‖M i j - M' i j‖ ≤
      ((x₀ : ℝ) / 2) ^ d * (k * δ * (3 * x₀ * exp (2 * ℓ) + 1) ^ k) := by
    intro i j
    simp only [M, M', Matrix.of_apply]
    rw [← mul_sub, norm_mul, norm_pow]
    refine mul_le_mul (hza i j.1) ?_ (norm_nonneg _) (by positivity)
    refine (det_pow_sub_le _ _ hc1 (hn i) (hFE i) (Nat.lt_succ_iff.mp j.2.2)).trans ?_
    rw [norm_sub_rev]
    have := (hP i).2
    gcongr
  have hdiff := det_matrix_sub_le M M' (by positivity) hMb hM'b hMM'b
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, mul_comm (d + 1) (k + 1)] at hdiff
  have hdiff' := hdiff.trans (det_delta_le hk hx₀ hδ)
  have hlt : ‖M.det‖ < 1 := by
    have h3 := norm_add_le M'.det (M.det - M'.det)
    rw [add_sub_cancel] at h3
    have := det_exp_neg_one_lt
    linarith
  rw [hdet] at hlt ⊢
  rw [Complex.norm_intCast] at hlt
  have : |N.det| < 1 := by exact_mod_cast hlt
  rw [Int.abs_lt_one_iff.mp this]
  simp

/-- **Proposition 4.1.** -/
theorem solutions_on_curve {x₀ k d : ℕ} {ℓ δ : ℝ} (hk : 1 ≤ k) (hx₀ : 2 ≤ x₀) (hℓ : 0 ≤ ℓ)
    {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (closedBall (x₀ : ℂ) (x₀ / 2)))
    (hFb : ∀ z ∈ closedBall (x₀ : ℂ) (x₀ / 2), ‖F z‖ ≤ 3 * x₀ * exp (2 * ℓ))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ₃ x₀ k d ℓ) (S : Finset (ℕ × ℕ))
    (hS : ∀ p ∈ S, |(p.2 : ℝ) - x₀| ≤ windowRadius x₀ k d ℓ ∧ ‖F p.2 - p.1‖ ≤ δ) :
    ∃ A : Fin (k + 1) → ℂ[X], (∃ b, A b ≠ 0) ∧ (∀ b, (A b).natDegree ≤ d) ∧
      ∀ p ∈ S, ∑ b : Fin (k + 1), (A b).eval (p.2 : ℂ) * ((p.1 : ℕ) : ℂ) ^ (b : ℕ) = 0 := by
  -- `0 ≤ δ` is not needed (it follows from `hS` whenever `S` is nonempty).
  have _ := hδ0
  classical
  let Mat : Matrix S (Fin (d + 1) × Fin (k + 1)) ℂ := Matrix.of fun p j =>
    (((p : ℕ × ℕ).2 : ℂ) - x₀) ^ (j.1 : ℕ) * ((p : ℕ × ℕ).1 : ℂ) ^ (j.2 : ℕ)
  have hminor : ∀ e : Fin (d + 1) × Fin (k + 1) → S, (Mat.submatrix e id).det = 0 := fun e =>
    det_minor_zero hk hx₀ hℓ hF hFb hδ (fun i => (e i : ℕ × ℕ)) (fun i => hS _ (e i).2)
  obtain ⟨c, hc0, hc⟩ := det_exists_mulVec_eq_zero Mat hminor
  obtain ⟨⟨a₀, b₀⟩, hab⟩ := Function.ne_iff.mp hc0
  refine ⟨fun b => (∑ a : Fin (d + 1), C (c (a, b)) * X ^ (a : ℕ)).comp (X - C (x₀ : ℂ)),
    ⟨b₀, ?_⟩, ?_, ?_⟩
  · intro h
    rw [comp_eq_zero_iff] at h
    rcases h with h | ⟨-, h⟩
    · have := congrArg (fun q => coeff q (a₀ : ℕ)) h
      simp [finsetSum_coeff, Fin.val_inj] at this
      exact hab this
    · have := congrArg natDegree h
      rw [natDegree_X_sub_C, natDegree_C] at this
      exact one_ne_zero this
  · intro b
    rw [natDegree_comp, natDegree_X_sub_C, mul_one]
    apply natDegree_sum_le_of_forall_le
    intro a _
    exact (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp a.2)
  · intro p hp
    have h1 := congrFun hc ⟨p, hp⟩
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Mat, Matrix.of_apply,
      Pi.zero_apply] at h1
    simp only [eval_comp, eval_finsetSum, eval_sub, eval_X, eval_C, eval_mul, eval_pow,
      Finset.sum_mul]
    rw [Finset.sum_comm, ← h1]
    apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring

end Singmaster
