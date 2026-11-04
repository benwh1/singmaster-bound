module

public import Singmaster.Determinant.Main
public import Singmaster.Interpolation.Main
public import Singmaster.ZeroEstimate.Main

@[expose] public section

/-!
# Lemma 7.2: one window

Write `L = log t`, `λ = log L`, `a₀ = a₀(k)`, `α = k/(k+1)`, `θ = (k+1)/(2k+1)`, `M₀ = L^θ`
and `M₁ = L/λ^{7/5}`, and assume (7.1), `40 (k+1)² a₀ ≤ λ^{2/5}` (`ct_standing`). For
`M₀ ≤ M ≤ M₁` and an integer `x₀ ∈ [M, 2M]`, the window `|m - x₀| ≤ r_M` (`rad`) contains at
most `L/M` elements of `Sol(t)` (`ct_window`). The proof combines Propositions 3.1, 4.1 and 6.1.
`ct_delta3` and `ct_delta5` show that the tolerances `δ₃` and `δ₅` of Propositions 4.1 and 6.1
are at least `e^{-L/8}`, using inequality (7.2) (`ct_H`).

`GoodLam X λ` collects the conditions "`λ` is large" used in Section 7.
-/

open Real Filter Polynomial Topology

namespace Singmaster

/-! ## Numerical lemmas -/

/-- Hypothesis (7.1) gives `k + 1 ≤ λ^{1/5}` and `160 a₀ ≤ λ^{2/5}`. -/
lemma ct_standing {k : ℕ} {lam : ℝ} (hk : 1 ≤ k) (hlam : 0 ≤ lam)
    (h : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ lam ^ ((2 : ℝ) / 5)) :
    (k : ℝ) + 1 ≤ lam ^ ((1 : ℝ) / 5) ∧ 160 * a₀ k ≤ lam ^ ((2 : ℝ) / 5) := by
  have ha := a₀_ge k
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : lam ^ ((2 : ℝ) / 5) = (lam ^ ((1 : ℝ) / 5)) ^ 2 := by
    rw [← rpow_natCast, ← rpow_mul hlam]; norm_num
  have h15 : 0 ≤ lam ^ ((1 : ℝ) / 5) := by positivity
  constructor
  · have h1 : ((k : ℝ) + 1) ^ 2 ≤ (lam ^ ((1 : ℝ) / 5)) ^ 2 := by
      rw [← hsq]; nlinarith [sq_nonneg ((k : ℝ) + 1)]
    nlinarith
  · have h4 : (4 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right h4 (show (0 : ℝ) ≤ a₀ k by linarith)
    linarith

/-- The conditions "`λ` is large" used in Section 7 (`λ = log log t`). -/
def GoodLam (X lam : ℝ) : Prop :=
  9 ≤ lam ∧ X ≤ exp (lam / 2) ∧ 400 ≤ lam ^ ((2 : ℝ) / 5) ∧
    12 * (lam ^ ((1 : ℝ) / 5) * exp (-(1 / 4) * lam)) +
      2 * (lam ^ ((1 : ℝ) / 5) * exp (-(1 / 10) * lam)) ≤ 0.09

lemma ct_eventually_goodLam (X : ℝ) : ∀ᶠ lam in atTop, GoodLam X lam := by
  have h1 : Tendsto (fun lam : ℝ => exp (lam / 2)) atTop atTop :=
    tendsto_exp_atTop.comp (tendsto_id.atTop_div_const (by norm_num))
  have h2 : Tendsto (fun lam : ℝ => lam ^ ((2 : ℝ) / 5)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have h3 : Tendsto (fun lam : ℝ => 12 * (lam ^ ((1 : ℝ) / 5) * exp (-(1 / 4) * lam)) +
      2 * (lam ^ ((1 : ℝ) / 5) * exp (-(1 / 10) * lam))) atTop (𝓝 0) := by
    have a1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 : ℝ) / 5) (1 / 4) (by norm_num)
    have a2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((1 : ℝ) / 5) (1 / 10) (by norm_num)
    simpa using (a1.const_mul 12).add (a2.const_mul 2)
  filter_upwards [eventually_ge_atTop 9, h1.eventually_ge_atTop X, h2.eventually_ge_atTop 400,
    (tendsto_order.1 h3).2 0.09 (by norm_num)] with lam a b c d
  exact ⟨a, b, c, d.le⟩

/-- `η₀(x₀, ℓ) ≤ 12 e^{-λ/4} + 2 e^{-λ/10}` once `x₀ ≥ e^{λ/2}` and `ℓ ≥ λ/2`. -/
lemma ct_eta {x₀ lam ℓ : ℝ} (hlam : 0 ≤ lam) (hx : exp (lam / 2) ≤ x₀) (hℓ : lam / 2 ≤ ℓ) :
    η₀ x₀ ℓ ≤ 12 * exp (-(1 / 4) * lam) + 2 * exp (-(1 / 10) * lam) := by
  have hx1 : 1 ≤ x₀ := (one_le_exp (by linarith)).trans hx
  have hx0 : 0 < x₀ := by linarith
  have hs0 : 0 < √x₀ := Real.sqrt_pos.2 hx0
  have hsx : √x₀ * √x₀ = x₀ := Real.mul_self_sqrt hx0.le
  have hs1 : 1 ≤ √x₀ := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hx1
  have hes : exp (lam / 4) ≤ √x₀ := by
    rw [Real.le_sqrt (exp_pos _).le hx0.le, ← exp_nat_mul]
    calc exp ((2 : ℕ) * (lam / 4)) = exp (lam / 2) := by congr 1; push_cast; ring
      _ ≤ x₀ := hx
  have hlog : log x₀ ≤ 2 * √x₀ := by
    have h1 : log x₀ = 2 * log √x₀ := by rw [Real.log_sqrt hx0.le]; ring
    have h2 := Real.log_le_sub_one_of_pos hs0
    linarith
  have hE : exp (-(1 / 4) * lam) * exp (lam / 4) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  have hE0 : 0 < exp (-(1 / 4) * lam) := exp_pos _
  have key : √x₀ ≤ exp (-(1 / 4) * lam) * x₀ := by
    have h := mul_le_mul_of_nonneg_left hes hE0.le
    rw [hE] at h
    calc √x₀ = 1 * √x₀ := by ring
      _ ≤ (exp (-(1 / 4) * lam) * √x₀) * √x₀ := mul_le_mul_of_nonneg_right h hs0.le
      _ = exp (-(1 / 4) * lam) * x₀ := by rw [mul_assoc, hsx]
  have h1 : 2 * (log x₀ + 4) / x₀ ≤ 12 * exp (-(1 / 4) * lam) := by
    rw [div_le_iff₀ hx0]
    linarith
  have h2 : exp (-ℓ / 5) ≤ exp (-(1 / 10) * lam) := exp_le_exp.2 (by linarith)
  unfold η₀
  linarith

/-- If `log log log t ≥ 1` then `log t > 0` and `log log t ≥ e`. -/
lemma ct_lam_of_logloglog (t : ℕ) (h : 1 ≤ log (log (log t))) :
    0 < log (t : ℝ) ∧ exp 1 ≤ log (log t) := by
  rcases t with _ | _ | t
  · simp at h; linarith
  · simp at h; linarith
  have hL : log (2 : ℝ) ≤ log ((t + 2 : ℕ) : ℝ) := log_le_log (by norm_num) (by push_cast; linarith)
  have hl2 := Real.log_two_gt_d9
  have hLpos : 0 < log ((t + 2 : ℕ) : ℝ) := by linarith
  refine ⟨hLpos, ?_⟩
  set lam := log (log ((t + 2 : ℕ) : ℝ))
  by_cases hpos : 0 < lam
  · exact (Real.le_log_iff_exp_le hpos).1 h
  · exfalso
    push Not at hpos
    have he : exp (-1) < log ((t + 2 : ℕ) : ℝ) := by
      have := Real.exp_one_gt_d9
      have h1 : exp (-1) = (exp 1)⁻¹ := by rw [exp_neg]
      rw [h1, inv_lt_comm₀ (exp_pos 1) hLpos]
      calc (log ((t + 2 : ℕ) : ℝ))⁻¹ ≤ (log 2)⁻¹ := inv_anti₀ (by positivity) hL
        _ < 2.7182818283 := by rw [inv_lt_comm₀ (by positivity) (by norm_num)]; norm_num; linarith
        _ < exp 1 := this
    have hge : -1 < lam := by
      have := log_lt_log (exp_pos _) he
      rwa [log_exp] at this
    have : log lam ≤ 0 := by
      rw [← Real.log_neg_eq_log]; exact Real.log_nonpos (by linarith) (by linarith)
    linarith

/-! ## The window radius -/

/-- The common window radius `r_M = (M/2)^{k/(k+1)} e^{-2a₀-1}` of a block `[M, 2M]`. -/
noncomputable def rad (k : ℕ) (M : ℝ) : ℝ := (M / 2) ^ ((k : ℝ) / (k + 1)) * exp (-(2 * a₀ k) - 1)

/-! ## The tolerances `δ₃` and `δ₅` -/

/-- The exponent bound behind `ct_delta3`. -/
lemma ct_delta3_expo {K β lM d D : ℝ} (hK2 : 2 ≤ K) (hβ : 1 ≤ β) (hlM : 0 ≤ lM) (hd0 : 0 ≤ d)
    (hd : d ≤ β) (hD : D = K * (d + 1)) :
    1 + D * D + D + K + d * D * lM + (K - 1) * D * (3 + lM + 2 * β) ≤
      K ^ 2 * β ^ 2 * (19 + 4 * lM) := by
  have hDβ : D ≤ 2 * K * β := by rw [hD]; nlinarith
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have e1 : D * D ≤ 4 * K ^ 2 * β ^ 2 := by nlinarith
  have e2 : d * D * lM ≤ 2 * K ^ 2 * β ^ 2 * lM := by
    have : d * D ≤ 2 * K ^ 2 * β ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hlM
  have e3 : (K - 1) * D ≤ 2 * K ^ 2 * β := by nlinarith
  have e4 : (K - 1) * D * (3 + lM + 2 * β) ≤ 2 * K ^ 2 * β * (3 + lM + 2 * β) :=
    mul_le_mul_of_nonneg_right e3 (by positivity)
  have e5 : 2 * K ^ 2 * β * (3 + lM + 2 * β) ≤ 2 * K ^ 2 * β ^ 2 * (3 + lM) + 4 * K ^ 2 * β ^ 2 := by
    have : K ^ 2 * β ≤ K ^ 2 * β ^ 2 := by nlinarith
    have h := mul_le_mul_of_nonneg_right this (show (0 : ℝ) ≤ 3 + lM by positivity)
    nlinarith
  have hK1 : (1 : ℝ) ≤ K ^ 2 := by nlinarith
  have hβ1 : (1 : ℝ) ≤ β ^ 2 := by nlinarith
  have h1 : (1 : ℝ) ≤ K ^ 2 * β ^ 2 := one_le_mul_of_one_le_of_one_le hK1 hβ1
  have hD2 : D ≤ 2 * K ^ 2 * β ^ 2 := by nlinarith
  have hK : K ≤ K ^ 2 * β ^ 2 := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- `e^{-L/8} ≤ δ₃`. -/
lemma ct_delta3 {x₀ k d : ℕ} {L M : ℝ} (hk : 1 ≤ k) (hM : 2 ≤ M) (hLM : M ≤ L)
    (hx₁ : M ≤ x₀) (hx₂ : (x₀ : ℝ) ≤ 2 * M) (hd : (d : ℝ) ≤ L / M) (hβ : 1 ≤ L / M)
    (hH : 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ M ^ 2 / L) :
    exp (-L / 8) ≤ δ₃ x₀ k d (L / x₀) := by
  have hMpos : 0 < M := by linarith
  have hL0 : 0 < L := by linarith
  have hx0 : (2 : ℝ) ≤ x₀ := by linarith
  obtain ⟨β, hβdef⟩ : ∃ β, β = L / M := ⟨_, rfl⟩
  rw [← hβdef] at hd hβ
  have hLβ : L = M * β := by rw [hβdef]; field_simp
  have hlM : 0 ≤ log M := Real.log_nonneg (by linarith)
  have hKr : (2 : ℝ) ≤ (k : ℝ) + 1 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  obtain ⟨D, hD⟩ : ∃ D : ℕ, (k + 1) * (d + 1) = D := ⟨_, rfl⟩
  have hDr : (D : ℝ) = ((k : ℝ) + 1) * ((d : ℝ) + 1) := by rw [← hD]; push_cast; ring
  have hℓβ : L / x₀ ≤ β := by rw [hβdef]; exact div_le_div_of_nonneg_left hL0.le hMpos hx₁
  have hℓ0 : 0 ≤ L / x₀ := by positivity
  -- each factor is at most an exponential
  have f1 : (2 : ℝ) ≤ exp 1 := by have := add_one_le_exp (1 : ℝ); linarith
  have f2 : ((D.factorial : ℕ) : ℝ) ≤ exp ((D : ℝ) * D) := by
    calc ((D.factorial : ℕ) : ℝ) ≤ ((D ^ D : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_le_pow D
      _ = (D : ℝ) ^ D := by push_cast; ring
      _ ≤ (exp (D : ℝ)) ^ D := pow_le_pow_left₀ (by positivity)
          (by have := add_one_le_exp (D : ℝ); linarith) _
      _ = exp ((D : ℝ) * D) := by rw [← exp_nat_mul]
  have f3 : ((D : ℕ) : ℝ) ≤ exp (D : ℝ) := by have := add_one_le_exp (D : ℝ); linarith
  have f4 : (k : ℝ) ≤ exp ((k : ℝ) + 1) := by have := add_one_le_exp ((k : ℝ) + 1); linarith
  have f5 : ((x₀ : ℝ) / 2) ^ (d * D) ≤ exp (((d : ℝ) * D) * log M) := by
    calc ((x₀ : ℝ) / 2) ^ (d * D) ≤ M ^ (d * D) := pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = exp (log M) ^ (d * D) := by rw [exp_log hMpos]
      _ = exp (((d : ℝ) * D) * log M) := by rw [← exp_nat_mul]; push_cast; ring_nf
  have hB : 3 * x₀ * exp (2 * (L / x₀)) + 1 ≤ exp (3 + log M + 2 * β) := by
    have h1 : 1 ≤ (x₀ : ℝ) * exp (2 * (L / x₀)) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_exp (by positivity))
    have h2 : exp (2 * (L / x₀)) ≤ exp (2 * β) := exp_le_exp.2 (by linarith)
    have h8 : (8 : ℝ) ≤ exp 3 := by
      have := Real.exp_one_gt_d9
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (show (2 : ℝ) ≤ exp 1 by linarith) 3
      rw [← exp_nat_mul] at h; norm_num at h; linarith
    calc 3 * x₀ * exp (2 * (L / x₀)) + 1 ≤ 4 * (x₀ * exp (2 * (L / x₀))) := by linarith
      _ ≤ 4 * (2 * M * exp (2 * β)) := by gcongr
      _ = 8 * M * exp (2 * β) := by ring
      _ ≤ exp 3 * exp (log M) * exp (2 * β) := by rw [exp_log hMpos]; gcongr
      _ = exp (3 + log M + 2 * β) := by rw [← exp_add, ← exp_add]
  have f6 : (3 * x₀ * exp (2 * (L / x₀)) + 1) ^ (k * D) ≤
      exp (((k : ℝ) * D) * (3 + log M + 2 * β)) := by
    calc (3 * x₀ * exp (2 * (L / x₀)) + 1) ^ (k * D) ≤ (exp (3 + log M + 2 * β)) ^ (k * D) :=
          pow_le_pow_left₀ (by positivity) hB _
      _ = _ := by rw [← exp_nat_mul]; push_cast; ring_nf
  -- the exponent
  have hexpo := ct_delta3_expo (K := (k : ℝ) + 1) (β := β) (lM := log M) (d := d) (D := D)
    hKr hβ hlM (Nat.cast_nonneg d) hd hDr
  have hfin : ((k : ℝ) + 1) ^ 2 * β ^ 2 * (19 + 4 * log M) ≤ L / 8 := by
    have h1 : 8 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ M ^ 2 / L := by nlinarith
    rw [le_div_iff₀ hL0, hLβ] at h1
    have hβ0 : 0 < β := by linarith
    have : 8 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) * β ≤ M := by nlinarith
    rw [hLβ]; nlinarith
  -- conclude
  unfold δ₃
  rw [hD]
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hDpos : (0 : ℝ) < D := by rw [hDr]; positivity
  have hP : 0 < 2 * ((D.factorial : ℕ) : ℝ) * ((D : ℕ) : ℝ) * k * ((x₀ : ℝ) / 2) ^ (d * D) *
      (3 * x₀ * exp (2 * (L / x₀)) + 1) ^ (k * D) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by positivity) hDpos) hk0) (by positivity)) (by positivity)
  rw [le_inv_comm₀ (exp_pos _) hP, ← exp_neg, neg_div, neg_neg]
  have hprod : 2 * ((D.factorial : ℕ) : ℝ) * ((D : ℕ) : ℝ) * k * ((x₀ : ℝ) / 2) ^ (d * D) *
      (3 * x₀ * exp (2 * (L / x₀)) + 1) ^ (k * D) ≤
      exp 1 * exp ((D : ℝ) * D) * exp (D : ℝ) * exp ((k : ℝ) + 1) *
        exp (((d : ℝ) * D) * log M) * exp (((k : ℝ) * D) * (3 + log M + 2 * β)) := by
    have g1 := mul_le_mul f1 f2 (by positivity) (by positivity)
    have g2 := mul_le_mul g1 f3 (by positivity) (by positivity)
    have g3 := mul_le_mul g2 f4 (by positivity) (by positivity)
    have g4 := mul_le_mul g3 f5 (by positivity) (by positivity)
    exact mul_le_mul g4 f6 (by positivity) (by positivity)
  have hsum : exp 1 * exp ((D : ℝ) * D) * exp (D : ℝ) * exp ((k : ℝ) + 1) *
        exp (((d : ℝ) * D) * log M) * exp (((k : ℝ) * D) * (3 + log M + 2 * β)) =
      exp (1 + (D : ℝ) * D + D + ((k : ℝ) + 1) + (d : ℝ) * D * log M +
        ((k : ℝ) + 1 - 1) * D * (3 + log M + 2 * β)) := by
    rw [← exp_add, ← exp_add, ← exp_add, ← exp_add, ← exp_add]; congr 1; ring
  calc _ ≤ _ := hprod
    _ = _ := hsum
    _ ≤ exp (L / 8) := exp_le_exp.2 (hexpo.trans hfin)

/-- `e^{-L/8} ≤ δ₅`. -/
lemma ct_delta5 {x₀ k : ℕ} {L M : ℝ} (hk : 1 ≤ k) (hM : 2 ≤ M) (hLM : M ≤ L)
    (hx₁ : M ≤ x₀) (hx₂ : (x₀ : ℝ) ≤ 2 * M) (ha : 1 ≤ a₀ k) (hβ : 1 ≤ L / M)
    (hH : 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ M ^ 2 / L) :
    exp (-L / 8) ≤ δ₅ k x₀ (L / (a₀ k * x₀)) := by
  have hMpos : 0 < M := by linarith
  have hL0 : 0 < L := by linarith
  have hx0 : (0 : ℝ) < x₀ := by linarith
  have hlM : 0 ≤ log M := Real.log_nonneg (by linarith)
  set β := L / M with hβdef
  have hLβ : L = M * β := by rw [hβdef]; field_simp
  set K : ℝ := (k : ℝ) + 1
  have hT : L / (a₀ k * x₀) + 1 ≤ 2 * β := by
    have h1 : L / (a₀ k * x₀) ≤ β :=
      div_le_div_of_nonneg_left hL0.le hMpos (by nlinarith)
    linarith
  have hlog : log (6 * x₀ + 6) ≤ 3 + log M := by
    have h15 : log (15 : ℝ) ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.7) (show (2.7 : ℝ) ≤ exp 1 by linarith) 3
      rw [← exp_nat_mul] at h; norm_num at h; linarith
    calc log (6 * x₀ + 6) ≤ log (15 * M) := log_le_log (by positivity) (by linarith)
      _ = log 15 + log M := log_mul (by norm_num) hMpos.ne'
      _ ≤ 3 + log M := by linarith
  have hMM : M ^ 2 / L ≤ M := by
    rw [div_le_iff₀ hL0]; nlinarith
  have hK : 16000 * K ^ 2 * (3 + log M) ≤ M := by
    have : 16000 * K ^ 2 * (3 + log M) ≤ 16000 * K ^ 2 * (19 + 4 * log M) := by
      have : 0 ≤ 16000 * K ^ 2 := by positivity
      nlinarith
    linarith
  unfold δ₅
  apply exp_le_exp.2
  have hβ0 : 0 < β := by linarith
  have e1 : 1000 * K ^ 2 * (L / (a₀ k * x₀) + 1) * log (6 * x₀ + 6) ≤
      1000 * K ^ 2 * (2 * β) * (3 + log M) := by
    have hK0 : 0 ≤ 1000 * K ^ 2 := by positivity
    have hl0 : 0 ≤ log (6 * x₀ + 6) := Real.log_nonneg (by linarith)
    calc 1000 * K ^ 2 * (L / (a₀ k * x₀) + 1) * log (6 * x₀ + 6)
        ≤ 1000 * K ^ 2 * (2 * β) * log (6 * x₀ + 6) := by gcongr
      _ ≤ 1000 * K ^ 2 * (2 * β) * (3 + log M) := by gcongr
  have e2 : 1000 * K ^ 2 * (2 * β) * (3 + log M) ≤ L / 8 := by
    rw [hLβ]
    have := mul_le_mul_of_nonneg_right hK hβ0.le
    nlinarith
  linarith

/-- Inequality (7.2): `16000 (k+1)² (19 + 4 log M) ≤ M²/L` for `M₀ ≤ M ≤ M₁`. -/
lemma ct_H {t k : ℕ} {M : ℝ} (hk : 1 ≤ k) (hL : 0 < log (t : ℝ))
    (hlam : 2 * 10 ^ 7 ≤ log (log t))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5))
    (hM0 : log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ M)
    (hM1 : M ≤ log (t : ℝ) / log (log t) ^ ((7 : ℝ) / 5)) :
    16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ M ^ 2 / log (t : ℝ) := by
  set L := log (t : ℝ) with hLdef
  set lam := log L with hlamdef
  have hlam1 : 1 ≤ lam := by linarith
  have hlam0 : 0 < lam := by linarith
  have hLexp : L = exp lam := (exp_log hL).symm
  have hL1 : 1 ≤ L := by rw [hLexp]; exact one_le_exp (by linarith)
  obtain ⟨hk1, -⟩ := ct_standing hk hlam0.le hst
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set e := ((k : ℝ) + 1) / (2 * k + 1) with hedef
  have hMpos : 0 < M := lt_of_lt_of_le (rpow_pos_of_pos hL e) hM0
  -- `M² / L ≥ L^{2e-1} = exp(lam/(2k+1))`
  have h2e : 2 * e - 1 = 1 / (2 * k + 1) := by rw [hedef]; field_simp; ring
  have hM2 : exp (lam / (2 * k + 1)) ≤ M ^ 2 / L := by
    rw [le_div_iff₀ (by linarith)]
    calc exp (lam / (2 * k + 1)) * L = L ^ (2 * e - 1) * L := by
          rw [h2e, rpow_def_of_pos hL]; congr 1; rw [← hlamdef]; ring_nf
      _ = L ^ (2 * e) := by
          rw [← rpow_add_one (by linarith)]; congr 1; ring
      _ = (L ^ e) ^ 2 := by rw [← rpow_natCast, ← rpow_mul (by linarith)]; norm_num; ring_nf
      _ ≤ M ^ 2 := pow_le_pow_left₀ (by positivity) hM0 2
  -- `lam/(2k+1) ≥ lam^{4/5}/2`
  have h15 : (k : ℝ) + 1 ≤ lam ^ ((1 : ℝ) / 5) := hk1
  have hsplit : lam = lam ^ ((4 : ℝ) / 5) * lam ^ ((1 : ℝ) / 5) := by
    rw [← rpow_add hlam0]; norm_num
  have h45 : lam ^ ((4 : ℝ) / 5) / 2 ≤ lam / (2 * k + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]
    have h0 : 0 ≤ lam ^ ((4 : ℝ) / 5) := by positivity
    calc lam ^ ((4 : ℝ) / 5) * (2 * k + 1) ≤ lam ^ ((4 : ℝ) / 5) * (2 * lam ^ ((1 : ℝ) / 5)) := by
          apply mul_le_mul_of_nonneg_left _ h0; linarith
      _ = lam * 2 := by
          rw [show lam ^ ((4 : ℝ) / 5) * (2 * lam ^ ((1 : ℝ) / 5)) =
            2 * (lam ^ ((4 : ℝ) / 5) * lam ^ ((1 : ℝ) / 5)) by ring, ← hsplit]; ring
  -- `exp(lam^{4/5}/2) ≥ lam^{12/5}/48`
  have hcube : (lam ^ ((4 : ℝ) / 5) / 2) ^ 3 / (3 : ℕ).factorial ≤ exp (lam ^ ((4 : ℝ) / 5) / 2) :=
    Real.pow_div_factorial_le_exp _ (by positivity) 3
  have h125 : (lam ^ ((4 : ℝ) / 5)) ^ 3 = lam * lam ^ ((7 : ℝ) / 5) := by
    rw [← rpow_natCast, ← rpow_mul hlam0.le,
      show (4 : ℝ) / 5 * ((3 : ℕ) : ℝ) = 1 + 7 / 5 by norm_num, rpow_add hlam0, rpow_one]
  -- the polynomial side
  have hlogM : log M ≤ lam := by
    have hP : 0 < lam ^ ((7 : ℝ) / 5) := by positivity
    have h1 : 1 ≤ lam ^ ((7 : ℝ) / 5) := one_le_rpow hlam1 (by norm_num)
    have : M ≤ L := by
      calc M ≤ L / lam ^ ((7 : ℝ) / 5) := hM1
        _ ≤ L := div_le_self (by linarith) h1
    calc log M ≤ log L := log_le_log hMpos this
      _ = lam := rfl
  have hk2 : ((k : ℝ) + 1) ^ 2 ≤ lam ^ ((2 : ℝ) / 5) := by
    have : lam ^ ((2 : ℝ) / 5) = (lam ^ ((1 : ℝ) / 5)) ^ 2 := by
      rw [← rpow_natCast, ← rpow_mul hlam0.le]; norm_num
    rw [this]; exact pow_le_pow_left₀ (by positivity) h15 2
  have h725 : lam ^ ((2 : ℝ) / 5) * lam = lam ^ ((7 : ℝ) / 5) := by
    rw [← rpow_add_one hlam0.ne']; norm_num
  have hpoly : 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ 368000 * lam ^ ((7 : ℝ) / 5) := by
    have hl0 : 0 ≤ log M := Real.log_nonneg (by
      have := exp_le_exp.2 (show (0 : ℝ) ≤ lam / (2 * k + 1) by positivity)
      have : (1 : ℝ) ≤ M ^ 2 / L := by rw [exp_zero] at this; linarith
      rw [le_div_iff₀ (by linarith)] at this
      nlinarith)
    have e1 : 19 + 4 * log M ≤ 23 * lam := by linarith
    calc 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ 16000 * lam ^ ((2 : ℝ) / 5) * (23 * lam) := by
          gcongr
      _ = 368000 * (lam ^ ((2 : ℝ) / 5) * lam) := by ring
      _ = 368000 * lam ^ ((7 : ℝ) / 5) := by rw [h725]
  have hP : 0 ≤ lam ^ ((7 : ℝ) / 5) := by positivity
  calc 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ 368000 * lam ^ ((7 : ℝ) / 5) := hpoly
    _ ≤ lam * lam ^ ((7 : ℝ) / 5) / 48 := by nlinarith
    _ = (lam ^ ((4 : ℝ) / 5) / 2) ^ 3 / (3 : ℕ).factorial := by
        rw [div_pow, h125]; norm_num [Nat.factorial]; ring
    _ ≤ exp (lam ^ ((4 : ℝ) / 5) / 2) := hcube
    _ ≤ exp (lam / (2 * k + 1)) := exp_le_exp.2 h45
    _ ≤ M ^ 2 / L := hM2

/-! ## One window -/

set_option maxHeartbeats 4000000 in
/-- **Lemma 7.2.** -/
theorem ct_window {t k x₀ : ℕ} {X M : ℝ} (hk : 1 ≤ k) (hAt : InterpolatingFunctionAt t X)
    (hL : 0 < log (t : ℝ)) (hgood : GoodLam X (log (log t)))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5))
    (hM0 : log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ M)
    (hM1 : M ≤ log (t : ℝ) / log (log t) ^ ((7 : ℝ) / 5))
    (hx₁ : M ≤ x₀) (hx₂ : (x₀ : ℝ) ≤ 2 * M)
    (hH : 16000 * ((k : ℝ) + 1) ^ 2 * (19 + 4 * log M) ≤ M ^ 2 / log (t : ℝ)) :
    (((halfSolutions t).filter fun p => |(p.2 : ℝ) - x₀| ≤ rad k M).card : ℝ) ≤ log t / M := by
  have ht2 : 2 ≤ t := by
    by_contra h; push Not at h; interval_cases t <;> simp at hL
  obtain ⟨hlam9, hX, hlam400, hη⟩ := hgood
  set L := log (t : ℝ) with hLdef
  set lam := log L with hlamdef
  have hLexp : L = exp lam := (exp_log hL).symm
  have hlam1 : 1 ≤ lam := by linarith
  have hL1 : 1 ≤ L := by rw [hLexp]; exact one_le_exp (by linarith)
  obtain ⟨hk1, ha160⟩ := ct_standing hk (by linarith) hst
  have ha := a₀_ge k
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ha1 : 1 ≤ a₀ k := by linarith
  have ha0 : 0 < a₀ k := by linarith
  -- sizes of `M` and `x₀`
  have he : (1 : ℝ) / 2 ≤ ((k : ℝ) + 1) / (2 * k + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hM0' : exp (lam / 2) ≤ M := by
    calc exp (lam / 2) = L ^ ((1 : ℝ) / 2) := by rw [rpow_def_of_pos hL]; congr 1; ring
      _ ≤ L ^ (((k : ℝ) + 1) / (2 * k + 1)) := rpow_le_rpow_of_exponent_le hL1 he
      _ ≤ M := hM0
  have hlam75 : lam ^ ((7 : ℝ) / 5) = lam * lam ^ ((2 : ℝ) / 5) := by
    rw [show (7 : ℝ) / 5 = 1 + 2 / 5 by norm_num, rpow_add (by linarith), rpow_one]
  have hlam25 : lam ^ ((2 : ℝ) / 5) ≤ lam := by
    calc lam ^ ((2 : ℝ) / 5) ≤ lam ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
      _ = lam := rpow_one _
  have hlam15 : lam ^ ((1 : ℝ) / 5) ≤ lam := by
    calc lam ^ ((1 : ℝ) / 5) ≤ lam ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
      _ = lam := rpow_one _
  have hexp_lam : lam / 2 + 1 ≤ exp (lam / 2) := by
    have := add_one_le_exp (lam / 2); linarith
  have hM2 : 2 ≤ M := by linarith
  have hx0pos : (0 : ℝ) < x₀ := by linarith
  have hx0_2 : 2 ≤ x₀ := by exact_mod_cast (show (2 : ℝ) ≤ x₀ by linarith)
  have hP : 0 < lam ^ ((7 : ℝ) / 5) := by positivity
  have hMlam : M * lam ^ ((7 : ℝ) / 5) ≤ L := (le_div_iff₀ hP).1 hM1
  have hP1 : lam ≤ lam ^ ((7 : ℝ) / 5) := by
    rw [hlam75]
    have := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ lam ^ ((2 : ℝ) / 5) by linarith)
      (show (0 : ℝ) ≤ lam by linarith)
    linarith
  have h75 : 1 ≤ lam ^ ((7 : ℝ) / 5) := by linarith
  have hML : M ≤ L := by
    have := le_mul_of_one_le_right (show (0 : ℝ) ≤ M by linarith) h75
    linarith
  have hx0L : (x₀ : ℝ) ≤ 2 * L := by linarith
  have hℓ : lam ^ ((7 : ℝ) / 5) / 2 ≤ L / x₀ := by
    rw [div_le_div_iff₀ (by norm_num) hx0pos]
    have := mul_le_mul_of_nonneg_left hx₂ hP.le
    linarith
  have hlogx0 : log (x₀ : ℝ) ≤ log 2 + lam := by
    calc log (x₀ : ℝ) ≤ log (2 * L) := log_le_log hx0pos hx0L
      _ = log 2 + lam := by rw [log_mul (by norm_num) hL.ne']
  have hl2 := Real.log_two_lt_d9
  -- the hypotheses of Proposition 3.1
  have hXx0 : X ≤ x₀ := hX.trans (hM0'.trans hx₁)
  have h100 : 100 * log (x₀ : ℝ) ≤ L / x₀ := by
    have : 100 * (log 2 + lam) ≤ lam ^ ((7 : ℝ) / 5) / 2 := by
      rw [hlam75]
      have := mul_le_mul_of_nonneg_left hlam400 (show (0 : ℝ) ≤ lam by linarith)
      linarith
    linarith
  obtain ⟨F, κ, hFd, hFn, hκd, hκb, hκ0, hFκ, hFb⟩ := hAt x₀ hXx0 h100
  -- the degree `d` and `T = L/(a₀ x₀)`
  have haM : 0 < a₀ k * M := by positivity
  have hax : 0 < a₀ k * x₀ := by positivity
  obtain ⟨d, hd⟩ : ∃ d, d = ⌊L / (a₀ k * M)⌋₊ := ⟨_, rfl⟩
  have hd1 : (d : ℝ) ≤ L / (a₀ k * M) := by rw [hd]; exact Nat.floor_le (by positivity)
  have hd2 : L / (a₀ k * M) < d + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
  have hLaM : lam ^ ((7 : ℝ) / 5) / a₀ k ≤ L / (a₀ k * M) := by
    rw [div_le_div_iff₀ ha0 haM]
    have := mul_le_mul_of_nonneg_left hMlam ha0.le
    linarith
  have hbig : 40 * ((k : ℝ) + 1) ^ 2 * lam ≤ lam ^ ((7 : ℝ) / 5) / a₀ k := by
    rw [le_div_iff₀ ha0, hlam75]
    have := mul_le_mul_of_nonneg_left hst (show (0 : ℝ) ≤ lam by linarith)
    linarith
  have hT1 : L / (a₀ k * M) ≤ 2 * (L / (a₀ k * x₀)) := by
    rw [div_le_iff₀ haM]
    have : 2 * (L / (a₀ k * x₀)) * (a₀ k * M) = L * (2 * M / x₀) := by field_simp
    rw [this]
    have : 1 ≤ 2 * M / x₀ := by rw [le_div_iff₀ hx0pos]; linarith
    linarith [le_mul_of_one_le_right hL.le this]
  have hT2 : L / (a₀ k * x₀) ≤ L / (a₀ k * M) :=
    div_le_div_of_nonneg_left hL.le haM (mul_le_mul_of_nonneg_left hx₁ ha0.le)
  have hk2l : ((k : ℝ) + 1) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * lam :=
    le_mul_of_one_le_right (by positivity) hlam1
  have hT10 : 10 * ((k : ℝ) + 1) ^ 2 ≤ L / (a₀ k * x₀) := by linarith
  have hdT : (d : ℝ) ≤ 2 * (L / (a₀ k * x₀)) := hd1.trans hT1
  have hηk : (k : ℝ) * η₀ x₀ (L / x₀) ≤ 0.09 := by
    have h1 := ct_eta (x₀ := x₀) (ℓ := L / x₀) (by linarith) (hM0'.trans hx₁) (by linarith)
    have h2 : 0 ≤ 12 * exp (-(1 / 4) * lam) + 2 * exp (-(1 / 10) * lam) := by positivity
    calc (k : ℝ) * η₀ x₀ (L / x₀) ≤ k * (12 * exp (-(1 / 4) * lam) + 2 * exp (-(1 / 10) * lam)) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ lam ^ ((1 : ℝ) / 5) * (12 * exp (-(1 / 4) * lam) + 2 * exp (-(1 / 10) * lam)) :=
          mul_le_mul_of_nonneg_right (by linarith) h2
      _ ≤ 0.09 := by linarith
  -- comparing radii
  have hα0 : (0 : ℝ) ≤ (k : ℝ) / (k + 1) := by positivity
  have hα1 : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hM2' : 1 ≤ M / 2 := by linarith
  have hrM1 : (M / 2) ^ ((k : ℝ) / (k + 1)) ≤ M / 2 := by
    calc (M / 2) ^ ((k : ℝ) / (k + 1)) ≤ (M / 2) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hM2' hα1
      _ = M / 2 := rpow_one _
  have hexp1 : exp (-(2 * a₀ k) - 1) * (2 * a₀ k) ≤ 1 := by
    have h := add_one_le_exp (2 * a₀ k + 1)
    have h' : exp (-(2 * a₀ k) - 1) * exp (2 * a₀ k + 1) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    have := mul_le_mul_of_nonneg_left (show 2 * a₀ k ≤ exp (2 * a₀ k + 1) by linarith)
      (exp_pos (-(2 * a₀ k) - 1)).le
    linarith
  have hrad_zero : rad k M ≤ x₀ / (4 * a₀ k) := by
    unfold rad
    rw [le_div_iff₀ (by positivity)]
    have h0 : 0 ≤ exp (-(2 * a₀ k) - 1) := (exp_pos _).le
    have : (M / 2) ^ ((k : ℝ) / (k + 1)) * exp (-(2 * a₀ k) - 1) * (4 * a₀ k) ≤
        M / 2 * exp (-(2 * a₀ k) - 1) * (4 * a₀ k) := by gcongr
    have := mul_le_mul_of_nonneg_left hexp1 (show (0 : ℝ) ≤ M by linarith)
    linarith
  have hrad_half : rad k M ≤ x₀ / 2 := by
    refine hrad_zero.trans ?_
    exact div_le_div_of_nonneg_left hx0pos.le (by norm_num) (by linarith)
  have hrad_wr : rad k M ≤ windowRadius x₀ k d (L / x₀) := by
    unfold rad windowRadius
    apply mul_le_mul (rpow_le_rpow (by linarith) (by linarith) hα0) _ (exp_pos _).le
      (by positivity)
    apply exp_le_exp.2
    have hd0 : (0 : ℝ) < d + 1 := by positivity
    rw [neg_div]
    suffices hQ : (2 * (L / x₀) + log (3 * x₀) + 2 * log (((k : ℝ) + 1) * (d + 1)) + 1) / (d + 1)
        ≤ 2 * a₀ k + 1 by linarith
    rw [div_le_iff₀ hd0]
    -- `L/x₀ ≤ a₀ (d+1)`
    have hq : L / x₀ ≤ a₀ k * (d + 1) := by
      have h1 : L / x₀ ≤ L / M := div_le_div_of_nonneg_left hL.le (by linarith) hx₁
      have h2 : L / M = a₀ k * (L / (a₀ k * M)) := by field_simp
      have h3 := mul_le_mul_of_nonneg_left hd2.le ha0.le
      linarith
    have hl3 : log (3 * (x₀ : ℝ)) ≤ log 6 + lam := by
      calc log (3 * (x₀ : ℝ)) ≤ log (6 * L) := log_le_log (by positivity) (by linarith)
        _ = log 6 + lam := by rw [log_mul (by norm_num) hL.ne']
    have hl6 : log (6 : ℝ) ≤ 3 * log 2 := by
      have := log_le_log (by norm_num : (0 : ℝ) < 6) (by norm_num : (6 : ℝ) ≤ 2 ^ 3)
      rwa [Real.log_pow, Nat.cast_ofNat] at this
    have hdL : (d : ℝ) + 1 ≤ 2 * L := by
      have : L / (a₀ k * M) ≤ L := div_le_self hL.le (by
        have := mul_le_mul ha1 (show (1 : ℝ) ≤ M by linarith) zero_le_one ha0.le
        linarith)
      linarith
    have hlD : log (((k : ℝ) + 1) * (d + 1)) ≤ (k + 1) + (log 2 + lam) := by
      rw [log_mul (by positivity) (by positivity)]
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k + 1 by positivity)
      have h2 : log ((d : ℝ) + 1) ≤ log (2 * L) := log_le_log (by positivity) hdL
      rw [log_mul (by norm_num) hL.ne'] at h2
      linarith
    have hdbig : 40 * ((k : ℝ) + 1) ^ 2 * lam < d + 1 := by linarith
    have hkk : (k : ℝ) + 1 ≤ ((k : ℝ) + 1) ^ 2 := by
      have := le_mul_of_one_le_right (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
        (show (1 : ℝ) ≤ (k : ℝ) + 1 by linarith)
      linarith [sq ((k : ℝ) + 1)]
    have hkl : ((k : ℝ) + 1) ≤ ((k : ℝ) + 1) ^ 2 * lam := hkk.trans hk2l
    have hl1 : lam ≤ ((k : ℝ) + 1) ^ 2 * lam :=
      le_mul_of_one_le_left (by linarith) (by nlinarith only [hK])
    have h36 : 36 ≤ ((k : ℝ) + 1) ^ 2 * lam := by nlinarith only [hK, hlam9]
    have h3 := mul_le_mul_of_nonneg_left hq (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  -- the count
  set S := (halfSolutions t).filter fun p => |(p.2 : ℝ) - x₀| ≤ rad k M with hSdef
  have hLMβ : 1 ≤ L / M := by rw [le_div_iff₀ (by linarith)]; linarith
  have hdβ : (d : ℝ) ≤ L / M := by
    have : L / (a₀ k * M) ≤ L / M :=
      div_le_div_of_nonneg_left hL.le (by linarith) (by nlinarith)
    linarith
  have hδ3 : exp (-L / 8) ≤ δ₃ x₀ k d (L / x₀) :=
    ct_delta3 hk hM2 hML hx₁ hx₂ hdβ hLMβ hH
  have hδ5 : exp (-L / 8) ≤ δ₅ k x₀ (L / (a₀ k * x₀)) :=
    ct_delta5 hk hM2 hML hx₁ hx₂ ha1 hLMβ hH
  have hSprop : ∀ p ∈ S, |(p.2 : ℝ) - x₀| ≤ windowRadius x₀ k d (L / x₀) ∧
      ‖F p.2 - p.1‖ ≤ exp (-L / 8) := by
    intro p hp
    rw [hSdef, Finset.mem_filter, mem_halfSolutions ht2] at hp
    exact ⟨hp.2.trans hrad_wr, hFn p.1 p.2 hp.1.1 hp.1.2 (hp.2.trans hrad_half)⟩
  have hLM : L / M = a₀ k * (L / (a₀ k * M)) := by field_simp
  have hq0 : 0 ≤ L / (a₀ k * M) := by positivity
  by_cases hcard : (k + 1) * (d + 1) ≤ S.card
  · obtain ⟨A, hA0, hAd, hAv⟩ :=
      solutions_on_curve (ℓ := L / x₀) (δ := exp (-L / 8)) hk hx0_2 (by positivity) hFd hFb
        (exp_pos _).le hδ3 S hSprop
    have hZcard : (S.image fun p => ((p.2 : ℕ) : ℂ)).card = S.card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      have h' : p.2 = q.2 := by simpa using hpq
      exact halfSolutions_injOn_snd ht2 (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hq).1 h'
    have hcast : ((x₀ : ℝ) : ℂ) = (x₀ : ℂ) := Complex.ofReal_natCast x₀
    have hZ : ∀ z ∈ S.image fun p => ((p.2 : ℕ) : ℂ), ‖z - ((x₀ : ℝ) : ℂ)‖ ≤ x₀ / (4 * a₀ k) ∧
        ∃ w : ℂ, ∑ b : Fin (k + 1), (A b).eval z * w ^ (b : ℕ) = 0 ∧ ‖F z - w‖ ≤ exp (-L / 8) := by
      intro z hz
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hz
      refine ⟨?_, ((p.1 : ℕ) : ℂ), hAv p hp, (hSprop p hp).2⟩
      rw [hcast]
      have h1 := (Finset.mem_filter.1 hp).2
      have : ‖((p.2 : ℕ) : ℂ) - (x₀ : ℂ)‖ = |(p.2 : ℝ) - x₀| := by
        rw [show ((p.2 : ℕ) : ℂ) - (x₀ : ℂ) = (((p.2 : ℝ) - x₀ : ℝ) : ℂ) by push_cast; ring,
          Complex.norm_real, Real.norm_eq_abs]
      rw [this]; exact h1.trans hrad_zero
    have hsep : ∀ z ∈ S.image fun p => ((p.2 : ℕ) : ℂ), ∀ z' ∈ S.image fun p => ((p.2 : ℕ) : ℂ),
        z ≠ z' → 1 ≤ ‖z - z'‖ := by
      intro z hz z' hz' hne
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hz
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hz'
      have hne' : p.2 ≠ q.2 := fun h => hne (by rw [h])
      rw [show ((p.2 : ℕ) : ℂ) - ((q.2 : ℕ) : ℂ) = (((p.2 : ℝ) - q.2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      rcases Nat.lt_or_gt_of_ne hne' with h | h
      · have : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast h
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast h
        rw [abs_of_nonneg (by linarith)]; linarith
    have h := zero_estimate k d L x₀ (η₀ x₀ (L / x₀)) (exp (-L / 8)) F κ hk (by linarith) hT10 hdT
      hηk (by rw [hcast]; exact hκd) (by rw [hcast]; exact hκb) (by rw [hcast]; exact hκ0)
      (by rw [hcast]; exact hFκ) (exp_pos _).le hδ5 A hA0 hAd _ hZ hsep
    rw [hZcard] at h
    have h17 : 17 * (4 * (k : ℝ) + 3) ≤ a₀ k := by linarith
    calc (S.card : ℝ) ≤ 17 * (4 * k + 3) * (L / (a₀ k * x₀)) := h
      _ ≤ 17 * (4 * k + 3) * (L / (a₀ k * M)) := by gcongr
      _ ≤ a₀ k * (L / (a₀ k * M)) := mul_le_mul_of_nonneg_right h17 hq0
      _ = L / M := hLM.symm
  · push Not at hcard
    have h1 : (S.card : ℝ) + 1 ≤ ((k : ℝ) + 1) * (d + 1) := by exact_mod_cast hcard
    have hLM' : lam ^ ((7 : ℝ) / 5) ≤ L / M := by rw [le_div_iff₀ (by linarith)]; linarith
    have h2k : 2 * (k : ℝ) ≤ L / M := by rw [hlam75] at hLM'; nlinarith
    have h2a : 2 * ((k : ℝ) + 1) ≤ a₀ k := by linarith
    rw [hLM] at h2k ⊢
    have e1 := mul_le_mul_of_nonneg_right h2a hq0
    have e2 := mul_le_mul_of_nonneg_left (show (d : ℝ) + 1 ≤ L / (a₀ k * M) + 1 by linarith)
      (show (0 : ℝ) ≤ (k : ℝ) + 1 by positivity)
    linarith

end Singmaster
