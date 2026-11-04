module

public import Singmaster.ZeroEstimate.Setup

@[expose] public section

/-!
# Proposition 6.1: the zero estimate

The points `z ∈ Z` are at mutual distance at least `1` and carry numbers `w_z` with
`∑_b A_b(z) w_z^b = 0` and `|F(z) - w_z| ≤ δ ≤ δ₅`. Then `|Z| ≤ 17(4k+3)T` (`zero_estimate`).
The points `s_z = (1/z - u₀)/ρ` are near-zeros of `G`, by (6.8) (`ze_near_zero`). We subtract the
Lagrange interpolation polynomial of `G` at these points, which is at most `m₀/4` by (6.9)
(`ze_num_lagrange`), and apply Jensen's formula to the difference (`ze_card_le`).
-/

open Complex Polynomial Metric Real Finset

namespace Singmaster

/-- The tolerance `δ₅ = exp(-1000 (k+1)² (T+1) log(6x₀+6))` of Proposition 6.1. -/
noncomputable def δ₅ (k : ℕ) (x₀ T : ℝ) : ℝ :=
  Real.exp (-(1000 * ((k : ℝ) + 1) ^ 2 * (T + 1) * Real.log (6 * x₀ + 6)))

/-! ## Numerics -/

/-- `log(4 N 3^N e^{10N} + 3) ≤ 17 N log 2` for `N ≥ 80`. -/
lemma ze_jensen_core {x : ℝ} (hx : 80 ≤ x) (n : ℕ) (hn : (n : ℝ) = x) :
    Real.log (4 * (x * 3 ^ n * Real.exp (10 * x)) + 3) ≤ 17 * x * Real.log 2 := by
  have hx0 : 0 < x := by linarith
  have h3 : (0 : ℝ) < 3 ^ n := by positivity
  have hY0 : 0 < x * 3 ^ n * Real.exp (10 * x) := by positivity
  have hY1 : 1 ≤ x * 3 ^ n * Real.exp (10 * x) := by
    have a : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    have b : (1 : ℝ) ≤ Real.exp (10 * x) := Real.one_le_exp (by linarith)
    have c : (1 : ℝ) ≤ x * 3 ^ n := by nlinarith
    nlinarith
  have hle : 4 * (x * 3 ^ n * Real.exp (10 * x)) + 3 ≤ 2 ^ 3 * (x * 3 ^ n * Real.exp (10 * x)) := by
    norm_num; linarith
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by norm_num) hY0.ne', Real.log_mul (by positivity) (Real.exp_pos _).ne',
    Real.log_mul hx0.ne' h3.ne', Real.log_pow, Real.log_pow, Real.log_exp, hn] at hlog
  have hl3 : Real.log (3 : ℝ) ≤ 2 * Real.log 2 := by
    have := log_le_of_le_two_pow (x := 3) (m := 2) (by norm_num) (by norm_num)
    push_cast at this; linarith
  have hlx := num_log_le_quarter hx0
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have p1 : x * Real.log 3 ≤ x * (2 * Real.log 2) := mul_le_mul_of_nonneg_left hl3 hx0.le
  have p2 : x * 0.6931471803 ≤ x * Real.log 2 := mul_le_mul_of_nonneg_left hl2'.le hx0.le
  push_cast at hlog
  linarith

/-- The Jensen bound for `G - e`: `log(4 C_a + 3)/log 2 ≤ 17 (4k+3) T`. -/
lemma ze_num_jensen {k N : ℕ} {T : ℝ} (hk : 1 ≤ k)
    (hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ T) (hN1 : 2 * k * T ≤ N) (hN : (N : ℝ) ≤ (4 * k + 3) * T) :
    Real.log (4 * (N * 3 ^ N * Real.exp (5 * max (2 * k * T) (2 * N))) + 3) / Real.log 2 ≤
      17 * (4 * k + 3) * T := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have hT40 : (40 : ℝ) ≤ T := by linarith
  have hkT : T ≤ (k : ℝ) * T := by
    have := mul_le_mul_of_nonneg_right hK (by linarith : (0 : ℝ) ≤ T)
    linarith
  have hN80 : (80 : ℝ) ≤ N := by linarith
  have hmax : max (2 * (k : ℝ) * T) (2 * N) = 2 * N := max_eq_right (by linarith)
  rw [hmax, show 5 * (2 * (N : ℝ)) = 10 * N by ring]
  have hl0 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  rw [div_le_iff₀ hl0]
  have hcore := ze_jensen_core hN80 N rfl
  have : 17 * (N : ℝ) * Real.log 2 ≤ 17 * ((4 * k + 3) * T) * Real.log 2 := by
    apply mul_le_mul_of_nonneg_right _ hl0.le
    linarith
  linarith

/-- `log(6x₀+6) ≥ 1`. -/
lemma ze_log_ge {x₀ : ℝ} (hx : 1 ≤ x₀) : 1 ≤ Real.log (6 * x₀ + 6) := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- `2 e³ δ ≤ 1`. -/
lemma ze_delta_small {k : ℕ} {x₀ T δ : ℝ} (hx : 1 ≤ x₀) (hT : 0 ≤ T)
    (hδ : δ ≤ δ₅ k x₀ T) : 2 * Real.exp 3 * δ ≤ 1 := by
  have hℓ := ze_log_ge hx
  have hk : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    have : (1 : ℝ) ≤ (k : ℝ) + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
    nlinarith
  have hP : 4 ≤ 1000 * ((k : ℝ) + 1) ^ 2 * (T + 1) * Real.log (6 * x₀ + 6) := by
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * (T + 1) := by nlinarith
    have h2 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 * (T + 1) * Real.log (6 * x₀ + 6) := by nlinarith
    linarith
  have h1 : δ ≤ Real.exp (-4) := hδ.trans (Real.exp_le_exp.2 (by linarith))
  have h2 : 2 * Real.exp 3 * Real.exp (-4) ≤ 1 := by
    rw [mul_assoc, ← Real.exp_add]
    have := Real.add_one_le_exp 1
    have e : Real.exp (3 + -4) = (Real.exp 1)⁻¹ := by rw [← Real.exp_neg]; norm_num
    rw [e, ← div_eq_mul_inv, div_le_one (Real.exp_pos 1)]
    linarith
  have := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * Real.exp 3)
  linarith

/-- The exponent bookkeeping of `ze_num_lagrange`. -/
lemma ze_lin {k T ℓ N₁ L16 : ℝ} (hk1 : 1 ≤ k) (hT : 10 * (k + 1) ^ 2 ≤ T) (hℓ : 1 ≤ ℓ)
    (hN₁ : N₁ ≤ 17 * (4 * k + 3) * T + 1) (hL16 : L16 ≤ 16 * k + 11) :
    17.6 + N₁ + (k + 1) + (T + (17.5 * k + 7) * T + (4 * k + 2) * T + (4 * k + 3) * T * L16) +
      2 * k + 3 + -(1000 * ((k + 1) ^ 2 * (T + 1) * ℓ)) + N₁ * ℓ ≤ 0 := by
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  have hA : (4 * k + 3) * T * L16 ≤ (4 * k + 3) * T * (16 * k + 11) :=
    mul_le_mul_of_nonneg_left hL16 (by positivity)
  have hB : (4 * k + 3) * T * (16 * k + 11) ≤ 64 * ((k + 1) ^ 2 * T) := by
    have : (4 * k + 3) * (16 * k + 11) ≤ 64 * (k + 1) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_right this hT0
    linarith
  have hKK : k + 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hKT : (k + 1) * T ≤ (k + 1) ^ 2 * T := mul_le_mul_of_nonneg_right hKK hT0
  have hA1 : (k + 1) ^ 2 * T ≤ (k + 1) ^ 2 * T * ℓ := le_mul_of_one_le_right (by positivity) hℓ
  have hK2 : 1 ≤ (k + 1) ^ 2 := by nlinarith
  have hA2 : 1 ≤ (k + 1) ^ 2 * ℓ := by nlinarith
  have hKA2 : k + 1 ≤ (k + 1) ^ 2 * ℓ := by nlinarith
  have hℓA2 : ℓ ≤ (k + 1) ^ 2 * ℓ := le_mul_of_one_le_left (by linarith) hK2
  have hKTℓ : (k + 1) * T * ℓ ≤ (k + 1) ^ 2 * T * ℓ := mul_le_mul_of_nonneg_right hKT (by linarith)
  have hN₁' : N₁ ≤ 68 * ((k + 1) * T) + 1 := by
    have := mul_le_mul_of_nonneg_right (show 17 * (4 * k + 3) ≤ 68 * (k + 1) by linarith) hT0
    linarith
  have hN₁ℓ : N₁ * ℓ ≤ 68 * ((k + 1) * T * ℓ) + ℓ := by
    have := mul_le_mul_of_nonneg_right hN₁' (by linarith : (0 : ℝ) ≤ ℓ)
    linarith
  have hXe' : T + (17.5 * k + 7) * T + (4 * k + 2) * T ≤ 22 * ((k + 1) * T) := by nlinarith
  have hexp : (k + 1) ^ 2 * (T + 1) * ℓ = (k + 1) ^ 2 * T * ℓ + (k + 1) ^ 2 * ℓ := by ring
  rw [hexp]
  linarith

/-- Inequality (6.9): the Lagrange interpolation polynomial is at most `m₀/4`. -/
lemma ze_num_lagrange {k N₁ : ℕ} {T x₀ δ X : ℝ} (hk : 1 ≤ k)
    (hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ T) (hN₁ : (N₁ : ℝ) ≤ 17 * (4 * k + 3) * T + 1) (hx : 1 ≤ x₀)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ₅ k x₀ T) (hX0 : 0 ≤ X)
    (hX : X ≤ Real.exp (T + (17.5 * k + 7) * T + (4 * k + 2) * T +
      (4 * k + 3) * T * Real.log (16 * k + 12))) :
    4 * ((N₁ : ℝ) * (((k : ℝ) + 1) * (2.2 * X) * (3 ^ k * (2 * Real.exp 3 * δ))) * x₀ ^ N₁) ≤ 1 := by
  have hℓ : 1 ≤ Real.log (6 * x₀ + 6) := ze_log_ge hx
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hx0 : 0 < x₀ := by linarith
  have hc : (17.6 : ℝ) ≤ Real.exp 17.6 := by linarith [Real.add_one_le_exp (17.6 : ℝ)]
  have hN₁e : (N₁ : ℝ) ≤ Real.exp N₁ := by linarith [Real.add_one_le_exp (N₁ : ℝ)]
  have hKe : (k : ℝ) + 1 ≤ Real.exp ((k : ℝ) + 1) := by linarith [Real.add_one_le_exp ((k : ℝ) + 1)]
  have h3e : (3 : ℝ) ^ k ≤ Real.exp (2 * k) := by
    rw [num_pow_eq_exp (by norm_num)]
    apply Real.exp_le_exp.2
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
    nlinarith
  have hxe : x₀ ^ N₁ ≤ Real.exp (N₁ * Real.log (6 * x₀ + 6)) := by
    rw [num_pow_eq_exp hx0]
    apply Real.exp_le_exp.2
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    exact Real.log_le_log hx0 (by linarith)
  have hδe : δ ≤ Real.exp (-(1000 * (((k : ℝ) + 1) ^ 2 * (T + 1) * Real.log (6 * x₀ + 6)))) := by
    refine hδ.trans (le_of_eq ?_)
    unfold δ₅; congr 1; ring
  have step : 4 * ((N₁ : ℝ) * (((k : ℝ) + 1) * (2.2 * X) * (3 ^ k * (2 * Real.exp 3 * δ))) *
      x₀ ^ N₁) = 17.6 * N₁ * ((k : ℝ) + 1) * X * 3 ^ k * Real.exp 3 * δ * x₀ ^ N₁ := by ring
  rw [step]
  have step2 : 17.6 * N₁ * ((k : ℝ) + 1) * X * 3 ^ k * Real.exp 3 * δ * x₀ ^ N₁ ≤
      Real.exp 17.6 * Real.exp N₁ * Real.exp ((k : ℝ) + 1) *
        Real.exp (T + (17.5 * k + 7) * T + (4 * k + 2) * T +
          (4 * k + 3) * T * Real.log (16 * k + 12)) * Real.exp (2 * k) * Real.exp 3 *
        Real.exp (-(1000 * (((k : ℝ) + 1) ^ 2 * (T + 1) * Real.log (6 * x₀ + 6)))) *
        Real.exp (N₁ * Real.log (6 * x₀ + 6)) := by
    gcongr
  refine step2.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_one_iff]
  have hlog16 : Real.log (16 * k + 12) ≤ 16 * k + 11 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 * k + 12 by positivity)
    linarith
  exact ze_lin hk1 hT hℓ hN₁ hlog16

/-! ## Lagrange interpolation -/

/-- The Lagrange interpolation polynomial of `f` at the nodes `W`, as a function. -/
noncomputable def ze_lag (W : Finset ℂ) (f : ℂ → ℂ) (s : ℂ) : ℂ :=
  ∑ w ∈ W, f w * ∏ w' ∈ W.erase w, ((s - w') / (w - w'))

/-- `e` interpolates `f` at the nodes. -/
lemma ze_lag_eval (W : Finset ℂ) (f : ℂ → ℂ) {v : ℂ} (hv : v ∈ W) : ze_lag W f v = f v := by
  classical
  unfold ze_lag
  rw [Finset.sum_eq_single v]
  · rw [Finset.prod_eq_one, mul_one]
    intro w' hw'
    exact div_self (sub_ne_zero.2 (Finset.ne_of_mem_erase hw').symm)
  · intro w _ hwv
    rw [Finset.prod_eq_zero (i := v) (Finset.mem_erase.2 ⟨Ne.symm hwv, hv⟩) (by simp), mul_zero]
  · intro h; exact absurd hv h

lemma ze_lag_diff (W : Finset ℂ) (f : ℂ → ℂ) : Differentiable ℂ (ze_lag W f) := by
  unfold ze_lag
  fun_prop

/-- With nodes in `|s| ≤ 1/3`, `5/x₀` apart, `|e| ≤ |W| B x₀^{|W|}` on `|s| ≤ 4`. -/
lemma ze_lag_bound (W : Finset ℂ) (f : ℂ → ℂ) {x₀ B : ℝ} (hx : 1 ≤ x₀)
    (hW : ∀ w ∈ W, ‖w‖ ≤ 1 / 3) (hsep : ∀ w ∈ W, ∀ w' ∈ W, w ≠ w' → 5 / x₀ ≤ ‖w - w'‖)
    (hf : ∀ w ∈ W, ‖f w‖ ≤ B) {s : ℂ} (hs : ‖s‖ ≤ 4) :
    ‖ze_lag W f s‖ ≤ W.card * B * x₀ ^ W.card := by
  classical
  unfold ze_lag
  refine (norm_sum_le _ _).trans ?_
  have hx0 : 0 < x₀ := by linarith
  have hterm : ∀ w ∈ W, ‖f w * ∏ w' ∈ W.erase w, ((s - w') / (w - w'))‖ ≤ B * x₀ ^ W.card := by
    intro w hw
    rw [norm_mul, norm_prod]
    have hB : 0 ≤ B := (norm_nonneg _).trans (hf w hw)
    have hfac : ∀ w' ∈ W.erase w, ‖(s - w') / (w - w')‖ ≤ x₀ := by
      intro w' hw'
      obtain ⟨hne, hw'W⟩ := Finset.mem_erase.1 hw'
      have h1 : ‖s - w'‖ ≤ 5 := by
        have := hW w' hw'W
        have := norm_sub_le s w'
        linarith
      have h2 := hsep w hw w' hw'W (Ne.symm hne)
      have h3 : 0 < ‖w - w'‖ := lt_of_lt_of_le (by positivity) h2
      rw [norm_div, div_le_iff₀ h3]
      calc ‖s - w'‖ ≤ 5 := h1
        _ = x₀ * (5 / x₀) := by field_simp
        _ ≤ x₀ * ‖w - w'‖ := mul_le_mul_of_nonneg_left h2 hx0.le
    have hprod : ∏ w' ∈ W.erase w, ‖(s - w') / (w - w')‖ ≤ x₀ ^ W.card := by
      calc ∏ w' ∈ W.erase w, ‖(s - w') / (w - w')‖ ≤ ∏ _w' ∈ W.erase w, x₀ :=
            Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) hfac
        _ = x₀ ^ (W.erase w).card := Finset.prod_const _
        _ ≤ x₀ ^ W.card := pow_le_pow_right₀ hx Finset.card_erase_le
    exact mul_le_mul (hf w hw) hprod (by positivity) hB
  calc ∑ w ∈ W, ‖f w * ∏ w' ∈ W.erase w, ((s - w') / (w - w'))‖
      ≤ ∑ _w ∈ W, B * x₀ ^ W.card := Finset.sum_le_sum hterm
    _ = W.card * B * x₀ ^ W.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- `|r^j - 1| ≤ 3^j ε` if `|r - 1| ≤ ε ≤ 1`. -/
lemma ze_pow_sub_one_le {r : ℂ} {ε : ℝ} (hε : ε ≤ 1) (hr : ‖r - 1‖ ≤ ε) (j : ℕ) :
    ‖r ^ j - 1‖ ≤ 3 ^ j * ε := by
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hr
  have hr2 : ‖r‖ ≤ 2 := by
    calc ‖r‖ = ‖(r - 1) + 1‖ := by ring_nf
      _ ≤ ‖r - 1‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ ≤ 2 := by rw [norm_one]; linarith
  induction j with
  | zero => simp [hε0]
  | succ n ih =>
    have e : r ^ (n + 1) - 1 = r * (r ^ n - 1) + (r - 1) := by ring
    rw [e]
    have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
    calc ‖r * (r ^ n - 1) + (r - 1)‖ ≤ ‖r‖ * ‖r ^ n - 1‖ + ‖r - 1‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_mul]
      _ ≤ 2 * (3 ^ n * ε) + ε := by gcongr
      _ ≤ 3 ^ (n + 1) * ε := by
          rw [pow_succ]
          have : ε ≤ 3 ^ n * ε := le_mul_of_one_le_left hε0 h3
          linarith

/-! ## Near-zeros of `G`, and the Jensen step for `G - e` -/

namespace ZeroData

variable (D : ZeroData)

/-- The constant `C_b` of Lemma 5.1(b) for the data `D`. -/
noncomputable def ze_Bb : ℝ := 2 * ((∑ j, D.n j : ℕ) : ℝ) *
    (((D.k : ℝ) + 1) * 2 ^ (4 * D.k + 2)) ^ (Finset.univ.sup D.n) *
    Real.exp ((4 * D.k + 2) * D.T) * max 1 ((4 * ((∑ j, D.n j : ℕ) : ℝ) / D.T) ^ (∑ j, D.n j))

lemma ze_Bb_nonneg : 0 ≤ D.ze_Bb := by unfold ze_Bb; positivity

/-- `C_b ≤ e^{T + (17.5k+7)T + (4k+2)T + (4k+3)T log(16k+12)}`, as in (6.5). -/
lemma ze_Bb_le : D.ze_Bb ≤ Real.exp (D.T + (17.5 * D.k + 7) * D.T + (4 * D.k + 2) * D.T +
    (4 * D.k + 3) * D.T * Real.log (16 * D.k + 12)) := by
  have hk1 := D.k_ge
  have e1 := num_trunc_f1 D.T_ge D.N_le
  have e2 := num_trunc_f2 (k := D.k) D.T_pos.le D.nmax_le
  have e4 := num_trunc_f4 D.T_pos D.N_le
  have h2N : 2 * ((∑ j, D.n j : ℕ) : ℝ) ≤ Real.exp D.T := by
    have : (0 : ℝ) ≤ ((∑ j, D.n j : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  unfold ze_Bb
  rw [Real.exp_add, Real.exp_add, Real.exp_add]
  gcongr

/-- `|Q_j(u) E^j| = |q_j(s) e^{jTs} K(s)^j| ≤ 2.2 C_b m₀` on `|s| ≤ 4`. -/
lemma ze_term_le {M : ℝ} (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M)
    (j : Fin (D.k + 1)) {s : ℂ} (hs : ‖s‖ ≤ 4) :
    ‖(cvP D.k D.d D.A j).eval (D.u₀ + (D.ρ : ℂ) * s) *
      cexp ((D.L : ℂ) * (D.u₀ + (D.ρ : ℂ) * s) + D.κ (D.u₀ + (D.ρ : ℂ) * s)) ^ (j : ℕ)‖ ≤
      2.2 * (D.ze_Bb * M) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hL4 : ‖(D.R j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)‖ ≤ D.ze_Bb * M :=
    (expPoly_bound D.T_pos D.n D.R D.R_degree hM).2 j s hs
  obtain ⟨-, hb2⟩ := D.Pi_bounds j (s := s) (by linarith)
  have hK := D.Kpow_near j (s := s) (mem_closedBall_zero_iff.2 (by linarith [D.a_ge]))
  have hKn : ‖D.K s ^ (j : ℕ)‖ ≤ 1.1 := by
    have := norm_sub_norm_le (D.K s ^ (j : ℕ)) 1
    rw [norm_one] at this
    linarith
  have e : (cvP D.k D.d D.A j).eval (D.u₀ + (D.ρ : ℂ) * s) *
      cexp ((D.L : ℂ) * (D.u₀ + (D.ρ : ℂ) * s) + D.κ (D.u₀ + (D.ρ : ℂ) * s)) ^ (j : ℕ) =
      ((D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)) * D.K s ^ (j : ℕ) := by
    rw [D.q_eval, ← D.exp_identity]; ring
  rw [e, norm_mul]
  have hR : ‖(D.R j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)‖ =
      ‖(D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)‖ * ‖(D.Pi j).eval s‖ := by
    rw [R, eval_mul, mul_right_comm, norm_mul]
  have hqe : ‖(D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s)‖ ≤ 2 * (D.ze_Bb * M) := by
    have := norm_nonneg ((D.q j).eval s * cexp ((((j : ℕ) : ℂ) * (D.T : ℂ)) * s))
    nlinarith
  have hBM : 0 ≤ D.ze_Bb * M := mul_nonneg D.ze_Bb_nonneg hM0
  calc _ ≤ 2 * (D.ze_Bb * M) * 1.1 := mul_le_mul hqe hKn (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- `|z| ≤ 2 x₀`. -/
lemma ze_z_le {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) : ‖z‖ ≤ 2 * D.x₀ := by
  have hx := D.x₀_pos
  have h1 : ‖z‖ ≤ ‖z - (D.x₀ : ℂ)‖ + ‖(D.x₀ : ℂ)‖ := by
    calc ‖z‖ = ‖(z - (D.x₀ : ℂ)) + (D.x₀ : ℂ)‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [Complex.norm_real, Real.norm_of_nonneg hx.le] at h1
  have h2 : D.x₀ / (4 * a₀ D.k) ≤ D.x₀ :=
    div_le_self hx.le (by linarith [D.a_ge])
  linarith

/-- Inequality (6.3): points at distance at least `1` give nodes `s_z` at least `5/x₀` apart. -/
lemma ze_sz_sep {z z' : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k))
    (hz' : ‖z' - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k)) (h1 : 1 ≤ ‖z - z'‖) :
    5 / D.x₀ ≤ ‖D.sz z - D.sz z'‖ := by
  have hx := D.x₀_pos
  have ha := D.a_ge
  have hz0 := D.z_ne_zero hz
  have hz0' := D.z_ne_zero hz'
  have hρ : (D.ρ : ℂ) ≠ 0 := by exact_mod_cast D.ρ_pos.ne'
  have e : D.sz z - D.sz z' = (z' - z) / (z * z' * (D.ρ : ℂ)) := by
    unfold sz; field_simp; ring
  rw [e, norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg D.ρ_pos.le,
    norm_sub_rev]
  have hzn := D.ze_z_le hz
  have hzn' := D.ze_z_le hz'
  have hpos : 0 < ‖z‖ * ‖z'‖ * D.ρ := by
    have := norm_pos_iff.2 hz0
    have := norm_pos_iff.2 hz0'
    have := D.ρ_pos
    positivity
  rw [div_le_div_iff₀ hx hpos]
  have hρe : D.ρ * a₀ D.k * D.x₀ = 1 := by unfold ρ; field_simp
  have hzz : ‖z‖ * ‖z'‖ ≤ 4 * D.x₀ ^ 2 := by
    have := norm_nonneg z
    have := norm_nonneg z'
    nlinarith
  -- 5 ‖z‖‖z'‖ρ ≤ 20 x₀² ρ = 20 x₀/a ≤ x₀ ≤ ‖z - z'‖ x₀
  have h20 : 5 * (‖z‖ * ‖z'‖ * D.ρ) ≤ 20 * D.x₀ ^ 2 * D.ρ := by
    have := D.ρ_pos
    nlinarith
  have h21 : 20 * D.x₀ ^ 2 * D.ρ ≤ D.x₀ := by
    have : 20 * D.x₀ ^ 2 * D.ρ * a₀ D.k = 20 * D.x₀ := by
      calc 20 * D.x₀ ^ 2 * D.ρ * a₀ D.k = 20 * D.x₀ * (D.ρ * a₀ D.k * D.x₀) := by ring
        _ = 20 * D.x₀ := by rw [hρe, mul_one]
    have hρ0 := D.ρ_pos
    nlinarith
  nlinarith

/-- `Re(L u + κ(u)) ≥ -2` for `u = 1/z`, so `|E| ≥ e^{-2}`. -/
lemma ze_re_ge {z : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k))
    (hκ0 : ‖D.κ (D.x₀ : ℂ)⁻¹‖ ≤ 1)
    (hmem : z⁻¹ ∈ Metric.closedBall ((D.x₀ : ℂ)⁻¹) (D.x₀⁻¹ / 2)) :
    -2 ≤ ((D.L : ℂ) * z⁻¹ + D.κ z⁻¹).re := by
  have hx := D.x₀_pos
  have ha := D.a_ge
  have hL : 0 ≤ D.L := by
    have e : D.L = D.T * (a₀ D.k * D.x₀) := by
      unfold T; have := D.a_pos.ne'; field_simp
    rw [e]; have := D.T_pos; have := D.a_pos; positivity
  have hzre : 0 ≤ z.re := by
    have h1 := Complex.abs_re_le_norm (z - (D.x₀ : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    have h2 : D.x₀ / (4 * a₀ D.k) ≤ D.x₀ := div_le_self hx.le (by linarith)
    have := neg_abs_le (z.re - D.x₀)
    linarith
  have hure : 0 ≤ (z⁻¹).re := by
    rw [Complex.inv_re]; exact div_nonneg hzre (Complex.normSq_nonneg _)
  have hη1 : D.η ≤ 1 := by
    have := D.hη; have := D.η_nonneg; have := D.k_ge
    nlinarith
  have hκ : ‖D.κ z⁻¹‖ ≤ 2 := by
    have h1 := D.hκb _ hmem
    have h2 : ‖D.κ z⁻¹‖ ≤ ‖D.κ (D.x₀ : ℂ)⁻¹‖ + ‖D.κ z⁻¹ - D.κ (D.x₀ : ℂ)⁻¹‖ := by
      calc ‖D.κ z⁻¹‖ = ‖D.κ (D.x₀ : ℂ)⁻¹ + (D.κ z⁻¹ - D.κ (D.x₀ : ℂ)⁻¹)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    linarith
  rw [Complex.add_re, Complex.re_ofReal_mul]
  have h1 := Complex.abs_re_le_norm (D.κ z⁻¹)
  have h2 := neg_abs_le (D.κ z⁻¹).re
  have h3 : 0 ≤ D.L * (z⁻¹).re := mul_nonneg hL hure
  linarith

/-- **Inequality (6.8).** `|G(s_z)| ≤ (k+1) · 2.2 C_b m₀ · 3^k · 2e³δ`. -/
lemma ze_near_zero (F : ℂ → ℂ)
    (hF : ∀ u ∈ Metric.closedBall ((D.x₀ : ℂ)⁻¹) (D.x₀⁻¹ / 2),
      u⁻¹ ∈ Metric.closedBall (D.x₀ : ℂ) (D.x₀ / 2) →
      F u⁻¹ = u⁻¹ * ((1 - u) / 2 + Complex.exp (D.L * u + D.κ u) / Complex.exp 1))
    (hκ0 : ‖D.κ (D.x₀ : ℂ)⁻¹‖ ≤ 1)
    {M δ : ℝ} (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M)
    (hδ0 : 0 ≤ δ) (hδ1 : 2 * Real.exp 3 * δ ≤ 1)
    {z w : ℂ} (hz : ‖z - (D.x₀ : ℂ)‖ ≤ D.x₀ / (4 * a₀ D.k))
    (hw : ∑ b : Fin (D.k + 1), (D.A b).eval z * w ^ (b : ℕ) = 0) (hFw : ‖F z - w‖ ≤ δ) :
    ‖D.G (D.sz z)‖ ≤
      ((D.k : ℝ) + 1) * (2.2 * (D.ze_Bb * M)) * (3 ^ D.k * (2 * Real.exp 3 * δ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hz0 := D.z_ne_zero hz
  have hx := D.x₀_pos
  have ha := D.a_ge
  have hu : z⁻¹ ≠ 0 := inv_ne_zero hz0
  have hmem : z⁻¹ ∈ Metric.closedBall ((D.x₀ : ℂ)⁻¹) (D.x₀⁻¹ / 2) := by
    rw [mem_closedBall, dist_eq_norm]
    have h1 := D.inv_sub_le hz
    have h2 : D.ρ / 3 ≤ D.x₀⁻¹ / 2 := by
      unfold ρ
      have : 0 < D.x₀⁻¹ := inv_pos.2 hx
      rw [div_div, div_le_div_iff_of_pos_left this (by positivity) (by norm_num)]
      linarith
    exact h1.trans h2
  have hmem2 : z⁻¹⁻¹ ∈ Metric.closedBall (D.x₀ : ℂ) (D.x₀ / 2) := by
    rw [inv_inv, mem_closedBall, dist_eq_norm]
    have : D.x₀ / (4 * a₀ D.k) ≤ D.x₀ / 2 :=
      div_le_div_of_nonneg_left hx.le (by norm_num) (by linarith)
    linarith
  have hFz := hF z⁻¹ hmem hmem2
  rw [inv_inv] at hFz
  -- the two exponentials
  set E : ℂ := cexp ((D.L : ℂ) * z⁻¹ + D.κ z⁻¹) with hE
  set E' : ℂ := cexp 1 * (z⁻¹ * w - (1 - z⁻¹) / 2) with hE'
  have he1 : cexp 1 ≠ 0 := Complex.exp_ne_zero _
  have key2 := cv_identity D.A D.hAd hu (E := E') (Fu := w) (by
    rw [hE']; field_simp; ring)
  rw [inv_inv, hw, mul_zero] at key2
  have hG : D.G (D.sz z) = ∑ j : Fin (D.k + 1), (cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) := by
    rw [D.G_eq, D.u_sz]
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  set r : ℂ := E' / E with hr
  have hE'r : E' = E * r := by rw [hr]; field_simp
  have hG2 : D.G (D.sz z) =
      ∑ j : Fin (D.k + 1), (cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) * (1 - r ^ (j : ℕ)) := by
    have : ∑ j : Fin (D.k + 1), (cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) * (1 - r ^ (j : ℕ)) =
        ∑ j : Fin (D.k + 1), (cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) -
          ∑ j : Fin (D.k + 1), (cvP D.k D.d D.A j).eval z⁻¹ * E' ^ (j : ℕ) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hE'r, mul_pow]; ring
    rw [this, ← key2, sub_zero, hG]
  -- `|r - 1| ≤ 2 e³ δ`
  have hEeq : E = cexp 1 * (z⁻¹ * F z - (1 - z⁻¹) / 2) := by
    rw [hFz]; field_simp; ring
  have hdiff : E' - E = cexp 1 * z⁻¹ * (w - F z) := by
    rw [hEeq, hE']; ring
  have hun : ‖z⁻¹‖ ≤ 2 := by
    have := D.z_norm hz
    have := D.hx
    rw [norm_inv, inv_le_comm₀ (norm_pos_iff.2 hz0) (by norm_num)]
    linarith
  have hEn : Real.exp (-2) ≤ ‖E‖ := by
    rw [hE, Complex.norm_exp]
    exact Real.exp_le_exp.2 (D.ze_re_ge hz hκ0 hmem)
  have hrr : ‖r - 1‖ ≤ 2 * Real.exp 3 * δ := by
    have e : r - 1 = (E' - E) / E := by rw [hr]; field_simp
    have hEp : 0 < ‖E‖ := norm_pos_iff.2 hE0
    rw [e, norm_div, div_le_iff₀ hEp, hdiff, norm_mul, norm_mul, norm_sub_rev]
    have he : ‖cexp 1‖ = Real.exp 1 := by
      rw [Complex.norm_exp]; simp
    rw [he]
    have h3 : Real.exp 3 * Real.exp (-2) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    have h4 : Real.exp 1 * ‖z⁻¹‖ * ‖F z - w‖ ≤ Real.exp 1 * 2 * δ := by
      have := Real.exp_pos 1
      gcongr
    have h5 : 2 * Real.exp 3 * δ * Real.exp (-2) ≤ 2 * Real.exp 3 * δ * ‖E‖ := by
      have := Real.exp_pos 3
      gcongr
    have h6 : 2 * Real.exp 3 * δ * Real.exp (-2) = Real.exp 1 * 2 * δ := by
      rw [← h3]; ring
    linarith
  -- the sum
  rw [hG2]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ j : Fin (D.k + 1),
      ‖(cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) * (1 - r ^ (j : ℕ))‖ ≤
        2.2 * (D.ze_Bb * M) * (3 ^ D.k * (2 * Real.exp 3 * δ)) := by
    intro j
    rw [norm_mul]
    have h1 := D.ze_term_le hM j (s := D.sz z) (by linarith [D.sz_norm hz])
    rw [D.u_sz] at h1
    have h2 := ze_pow_sub_one_le hδ1 hrr j
    have hj : (j : ℕ) ≤ D.k := Nat.lt_succ_iff.1 j.isLt
    have h3 : ‖1 - r ^ (j : ℕ)‖ ≤ 3 ^ D.k * (2 * Real.exp 3 * δ) := by
      rw [norm_sub_rev]
      refine h2.trans ?_
      have : (3 : ℝ) ^ (j : ℕ) ≤ 3 ^ D.k := pow_le_pow_right₀ (by norm_num) hj
      have : 0 ≤ 2 * Real.exp 3 * δ := by positivity
      gcongr
    have hBM : 0 ≤ 2.2 * (D.ze_Bb * M) := by have := D.ze_Bb_nonneg; positivity
    exact mul_le_mul h1 h3 (norm_nonneg _) hBM
  calc ∑ j : Fin (D.k + 1), ‖(cvP D.k D.d D.A j).eval z⁻¹ * E ^ (j : ℕ) * (1 - r ^ (j : ℕ))‖
      ≤ ∑ _j : Fin (D.k + 1), 2.2 * (D.ze_Bb * M) * (3 ^ D.k * (2 * Real.exp 3 * δ)) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

/-- Jensen's formula applied to `G - e`, where `|e| ≤ m₀/4` on `|s| ≤ 4`. -/
lemma ze_card_le {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) {M : ℝ}
    (hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M)
    (hMc : ‖expPoly D.k D.T D.R c‖ = M) (e : ℂ → ℂ) (he : Differentiable ℂ e)
    (heb : ∀ s : ℂ, ‖s‖ ≤ 4 → ‖e s‖ ≤ M / 4)
    (W : Finset ℂ) (hW : ∀ w ∈ W, ‖w‖ ≤ 1 / 3 ∧ D.G w - e w = 0) :
    (W.card : ℝ) ≤ 17 * (4 * D.k + 3) * D.T := by
  have hMpos := D.M_pos hM
  have hsub : ∀ s : ℂ, ‖s‖ ≤ 4 → ‖D.G s - expPoly D.k D.T D.R s‖ ≤ M / 2 :=
    fun s hs => D.G_sub_le hM hs
  have L4a := (expPoly_bound D.T_pos D.n D.R D.R_degree hM).1
  set N := ∑ j, D.n j with hN
  set Ba : ℝ := (N : ℝ) * 3 ^ N * Real.exp (5 * max (2 * D.k * D.T) (2 * (N : ℝ))) with hBa
  have hBa0 : 0 ≤ Ba := by rw [hBa]; positivity
  have hHa : AnalyticOnNhd ℂ (fun s => D.G s - e s) (closedBall c 3) :=
    fun z hz => (D.G_analytic hc z hz).sub (he.analyticAt z)
  have hHc : M / 4 ≤ ‖D.G c - e c‖ := by
    have h1 := hsub c (by linarith)
    have h2 := heb c (by linarith)
    have h3 : ‖expPoly D.k D.T D.R c‖ ≤
        ‖D.G c - e c‖ + ‖D.G c - expPoly D.k D.T D.R c‖ + ‖e c‖ := by
      calc ‖expPoly D.k D.T D.R c‖ =
            ‖(D.G c - e c) - (D.G c - expPoly D.k D.T D.R c) + e c‖ := by ring_nf
        _ ≤ ‖(D.G c - e c) - (D.G c - expPoly D.k D.T D.R c)‖ + ‖e c‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_sub_le _ _
    linarith
  have hHc0 : D.G c - e c ≠ 0 := by
    intro h; rw [h, norm_zero] at hHc; linarith
  have hsph : ∀ z ∈ sphere c 3, ‖D.G z - e z‖ ≤ (Ba + 3 / 4) * M := by
    intro z hz
    have hz' : ‖z‖ ≤ 4 := by
      rw [mem_sphere, dist_eq_norm] at hz
      calc ‖z‖ = ‖(z - c) + c‖ := by ring_nf
        _ ≤ ‖z - c‖ + ‖c‖ := norm_add_le _ _
        _ ≤ 4 := by linarith
    have h1 := hsub z hz'
    have h2 := L4a z (by linarith)
    have h4 := heb z hz'
    have h3 : ‖D.G z - e z‖ ≤
        ‖expPoly D.k D.T D.R z‖ + ‖D.G z - expPoly D.k D.T D.R z‖ + ‖e z‖ := by
      calc ‖D.G z - e z‖ =
            ‖expPoly D.k D.T D.R z + (D.G z - expPoly D.k D.T D.R z) - e z‖ := by ring_nf
        _ ≤ ‖expPoly D.k D.T D.R z + (D.G z - expPoly D.k D.T D.R z)‖ + ‖e z‖ :=
            norm_sub_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    have e : (Ba + 3 / 4) * M = Ba * M + M / 2 + M / 4 := by ring
    rw [e]
    linarith
  have hJ := card_zeros_le_of_jensen hHa hHc0 hsph W (fun w hw => by
    refine ⟨?_, (hW w hw).2⟩
    rw [mem_closedBall, dist_eq_norm]
    have := (hW w hw).1
    calc ‖w - c‖ ≤ ‖w‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ 3 / 2 := by linarith)
  have hHcpos : 0 < ‖D.G c - e c‖ := norm_pos_iff.2 hHc0
  have hlog : Real.log ((Ba + 3 / 4) * M / ‖D.G c - e c‖) ≤ Real.log (4 * Ba + 3) := by
    apply Real.log_le_log (div_pos (mul_pos (by linarith) hMpos) hHcpos)
    calc (Ba + 3 / 4) * M / ‖D.G c - e c‖ ≤ (Ba + 3 / 4) * M / (M / 4) :=
          div_le_div_of_nonneg_left (mul_nonneg (by linarith) hMpos.le) (by linarith) hHc
      _ = 4 * Ba + 3 := by field_simp
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnum := ze_num_jensen D.hk D.T_ge D.N_ge D.N_le
  calc (W.card : ℝ) ≤ Real.log ((Ba + 3 / 4) * M / ‖D.G c - e c‖) / Real.log 2 := hJ
    _ ≤ Real.log (4 * Ba + 3) / Real.log 2 := div_le_div_of_nonneg_right hlog hl2.le
    _ ≤ 17 * (4 * D.k + 3) * D.T := hnum

/-- Proposition 6.1 for the data `D`. -/
theorem ze_main (F : ℂ → ℂ)
    (hF : ∀ u ∈ Metric.closedBall ((D.x₀ : ℂ)⁻¹) (D.x₀⁻¹ / 2),
      u⁻¹ ∈ Metric.closedBall (D.x₀ : ℂ) (D.x₀ / 2) →
      F u⁻¹ = u⁻¹ * ((1 - u) / 2 + Complex.exp (D.L * u + D.κ u) / Complex.exp 1))
    (hκ0 : ‖D.κ (D.x₀ : ℂ)⁻¹‖ ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ₅ D.k D.x₀ D.T)
    (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, ‖z - D.x₀‖ ≤ D.x₀ / (4 * a₀ D.k) ∧
      ∃ w : ℂ, ∑ b : Fin (D.k + 1), (D.A b).eval z * w ^ (b : ℕ) = 0 ∧ ‖F z - w‖ ≤ δ)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 1 ≤ ‖z - z'‖) :
    (Z.card : ℝ) ≤ 17 * (4 * D.k + 3) * D.T := by
  classical
  refine le_of_not_gt fun hcon => ?_
  have hY0 : 0 ≤ 17 * (4 * (D.k : ℝ) + 3) * D.T := by have := D.T_pos; positivity
  set N₁ := ⌊17 * (4 * (D.k : ℝ) + 3) * D.T⌋₊ + 1 with hN₁
  have hN₁Z : N₁ ≤ Z.card := (Nat.floor_lt hY0).2 hcon
  have hN₁le : (N₁ : ℝ) ≤ 17 * (4 * D.k + 3) * D.T + 1 := by
    rw [hN₁]; push_cast; linarith [Nat.floor_le hY0]
  have hN₁gt : 17 * (4 * (D.k : ℝ) + 3) * D.T < N₁ := by
    rw [hN₁]; push_cast; exact Nat.lt_floor_add_one _
  obtain ⟨Z', hZ'Z, hZ'c⟩ := Finset.exists_subset_card_eq hN₁Z
  -- the maximum `m₀` of `|G₀|` on `|s| ≤ 1/2`
  have hcont : ContinuousOn (fun s => ‖expPoly D.k D.T D.R s‖) (closedBall (0 : ℂ) (1 / 2)) :=
    (ep_differentiable D.k D.T D.R).continuous.norm.continuousOn
  obtain ⟨c, hc, hmax⟩ := (isCompact_closedBall (0 : ℂ) (1 / 2)).exists_isMaxOn
    ⟨0, mem_closedBall_self (by norm_num)⟩ hcont
  set M := ‖expPoly D.k D.T D.R c‖ with hMdef
  have hM : ∀ s : ℂ, ‖s‖ ≤ 1 / 2 → ‖expPoly D.k D.T D.R s‖ ≤ M :=
    fun s hs => isMaxOn_iff.1 hmax s (mem_closedBall_zero_iff.2 hs)
  have hM0 : 0 ≤ M := norm_nonneg _
  have hδ1 : 2 * Real.exp 3 * δ ≤ 1 := ze_delta_small D.hx D.T_pos.le hδ
  -- the nodes
  set W := Z'.image D.sz with hWdef
  have hWc : W.card = N₁ := by
    rw [hWdef, Finset.card_image_of_injOn (fun z _ w _ h => D.sz_inj h), hZ'c]
  have hWb : ∀ v ∈ W, ‖v‖ ≤ 1 / 3 := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    exact D.sz_norm (hZ z (hZ'Z hz)).1
  have hWsep : ∀ v ∈ W, ∀ v' ∈ W, v ≠ v' → 5 / D.x₀ ≤ ‖v - v'‖ := by
    intro v hv v' hv' hne
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hv'
    have hzz : z ≠ z' := fun h => hne (by rw [h])
    exact D.ze_sz_sep (hZ z (hZ'Z hz)).1 (hZ z' (hZ'Z hz')).1 (hsep z (hZ'Z hz) z' (hZ'Z hz') hzz)
  set B := ((D.k : ℝ) + 1) * (2.2 * (D.ze_Bb * M)) * (3 ^ D.k * (2 * Real.exp 3 * δ)) with hB
  have hWG : ∀ v ∈ W, ‖D.G v‖ ≤ B := by
    intro v hv
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hz1, w, hw, hFw⟩ := hZ z (hZ'Z hz)
    exact D.ze_near_zero F hF hκ0 hM hδ0 hδ1 hz1 hw hFw
  -- the Lagrange correction
  have heb : ∀ s : ℂ, ‖s‖ ≤ 4 → ‖ze_lag W D.G s‖ ≤ M / 4 := by
    intro s hs
    refine (ze_lag_bound W D.G D.hx hWb hWsep hWG hs).trans ?_
    rw [hWc]
    have hnum := ze_num_lagrange D.hk D.T_ge hN₁le D.hx hδ0 hδ D.ze_Bb_nonneg D.ze_Bb_le
    have e : (N₁ : ℝ) * B * D.x₀ ^ N₁ = M * ((N₁ : ℝ) * (((D.k : ℝ) + 1) * (2.2 * D.ze_Bb) *
        (3 ^ D.k * (2 * Real.exp 3 * δ))) * D.x₀ ^ N₁) := by rw [hB]; ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hnum hM0
    linarith
  have hcard := D.ze_card_le (mem_closedBall_zero_iff.1 hc) hM rfl (ze_lag W D.G)
    (ze_lag_diff W D.G) heb W (fun v hv => ⟨hWb v hv, by rw [ze_lag_eval W D.G hv, sub_self]⟩)
  rw [hWc] at hcard
  linarith

end ZeroData

/-- **Proposition 6.1.** -/
theorem zero_estimate (k d : ℕ) (L x₀ η δ : ℝ) (F κ : ℂ → ℂ) (hk : 1 ≤ k) (hx : 1 ≤ x₀)
    (hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ L / (a₀ k * x₀)) (hd : (d : ℝ) ≤ 2 * (L / (a₀ k * x₀)))
    (hη : k * η ≤ 0.09)
    (hκd : DifferentiableOn ℂ κ (Metric.closedBall ((x₀ : ℂ)⁻¹) (x₀⁻¹ / 2)))
    (hκb : ∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) (x₀⁻¹ / 2), ‖κ u - κ (x₀ : ℂ)⁻¹‖ ≤ η)
    (hκ0 : ‖κ (x₀ : ℂ)⁻¹‖ ≤ 1)
    (hF : ∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) (x₀⁻¹ / 2),
      u⁻¹ ∈ Metric.closedBall (x₀ : ℂ) (x₀ / 2) →
      F u⁻¹ = u⁻¹ * ((1 - u) / 2 + Complex.exp (L * u + κ u) / Complex.exp 1))
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ δ₅ k x₀ (L / (a₀ k * x₀)))
    (A : Fin (k + 1) → ℂ[X]) (hA : ∃ b, A b ≠ 0) (hAd : ∀ b, (A b).natDegree ≤ d)
    (Z : Finset ℂ)
    (hZ : ∀ z ∈ Z, ‖z - x₀‖ ≤ x₀ / (4 * a₀ k) ∧
      ∃ w : ℂ, ∑ b : Fin (k + 1), (A b).eval z * w ^ (b : ℕ) = 0 ∧ ‖F z - w‖ ≤ δ)
    (hsep : ∀ z ∈ Z, ∀ z' ∈ Z, z ≠ z' → 1 ≤ ‖z - z'‖) :
    (Z.card : ℝ) ≤ 17 * (4 * k + 3) * (L / (a₀ k * x₀)) :=
  ZeroData.ze_main ⟨k, d, L, x₀, η, κ, A, hk, hx, hT, hd, hη, hκd, hκb, hA, hAd⟩ F hF hκ0 hδ0 hδ
    Z hZ hsep

end Singmaster
