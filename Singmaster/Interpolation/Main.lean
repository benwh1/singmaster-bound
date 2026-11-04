module

public import Singmaster.Basic
public import Singmaster.Bernoulli
public import Singmaster.Interpolation.Contraction
public import Singmaster.Stirling.Main

@[expose] public section

/-!
# Proposition 3.1: the interpolating function

`F(z) = (z-1)/2 + exp(g(z) + v(z))`, where `g(z) = (L + lg z)/z` and `lg` is the function of
Lemma 2.1. Here `v` is the holomorphic fixed point of
`v = (1/z) ∑_{j=1}^{N₀} P_{2j}(z) e^{-2j(g + v)}/(2j)` with `N₀ = ⌊x₀/8⌋`.

The proof follows Section 3 of the paper.

1. The exact identity (3.1) at the integers (`interp_series`, `interp_sum_log_choose`): for
   `C(n, m) = t`, `2m ≤ n` and `c = n - (m-1)/2` we have `log c = g(m) + v*`, with
   `v* = ∑_k interp_f m c k ≥ 0`.
2. Truncating `v*` at `N₀` gives the fixed-point map at `v*`, so the stability of the fixed
   point bounds `|F(m) - n|` (`interp_tail`, `interp_sum_a_nat`, `interp_approx_core`).
3. Stirling estimates (`interp_D_bound`, `interp_reG_lower`, `interp_reG_upper`,
   `interp_D_mu`) on the open set `interp_U x = {x/3 < Re z, |z| < 5x/2}`.
4. The contraction hypothesis (`interp_hbound`, `interp_num_q`) with `q = e^{-ℓ/20}`.
5. Numerical inequalities (`interp_num_*`) and the geometry of the two discs
   (`interp_ball_geom`, `interp_inv_ball_geom`), and finally `interpolatingFunction`.
-/

open Real Polynomial

namespace Singmaster

/-- **Proposition 3.1.** Let `L = log t`, `ℓ = L/x₀` and `u₀ = 1/x₀`. For `x₀` large and
`ℓ ≥ 100 log x₀` there are functions `F`, holomorphic on `|z - x₀| ≤ x₀/2`, and `κ`, holomorphic
on `|u - u₀| ≤ u₀/2`, such that
(a) `|F(m) - n| ≤ e^{-L/8}` for every `(n, m) ∈ Sol(t)` with `|m - x₀| ≤ x₀/2`;
(b) `|F| ≤ 3 x₀ e^{2ℓ}`;
(c) `F(1/u) = u⁻¹ ((1 - u)/2 + e^{L u + κ(u)}/e)` whenever `1/u` lies in the disc of `F`;
(d) `|κ(u) - κ(u₀)| ≤ η₀` and `|κ(u₀)| ≤ 1`.
The proof takes `x₀ ≥ max(1000, e^{30})`. -/
def InterpolatingFunction : Prop :=
  ∃ X : ℝ, ∀ t x₀ : ℕ, X ≤ x₀ → 100 * log x₀ ≤ log t / x₀ →
    ∃ F κ : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.closedBall (x₀ : ℂ) (x₀ / 2)) ∧
      (∀ n m : ℕ, n.choose m = t → 2 * m ≤ n → |(m : ℝ) - x₀| ≤ x₀ / 2 →
        ‖F m - n‖ ≤ exp (-(log t) / 8)) ∧
      DifferentiableOn ℂ κ (Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2)) ∧
      (∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2),
        ‖κ u - κ (x₀ : ℂ)⁻¹‖ ≤ η₀ x₀ (log t / x₀)) ∧
      ‖κ (x₀ : ℂ)⁻¹‖ ≤ 1 ∧
      (∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2),
        u⁻¹ ∈ Metric.closedBall (x₀ : ℂ) (x₀ / 2) →
        F u⁻¹ = u⁻¹ * ((1 - u) / 2 + Complex.exp (log t * u + κ u) / Complex.exp 1)) ∧
      (∀ z ∈ Metric.closedBall (x₀ : ℂ) (x₀ / 2), ‖F z‖ ≤ 3 * x₀ * exp (2 * (log t / x₀)))

/-- Proposition 3.1 at a fixed `t`. -/
def InterpolatingFunctionAt (t : ℕ) (X : ℝ) : Prop :=
  ∀ x₀ : ℕ, X ≤ x₀ → 100 * log x₀ ≤ log t / x₀ →
    ∃ F κ : ℂ → ℂ,
      DifferentiableOn ℂ F (Metric.closedBall (x₀ : ℂ) (x₀ / 2)) ∧
      (∀ n m : ℕ, n.choose m = t → 2 * m ≤ n → |(m : ℝ) - x₀| ≤ x₀ / 2 →
        ‖F m - n‖ ≤ exp (-(log t) / 8)) ∧
      DifferentiableOn ℂ κ (Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2)) ∧
      (∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2),
        ‖κ u - κ (x₀ : ℂ)⁻¹‖ ≤ η₀ x₀ (log t / x₀)) ∧
      ‖κ (x₀ : ℂ)⁻¹‖ ≤ 1 ∧
      (∀ u ∈ Metric.closedBall ((x₀ : ℂ)⁻¹) ((x₀ : ℝ)⁻¹ / 2),
        u⁻¹ ∈ Metric.closedBall (x₀ : ℂ) (x₀ / 2) →
        F u⁻¹ = u⁻¹ * ((1 - u) / 2 + Complex.exp (log t * u + κ u) / Complex.exp 1)) ∧
      (∀ z ∈ Metric.closedBall (x₀ : ℂ) (x₀ / 2), ‖F z‖ ≤ 3 * x₀ * exp (2 * (log t / x₀)))

theorem interpolatingFunction_iff :
    InterpolatingFunction ↔ ∃ X, ∀ t, InterpolatingFunctionAt t X := Iff.rfl

open Finset in
/-- Reflection `i ↦ m - 1 - i` negates the centred offsets `i - (m-1)/2`. -/
lemma interp_reflect (m : ℕ) (g : ℝ → ℝ) :
    ∑ i ∈ range m, g ((i : ℝ) - ((m : ℝ) - 1) / 2) =
      ∑ i ∈ range m, g (-((i : ℝ) - ((m : ℝ) - 1) / 2)) := by
  rw [← Finset.sum_range_reflect (fun i : ℕ => g ((i : ℝ) - ((m : ℝ) - 1) / 2)) m]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  congr 1
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

lemma interp_offset_abs {m i : ℕ} (hi : i < m) :
    |(i : ℝ) - ((m : ℝ) - 1) / 2| ≤ ((m : ℝ) - 1) / 2 := by
  have : (i : ℝ) + 1 ≤ m := by exact_mod_cast hi
  have h0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  rw [abs_le]; constructor <;> linarith

lemma interp_log_pair {c y : ℝ} (hc : |y| < c) :
    Real.log (c - y) + Real.log (c + y) = 2 * Real.log c + Real.log (1 - (y / c) ^ 2) := by
  have hc0 : 0 < c := lt_of_le_of_lt (abs_nonneg y) hc
  have h1 : 0 < c - y := by linarith [le_abs_self y]
  have h2 : 0 < c + y := by linarith [neg_abs_le y]
  have h3 : 0 < 1 - (y / c) ^ 2 := by
    have : (y / c) ^ 2 < 1 := by
      rw [div_pow, div_lt_one (by positivity)]
      have := sq_lt_sq' (by linarith [neg_abs_le y]) (lt_of_le_of_lt (le_abs_self y) hc)
      exact this
    linarith
  rw [show 2 * Real.log c = Real.log (c ^ 2) by rw [Real.log_pow]; push_cast; ring,
    ← Real.log_mul (by positivity) h3.ne', ← Real.log_mul h1.ne' h2.ne']
  congr 1
  field_simp
  ring

open Finset in
/-- `2 ∑ log(c - x_i) = 2 m log c + ∑ log(1 - (x_i/c)^2)`. -/
lemma interp_two_sum_log {m : ℕ} {c : ℝ} (hc : ((m : ℝ) - 1) / 2 < c) :
    2 * ∑ i ∈ range m, Real.log (c - ((i : ℝ) - ((m : ℝ) - 1) / 2)) =
      2 * m * Real.log c +
        ∑ i ∈ range m, Real.log (1 - (((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) := by
  have hrefl := interp_reflect m (fun y => Real.log (c - y))
  simp only [sub_neg_eq_add] at hrefl
  rw [two_mul]
  nth_rewrite 2 [hrefl]
  rw [← Finset.sum_add_distrib]
  have : ∀ i ∈ range m, Real.log (c - ((i : ℝ) - ((m : ℝ) - 1) / 2)) +
      Real.log (c + ((i : ℝ) - ((m : ℝ) - 1) / 2)) =
      2 * Real.log c + Real.log (1 - (((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) := by
    intro i hi
    exact interp_log_pair (lt_of_le_of_lt (interp_offset_abs (mem_range.mp hi)) hc)
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  ring

/-- The `k`-th term (`j = k+1`) of the series `v* = (1/m) ∑_j P_{2j}(m) / (2j c^{2j})`. -/
noncomputable def interp_f (m : ℕ) (c : ℝ) (k : ℕ) : ℝ :=
  (∑ i ∈ Finset.range m, ((((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) ^ (k + 1) / (k + 1)) / (2 * m)

open Finset in
lemma interp_series {m : ℕ} (hm : 0 < m) {c : ℝ} (hc : ((m : ℝ) - 1) / 2 < c) :
    HasSum (interp_f m c)
      (Real.log c - (∑ i ∈ range m, Real.log (c - ((i : ℝ) - ((m : ℝ) - 1) / 2))) / m) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 : 0 < c := by linarith
  have hterm : ∀ i ∈ range m, HasSum
      (fun k : ℕ => ((((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) ^ (k + 1) / (k + 1))
      (-Real.log (1 - (((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2)) := by
    intro i hi
    apply Real.hasSum_pow_div_log_of_abs_lt_one
    have hab := lt_of_le_of_lt (interp_offset_abs (mem_range.mp hi)) hc
    rw [abs_of_nonneg (sq_nonneg _), div_pow, div_lt_one (by positivity)]
    exact sq_lt_sq' (by linarith [neg_abs_le ((i : ℝ) - ((m : ℝ) - 1) / 2)])
      (lt_of_le_of_lt (le_abs_self _) hab)
  have := (hasSum_sum hterm).div_const (2 * m)
  convert this using 1
  · funext k; rfl
  have h2 := interp_two_sum_log hc
  rw [Finset.sum_neg_distrib, eq_div_iff (by positivity)]
  set S := ∑ i ∈ range m, Real.log (c - ((i : ℝ) - ((m : ℝ) - 1) / 2))
  set T := ∑ i ∈ range m, Real.log (1 - (((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2)
  have : (Real.log c - S / m) * (2 * m) = 2 * m * Real.log c - 2 * S := by
    field_simp
  linarith

open Finset in
lemma interp_f_bounds {m : ℕ} (hm : 0 < m) {c : ℝ} (hc0 : 0 < c) (k : ℕ) :
    0 ≤ interp_f m c k ∧ interp_f m c k ≤ ((m / (2 * c)) ^ 2) ^ (k + 1) / 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hk : (1 : ℝ) ≤ k + 1 := by have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k); linarith
  have hle : ∀ i ∈ range m, ((((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) ^ (k + 1) / (k + 1) ≤
      ((m / (2 * c)) ^ 2) ^ (k + 1) := by
    intro i hi
    have hab := interp_offset_abs (mem_range.mp hi)
    have h1 : |((i : ℝ) - ((m : ℝ) - 1) / 2) / c| ≤ m / (2 * c) := by
      rw [abs_div, abs_of_pos hc0, div_le_div_iff₀ hc0 (by positivity)]
      nlinarith
    have h2 : (((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2 ≤ (m / (2 * c)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc _ ≤ ((((i : ℝ) - ((m : ℝ) - 1) / 2) / c) ^ 2) ^ (k + 1) :=
          div_le_self (by positivity) hk
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) h2 _
  unfold interp_f
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ ∑ i ∈ range m, ((m / (2 * c)) ^ 2) ^ (k + 1) := Finset.sum_le_sum hle
    _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp

lemma interp_tail {f : ℕ → ℝ} {v ρ : ℝ} (hf : HasSum f v) (h0 : ∀ k, 0 ≤ f k)
    (h1 : ∀ k, f k ≤ ρ ^ (k + 1) / 2) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 1 / 2) (N : ℕ) :
    0 ≤ v - ∑ k ∈ Finset.range N, f k ∧ v - ∑ k ∈ Finset.range N, f k ≤ ρ ^ (N + 1) := by
  have hN := (hasSum_nat_add_iff' N).mpr hf
  refine ⟨hN.nonneg (fun k => h0 _), ?_⟩
  have hg : HasSum (fun k : ℕ => ρ ^ (N + 1) / 2 * ρ ^ k) (ρ ^ (N + 1) / 2 * (1 - ρ)⁻¹) :=
    (hasSum_geometric_of_lt_one hρ0 (by linarith)).mul_left _
  have hle := hasSum_le (fun k => ?_) hN hg
  · have hinv : (1 - ρ)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have hp : 0 ≤ ρ ^ (N + 1) := pow_nonneg hρ0 _
    nlinarith
  · calc f (k + N) ≤ ρ ^ (k + N + 1) / 2 := h1 _
      _ = _ := by ring

open Finset in
/-- `∑_{i<m} log(n - i) = log (n.choose m) + log m!`. -/
lemma interp_sum_log_choose {n m : ℕ} (hmn : m ≤ n) :
    ∑ i ∈ range m, Real.log (((n : ℝ) - ((m : ℝ) - 1) / 2) - ((i : ℝ) - ((m : ℝ) - 1) / 2)) =
      Real.log (n.choose m) + Real.log m.factorial := by
  have h1 : ∀ i ∈ range m,
      Real.log (((n : ℝ) - ((m : ℝ) - 1) / 2) - ((i : ℝ) - ((m : ℝ) - 1) / 2)) =
        Real.log (((n - i : ℕ) : ℝ)) := by
    intro i hi; have := mem_range.mp hi; rw [Nat.cast_sub (by omega)]; congr 1; ring
  have h2 : ∀ i ∈ range m, (((n - i : ℕ) : ℝ)) ≠ 0 := by
    intro i hi; have := mem_range.mp hi
    exact Nat.cast_ne_zero.mpr (by omega)
  rw [Finset.sum_congr rfl h1, ← Real.log_prod h2, ← Nat.cast_prod,
    ← Nat.descFactorial_eq_prod_range, Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      (Nat.cast_ne_zero.mpr (Nat.choose_pos hmn).ne'), add_comm]

open Finset in
lemma interp_f_eq (m : ℕ) {c : ℝ} (hc0 : 0 < c) (k : ℕ) :
    interp_f m c k = (∑ i ∈ range m, ((i : ℝ) - ((m : ℝ) - 1) / 2) ^ (2 * (k + 1))) *
      Real.exp (-(2 * ((k : ℝ) + 1)) * Real.log c) / (2 * ((k : ℝ) + 1)) / m := by
  have hE : Real.exp (-(2 * ((k : ℝ) + 1)) * Real.log c) = (c ^ (2 * (k + 1)))⁻¹ := by
    rw [neg_mul, Real.exp_neg,
      show (2 * ((k : ℝ) + 1)) = ((2 * (k + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.exp_nat_mul, Real.exp_log hc0]
  rw [hE]; unfold interp_f
  rw [Finset.sum_mul, Finset.sum_div, Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← pow_mul, div_pow]
  field_simp

/-- The function `g(z) = (L + lg z)/z` of Section 3. -/
noncomputable def interp_G (lg : ℂ → ℂ) (L : ℝ) (z : ℂ) : ℂ := ((L : ℂ) + lg z) / z

/-- The coefficients `a_j(z) = P_{2j}(z) e^{-2j g(z)} / (2j z)` of the fixed-point equation. -/
noncomputable def interp_a (lg : ℂ → ℂ) (L : ℝ) (j : ℕ) (z : ℂ) : ℂ :=
  (powSumPoly j).eval z * Complex.exp (-(2 * (j : ℂ)) * interp_G lg L z) / (2 * j) / z

lemma interp_G_nat {lg : ℂ → ℂ} (hlg : ∀ m : ℕ, lg m = Real.log m.factorial) (L : ℝ) (m : ℕ) :
    interp_G lg L m = (((L + Real.log m.factorial) / m : ℝ) : ℂ) := by
  unfold interp_G; rw [hlg]; push_cast; ring

lemma interp_a_nat {lg : ℂ → ℂ} (hlg : ∀ m : ℕ, lg m = Real.log m.factorial) (L : ℝ) (m : ℕ)
    {c : ℝ} (hc0 : 0 < c) (k : ℕ) :
    interp_a lg L (k + 1) m * Complex.exp (-(2 * ((k + 1 : ℕ) : ℂ)) *
      ((Real.log c - (L + Real.log m.factorial) / m : ℝ) : ℂ)) = (interp_f m c k : ℂ) := by
  unfold interp_a
  rw [interp_G_nat hlg, powSumPoly_eval_nat, interp_f_eq m hc0 k]
  have hE : Complex.exp (-(2 * ((k + 1 : ℕ) : ℂ)) * (((L + Real.log m.factorial) / m : ℝ) : ℂ)) *
      Complex.exp (-(2 * ((k + 1 : ℕ) : ℂ)) *
        ((Real.log c - (L + Real.log m.factorial) / m : ℝ) : ℂ)) =
      ((Real.exp (-(2 * ((k : ℝ) + 1)) * Real.log c) : ℝ) : ℂ) := by
    rw [← Complex.exp_add, Complex.ofReal_exp]; congr 1; push_cast; ring
  calc _ = (∑ i ∈ Finset.range m, ((i : ℂ) - ((m : ℂ) - 1) / 2) ^ (2 * (k + 1))) *
        (Complex.exp (-(2 * ((k + 1 : ℕ) : ℂ)) * (((L + Real.log m.factorial) / m : ℝ) : ℂ)) *
        Complex.exp (-(2 * ((k + 1 : ℕ) : ℂ)) *
          ((Real.log c - (L + Real.log m.factorial) / m : ℝ) : ℂ))) /
        (2 * ((k + 1 : ℕ) : ℂ)) / m := by ring
    _ = _ := by rw [hE]; push_cast; ring

lemma interp_sum_a_nat {lg : ℂ → ℂ} (hlg : ∀ m : ℕ, lg m = Real.log m.factorial) (L : ℝ) (m : ℕ)
    {c : ℝ} (hc0 : 0 < c) (N : ℕ) :
    ∑ j ∈ Finset.Icc 1 N, interp_a lg L j m * Complex.exp (-(2 * (j : ℂ)) *
      ((Real.log c - (L + Real.log m.factorial) / m : ℝ) : ℂ)) =
      ((∑ k ∈ Finset.range N, interp_f m c k : ℝ) : ℂ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ, interp_a_nat hlg L m hc0 N]
    push_cast; ring

lemma interp_final_pow {m c G : ℝ} (hm : 0 < m) (hmc : m ≤ c) (hG : G ≤ Real.log c) (N : ℕ) :
    4 * c * ((m / (2 * c)) ^ 2) ^ (N + 1) ≤ m ^ (2 * N + 2) * Real.exp (-(2 * N + 1) * G) := by
  have hc : 0 < c := lt_of_lt_of_le hm hmc
  have h1 : ((m / (2 * c)) ^ 2) ^ (N + 1) = ((m / c) ^ 2) ^ (N + 1) * (1 / 4) ^ (N + 1) := by
    rw [← mul_pow]; congr 1; field_simp; ring
  have h4 : (1 / 4 : ℝ) ^ (N + 1) ≤ 1 / 4 := by
    calc (1 / 4 : ℝ) ^ (N + 1) ≤ (1 / 4) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 / 4 := by norm_num
  have h2 : c * ((m / c) ^ 2) ^ (N + 1) = m ^ (2 * N + 2) * (c ^ (2 * N + 1))⁻¹ := by
    rw [← pow_mul, div_pow, show 2 * (N + 1) = 2 * N + 2 by ring, pow_succ c (2 * N + 1)]
    field_simp
  have h3 : (c ^ (2 * N + 1))⁻¹ ≤ Real.exp (-(2 * N + 1) * G) := by
    have : (c ^ (2 * N + 1))⁻¹ = Real.exp (-(2 * N + 1) * Real.log c) := by
      rw [neg_mul, Real.exp_neg, show (2 * (N : ℝ) + 1) = ((2 * N + 1 : ℕ) : ℝ) by push_cast; ring,
        Real.exp_nat_mul, Real.exp_log hc]
    rw [this]
    apply Real.exp_le_exp.mpr
    have : (0 : ℝ) ≤ 2 * N + 1 := by positivity
    nlinarith
  have hp : 0 ≤ ((m / c) ^ 2) ^ (N + 1) := by positivity
  have hp' : 0 ≤ m ^ (2 * N + 2) := by positivity
  calc 4 * c * ((m / (2 * c)) ^ 2) ^ (N + 1)
      = 4 * (c * ((m / c) ^ 2) ^ (N + 1)) * (1 / 4) ^ (N + 1) := by rw [h1]; ring
    _ ≤ 4 * (c * ((m / c) ^ 2) ^ (N + 1)) * (1 / 4) := by gcongr
    _ = m ^ (2 * N + 2) * (c ^ (2 * N + 1))⁻¹ := by rw [h2]; ring
    _ ≤ _ := by gcongr

/-- Part (a) of Proposition 3.1 at one integer point, before the numerical estimates. -/
lemma interp_approx_core {lg : ℂ → ℂ} (hlg : ∀ m : ℕ, lg m = Real.log m.factorial) (L : ℝ) (N : ℕ)
    (v : ℂ → ℂ) {n m : ℕ} (hL : L = Real.log (n.choose m)) (h2m : 2 * m ≤ n) (hm : 0 < m)
    (hvq : ‖v m‖ ≤ 1 / 4)
    (hstab : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖w - v m‖ ≤
      2 * ‖w - ∑ j ∈ Finset.Icc 1 N, interp_a lg L j m * Complex.exp (-(2 * (j : ℂ)) * w)‖) :
    ‖((m : ℂ) - 1) / 2 + Complex.exp (interp_G lg L m + v m) - n‖ ≤
      (m : ℝ) ^ (2 * N + 2) * Real.exp (-(2 * N + 1) * (L / m)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : (2 * m : ℝ) ≤ n := by exact_mod_cast h2m
  set c : ℝ := (n : ℝ) - ((m : ℝ) - 1) / 2 with hc_def
  have hcm : (m : ℝ) ≤ c := by linarith
  have hc0 : 0 < c := by linarith
  have hc1 : ((m : ℝ) - 1) / 2 < c := by linarith
  have hS := interp_sum_log_choose (n := n) (m := m) (by omega)
  rw [← hL] at hS
  have hser := interp_series hm hc1
  rw [hS] at hser
  set vs : ℝ := Real.log c - (L + Real.log m.factorial) / m with hvs
  set ρ : ℝ := ((m : ℝ) / (2 * c)) ^ 2 with hρ
  have hb := interp_f_bounds hm hc0
  have hρ0 : 0 ≤ ρ := sq_nonneg _
  have hρ1 : ρ ≤ 1 / 4 := by
    have h1 : (m : ℝ) / (2 * c) ≤ 1 / 2 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    have h2 : 0 ≤ (m : ℝ) / (2 * c) := by positivity
    rw [hρ]; nlinarith
  have htail := interp_tail hser (fun k => (hb k).1) (fun k => (hb k).2) hρ0 (by linarith) N
  have hv0 := interp_tail hser (fun k => (hb k).1) (fun k => (hb k).2) hρ0 (by linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, sub_zero, zero_add, pow_one] at hv0
  set τ : ℝ := vs - ∑ k ∈ Finset.range N, interp_f m c k with hτ
  have hsum := interp_sum_a_nat hlg L m hc0 N
  have hvs1 : ‖(vs : ℂ)‖ ≤ 1 / 4 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hv0.1]; linarith
  have hst := hstab (vs : ℂ) (by linarith)
  rw [hsum, ← Complex.ofReal_sub, ← hτ, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg htail.1] at hst
  -- the identity `F m - n = c (e^{v m - vs} - 1)`
  have hGm : interp_G lg L m = (((L + Real.log m.factorial) / m : ℝ) : ℂ) := interp_G_nat hlg L m
  have hcexp : Complex.exp ((((L + Real.log m.factorial) / m : ℝ) : ℂ) + (vs : ℂ)) = (c : ℂ) := by
    rw [← Complex.ofReal_add, ← Complex.ofReal_exp, hvs]
    congr 1
    rw [show (L + Real.log m.factorial) / m + (Real.log c - (L + Real.log m.factorial) / m) =
      Real.log c by ring, Real.exp_log hc0]
  have hid : ((m : ℂ) - 1) / 2 + Complex.exp (interp_G lg L m + v m) - n =
      (c : ℂ) * (Complex.exp (v m - vs) - 1) := by
    have hn : (n : ℂ) = (c : ℂ) + ((m : ℂ) - 1) / 2 := by rw [hc_def]; push_cast; ring
    rw [hGm, hn, ← hcexp, mul_sub, ← Complex.exp_add, mul_one,
      show (((L + Real.log m.factorial) / m : ℝ) : ℂ) + (vs : ℂ) + (v m - vs) =
        (((L + Real.log m.factorial) / m : ℝ) : ℂ) + v m by ring]
    ring
  have hdiff : ‖v m - (vs : ℂ)‖ ≤ 2 * τ := by rw [norm_sub_rev]; exact hst
  have hdiff1 : ‖v m - (vs : ℂ)‖ ≤ 1 := by
    calc _ ≤ ‖v m‖ + ‖(vs : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1 := by linarith
  have hG : L / m ≤ Real.log c := by
    have h1 : 0 ≤ Real.log m.factorial :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m))
    have h2 : L / m ≤ (L + Real.log m.factorial) / m := by
      apply div_le_div_of_nonneg_right _ hm0.le; linarith
    linarith [hv0.1]
  rw [hid, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0]
  calc c * ‖Complex.exp (v m - vs) - 1‖ ≤ c * (2 * ‖v m - (vs : ℂ)‖) := by
        gcongr; exact Complex.norm_exp_sub_one_le hdiff1
    _ ≤ c * (2 * (2 * τ)) := by gcongr
    _ ≤ 4 * c * ρ ^ (N + 1) := by nlinarith [htail.2]
    _ ≤ _ := interp_final_pow hm0 hcm hG N

lemma interp_log_norm_le {z : ℂ} (hz : 1 ≤ ‖z‖) : ‖Complex.log z‖ ≤ Real.log ‖z‖ + π := by
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖z‖ + |z.arg| := by
        rw [Complex.log_re, Complex.log_im, abs_of_nonneg (Real.log_nonneg hz)]
    _ ≤ _ := by linarith [Complex.abs_arg_le_pi z]

lemma interp_D_eq (lg : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0) :
    lg z / z - Complex.log z + 1 = (Complex.log z / 2 + Real.log (2 * π) / 2 +
      (lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2))) / z := by
  field_simp; ring

lemma interp_log_two_pi : 0 ≤ Real.log (2 * π) ∧ Real.log (2 * π) ≤ 5.3 := by
  have hpi := Real.pi_gt_three
  have hpi' := Real.pi_lt_d2
  constructor
  · exact Real.log_nonneg (by linarith)
  · have := Real.log_le_sub_one_of_pos (show 0 < 2 * π by positivity); linarith

/-- The Stirling remainder controls `D(z) = lg z / z - log z + 1`. -/
lemma interp_D_bound {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {z : ℂ} (h1 : 1 ≤ ‖z‖) (h8 : ‖z‖ ≤ 8 * z.re) :
    ‖lg z / z - Complex.log z + 1‖ ≤
      (1 + (Real.log ‖z‖ + π) / 2 + Real.log (2 * π) / 2) / ‖z‖ := by
  have hz : z ≠ 0 := by intro h; rw [h, norm_zero] at h1; linarith
  have hr : 0 < ‖z‖ := by linarith
  rw [interp_D_eq lg hz, norm_div]
  gcongr
  have hJ := hst z h1 h8
  have hJ1 : 1 / ‖z‖ ≤ 1 := by rw [div_le_one hr]; exact h1
  have hL := interp_log_norm_le h1
  have h2pi : ‖((Real.log (2 * π) : ℝ) : ℂ) / 2‖ = Real.log (2 * π) / 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg interp_log_two_pi.1]
    norm_num
  calc _ ≤ ‖Complex.log z / 2‖ + ‖((Real.log (2 * π) : ℝ) : ℂ) / 2‖ +
        ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ := norm_add₃_le
    _ ≤ (Real.log ‖z‖ + π) / 2 + Real.log (2 * π) / 2 + 1 := by
        rw [h2pi, norm_div]
        have : ‖(2 : ℂ)‖ = 2 := by norm_num
        rw [this]
        linarith
    _ = _ := by ring

lemma interp_re_div_sub (lg : ℂ → ℂ) (z : ℂ) :
    |(lg z / z).re - (Real.log ‖z‖ - 1)| ≤ ‖lg z / z - Complex.log z + 1‖ := by
  have : (lg z / z).re - (Real.log ‖z‖ - 1) = (lg z / z - Complex.log z + 1).re := by
    simp [Complex.log_re]; ring
  rw [this]; exact Complex.abs_re_le_norm _

lemma interp_log_le (r : ℝ) (hr : 0 < r) : Real.log r ≤ 2 * r / 5 := by
  have h1 := Real.add_one_le_exp (Real.log r - 1)
  rw [Real.exp_sub, Real.exp_log hr] at h1
  have he := Real.exp_one_gt_d9
  have h2 : r / Real.exp 1 ≤ 2 * r / 5 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

lemma interp_D_half {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {z : ℂ} (h1 : 20 ≤ ‖z‖) (h8 : ‖z‖ ≤ 8 * z.re) :
    ‖lg z / z - Complex.log z + 1‖ ≤ 1 / 2 := by
  have hr : 0 < ‖z‖ := by linarith
  refine le_trans (interp_D_bound hst (by linarith) h8) ?_
  rw [div_le_iff₀ hr]
  have := interp_log_le ‖z‖ hr
  have := interp_log_two_pi.2
  have := Real.pi_lt_d2
  linarith

lemma interp_D_mu {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {x : ℝ} (hx : 2 ≤ x) {z : ℂ} (h1 : 2 * x / 3 ≤ ‖z‖) (h2 : ‖z‖ ≤ 2 * x)
    (h8 : ‖z‖ ≤ 8 * z.re) :
    ‖lg z / z - Complex.log z + 1‖ ≤ (9 + 3 / 4 * Real.log x) / x := by
  have hr : 0 < ‖z‖ := by linarith
  refine le_trans (interp_D_bound hst (by linarith) h8) ?_
  have hlog : Real.log ‖z‖ ≤ Real.log 2 + Real.log x := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hr h2
  have hl2 := Real.log_two_lt_d9
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have := interp_log_two_pi.2
  have := Real.pi_lt_d2
  have hnum : 1 + (Real.log ‖z‖ + π) / 2 + Real.log (2 * π) / 2 ≤ 6 + Real.log x / 2 := by
    linarith
  calc _ ≤ (6 + Real.log x / 2) / ‖z‖ := by gcongr
    _ ≤ (6 + Real.log x / 2) / (2 * x / 3) := by gcongr
    _ = _ := by field_simp; ring

lemma interp_re_ofReal_div (L : ℝ) (z : ℂ) : ((L : ℂ) / z).re = L * z.re / ‖z‖ ^ 2 := by
  rw [Complex.div_re]; simp [Complex.normSq_eq_norm_sq]

/-- The open set `U' = {x/3 < Re z, |z| < 5x/2}`. -/
def interp_U (x : ℝ) : Set ℂ := {z : ℂ | x / 3 < z.re ∧ ‖z‖ < 5 * x / 2}

lemma interp_U_open (x : ℝ) : IsOpen (interp_U x) :=
  (isOpen_lt continuous_const Complex.continuous_re).inter
    (isOpen_lt continuous_norm continuous_const)

lemma interp_U_props {x : ℝ} (hx : 3 ≤ x) {z : ℂ} (hz : z ∈ interp_U x) :
    0 < z.re ∧ z ≠ 0 ∧ x / 3 ≤ ‖z‖ ∧ 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 8 * z.re := by
  obtain ⟨h1, h2⟩ := hz
  have h3 := Complex.re_le_norm z
  refine ⟨by linarith, fun h => ?_, by linarith, by linarith, by linarith⟩
  rw [h] at h1; simp at h1; linarith

lemma interp_U_sub_re {x : ℝ} (hx : 3 ≤ x) : interp_U x ⊆ {z : ℂ | 0 < z.re} :=
  fun _ hz => (interp_U_props hx hz).1

lemma interp_G_diff {lg : ℂ → ℂ} (hlgd : DifferentiableOn ℂ lg {z : ℂ | 0 < z.re}) {x : ℝ}
    (hx : 3 ≤ x) (L : ℝ) : DifferentiableOn ℂ (interp_G lg L) (interp_U x) := by
  unfold interp_G
  exact ((differentiableOn_const _).add (hlgd.mono (interp_U_sub_re hx))).div differentiableOn_id
    (fun z hz => (interp_U_props hx hz).2.1)

lemma interp_a_diff {lg : ℂ → ℂ} (hlgd : DifferentiableOn ℂ lg {z : ℂ | 0 < z.re}) {x : ℝ}
    (hx : 3 ≤ x) (L : ℝ) (j : ℕ) : DifferentiableOn ℂ (interp_a lg L j) (interp_U x) := by
  unfold interp_a
  exact ((((Polynomial.differentiableOn _).mul
    ((differentiableOn_const _).mul (interp_G_diff hlgd hx L)).cexp).div_const _).div
      differentiableOn_id (fun z hz => (interp_U_props hx hz).2.1))

lemma interp_reG_lower {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {x L : ℝ} (hx : 60 ≤ x) (hL : 0 ≤ L) {z : ℂ} (hz : z ∈ interp_U x) :
    L / (19 * x) + Real.log ‖z‖ - 3 / 2 ≤ (interp_G lg L z).re := by
  unfold interp_G
  rw [add_div, Complex.add_re, interp_re_ofReal_div]
  obtain ⟨h0, hz0, h3, h1, h8⟩ := interp_U_props (by linarith) hz
  have hD := interp_D_half hst (by linarith : 20 ≤ ‖z‖) h8
  have hre := interp_re_div_sub lg z
  have hr : 0 < ‖z‖ := by linarith
  have h1' : L / (19 * x) ≤ L * z.re / ‖z‖ ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : ‖z‖ ^ 2 ≤ (5 * x / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz.2.le 2
    have hb : x * (x / 3) ≤ x * z.re := mul_le_mul_of_nonneg_left hz.1.le (by linarith)
    have : ‖z‖ ^ 2 ≤ z.re * (19 * x) := by nlinarith
    calc L * ‖z‖ ^ 2 ≤ L * (z.re * (19 * x)) := mul_le_mul_of_nonneg_left this hL
      _ = _ := by ring
  linarith [(abs_le.mp (le_trans hre hD)).1]

lemma interp_reG_upper {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {x L : ℝ} (hx : 60 ≤ x) (hL : 0 ≤ L) {z : ℂ} (hz1 : x / 2 ≤ z.re) (hz2 : ‖z‖ ≤ 3 * x / 2) :
    (interp_G lg L z).re ≤ 2 * L / x + Real.log ‖z‖ - 1 / 2 := by
  have h3 := Complex.re_le_norm z
  have hzU : z ∈ interp_U x := ⟨by linarith, by linarith⟩
  unfold interp_G
  rw [add_div, Complex.add_re, interp_re_ofReal_div]
  obtain ⟨h0, hz0, _, h1, h8⟩ := interp_U_props (by linarith) hzU
  have hD := interp_D_half hst (by linarith : 20 ≤ ‖z‖) h8
  have hre := interp_re_div_sub lg z
  have hr : 0 < ‖z‖ := by linarith
  have h1' : L * z.re / ‖z‖ ^ 2 ≤ 2 * L / x := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : z.re * x ≤ 2 * ‖z‖ ^ 2 := by nlinarith
    calc L * z.re * x = L * (z.re * x) := by ring
      _ ≤ L * (2 * ‖z‖ ^ 2) := mul_le_mul_of_nonneg_left this hL
      _ = _ := by ring
  linarith [(abs_le.mp (le_trans hre hD)).2]

lemma interp_powSum_bound {x : ℝ} (hx : 20 ≤ x) {N : ℕ} (hN : (N : ℝ) ≤ x / 8) {z : ℂ}
    (hz : z ∈ interp_U x) {j : ℕ} (hj : j ∈ Finset.Icc 1 N) :
    ‖(powSumPoly j).eval z‖ ≤ 16 * ‖z‖ ^ (2 * j + 1) := by
  obtain ⟨h0, hz0, h3, h1, h8⟩ := interp_U_props (by linarith) hz
  have hjN : (j : ℝ) ≤ N := by exact_mod_cast (Finset.mem_Icc.mp hj).2
  have hpi := Real.pi_gt_three
  have hA : (x / 3 + 1) / 2 ≤ ‖(z + 1) / 2‖ := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := Complex.re_le_norm (z + 1)
    simp only [Complex.add_re, Complex.one_re] at this
    linarith [hz.1]
  have hB : (x / 3 - 1) / 2 ≤ ‖(1 - z) / 2‖ := by
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
    have := Complex.abs_re_le_norm (1 - z)
    simp only [Complex.sub_re, Complex.one_re] at this
    linarith [hz.1, neg_abs_le (1 - z.re)]
  have hP := powSumPoly_norm_le (z := z) (j := j) (by nlinarith) (by nlinarith)
  have hj1 : (1 : ℝ) ≤ 2 * j + 1 := by have := (Nat.cast_nonneg j : (0 : ℝ) ≤ j); linarith
  calc _ ≤ 16 * (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) / (2 * j + 1) := hP
    _ ≤ 16 * (‖z‖ / 2 + 1 / 2) ^ (2 * j + 1) := div_le_self (by positivity) hj1
    _ ≤ _ := by gcongr; linarith

lemma interp_a_norm (lg : ℂ → ℂ) (L : ℝ) (j : ℕ) (z : ℂ) :
    ‖interp_a lg L j z‖ = ‖(powSumPoly j).eval z‖ *
      Real.exp (-(2 * j) * (interp_G lg L z).re) / (2 * j) / ‖z‖ := by
  unfold interp_a
  rw [norm_div, norm_div, norm_mul, Complex.norm_exp]
  congr 3
  · simp
  · norm_cast

lemma interp_a_term_bound {lg : ℂ → ℂ} {L s : ℝ} {j : ℕ} {z : ℂ} (hs : 0 ≤ s) (hj : 1 ≤ j)
    (hr : 0 < ‖z‖) (hG : Real.log ‖z‖ + 1 + s ≤ (interp_G lg L z).re)
    (hP : ‖(powSumPoly j).eval z‖ ≤ 16 * ‖z‖ ^ (2 * j + 1)) :
    ‖interp_a lg L j z‖ * (2 * j) * Real.exp (2 * j) ≤ 16 * Real.exp (-2 * s) := by
  have hj0 : (0 : ℝ) < j := by exact_mod_cast hj
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  rw [interp_a_norm]
  have hpow : ‖z‖ ^ (2 * j) = Real.exp ((2 * j) * Real.log ‖z‖) := by
    rw [show ((2 : ℝ) * j) = ((2 * j : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log hr]
  set E := Real.exp (-(2 * j) * (interp_G lg L z).re)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  calc ‖(powSumPoly j).eval z‖ * E / (2 * j) / ‖z‖ * (2 * j) * Real.exp (2 * j)
      = ‖(powSumPoly j).eval z‖ * E * Real.exp (2 * j) / ‖z‖ := by field_simp
    _ ≤ 16 * ‖z‖ ^ (2 * j + 1) * E * Real.exp (2 * j) / ‖z‖ := by gcongr
    _ = 16 * (‖z‖ ^ (2 * j) * E * Real.exp (2 * j)) := by rw [pow_succ]; field_simp
    _ = 16 * Real.exp (2 * j * (Real.log ‖z‖ + 1 - (interp_G lg L z).re)) := by
        rw [hpow, ← Real.exp_add, ← Real.exp_add]; congr 2; ring
    _ ≤ 16 * Real.exp (-2 * s) := by
        apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
        have hA : Real.log ‖z‖ + 1 - (interp_G lg L z).re ≤ -s := by linarith
        nlinarith [mul_nonneg (sub_nonneg.mpr hj1) hs,
          mul_nonneg hj0.le (by linarith : 0 ≤ -s - (Real.log ‖z‖ + 1 - (interp_G lg L z).re))]

lemma interp_hbound {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {x L : ℝ} (hx : 60 ≤ x) (hL : 48 * x ≤ L) {N : ℕ} (hN : (N : ℝ) ≤ x / 8) {z : ℂ}
    (hz : z ∈ interp_U x) :
    ∑ j ∈ Finset.Icc 1 N, ‖interp_a lg L j z‖ * (2 * j) * Real.exp (2 * j) ≤
      N * (16 * Real.exp (5 - 2 * (L / x) / 19)) := by
  obtain ⟨h0, hz0, h3, h1, h8⟩ := interp_U_props (by linarith) hz
  have hG := interp_reG_lower (lg := lg) (L := L) hst hx (by linarith) hz
  have hs : 0 ≤ L / x / 19 - 5 / 2 := by
    rw [sub_nonneg, div_div, le_div_iff₀ (by positivity)]; linarith
  have hterm : ∀ j ∈ Finset.Icc 1 N, ‖interp_a lg L j z‖ * (2 * j) * Real.exp (2 * j) ≤
      16 * Real.exp (5 - 2 * (L / x) / 19) := by
    intro j hj
    have := interp_a_term_bound (lg := lg) (L := L) hs (Finset.mem_Icc.mp hj).1 (by linarith)
      (by rw [show L / x / 19 = L / (19 * x) by field_simp]; linarith)
      (interp_powSum_bound (by linarith) hN hz hj)
    calc _ ≤ _ := this
      _ = _ := by congr 2; ring
  calc _ ≤ ∑ j ∈ Finset.Icc 1 N, 16 * Real.exp (5 - 2 * (L / x) / 19) := Finset.sum_le_sum hterm
    _ = _ := by rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; simp

/-! Numerics. Throughout `x ≥ 1000`, `log x ≥ 30` and `ℓ = L/x ≥ 100 log x`. -/

lemma interp_num_q {x ℓ : ℝ} (hx : 1000 ≤ x) (hlx : 30 ≤ Real.log x) (hℓ : 100 * Real.log x ≤ ℓ)
    {N : ℕ} (hN : (N : ℝ) ≤ x / 8) :
    N * (16 * Real.exp (5 - 2 * ℓ / 19)) ≤ Real.exp (-ℓ / 20) := by
  have h2x : (N : ℝ) * 16 ≤ Real.exp (1 + Real.log x) := by
    rw [Real.exp_add, Real.exp_log (by linarith)]
    have := Real.add_one_le_exp 1
    nlinarith
  calc (N : ℝ) * (16 * Real.exp (5 - 2 * ℓ / 19))
      = (N * 16) * Real.exp (5 - 2 * ℓ / 19) := by ring
    _ ≤ Real.exp (1 + Real.log x) * Real.exp (5 - 2 * ℓ / 19) := by gcongr
    _ = Real.exp (1 + Real.log x + (5 - 2 * ℓ / 19)) := by rw [← Real.exp_add]
    _ ≤ _ := by apply Real.exp_le_exp.mpr; linarith

lemma interp_num_q_quarter {ℓ : ℝ} (hℓ : 60 ≤ ℓ) : Real.exp (-ℓ / 20) ≤ 1 / 4 := by
  rw [neg_div, Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
  have := Real.add_one_le_exp (ℓ / 20)
  linarith

lemma interp_num_q_inv {x ℓ : ℝ} (hx : 1 ≤ x) (hℓ : 100 * Real.log x ≤ ℓ) :
    Real.exp (-ℓ / 20) ≤ 1 / x := by
  have hlx := Real.log_nonneg hx
  calc Real.exp (-ℓ / 20) ≤ Real.exp (-Real.log x) := Real.exp_le_exp.mpr (by linarith)
    _ = 1 / x := by rw [Real.exp_neg, Real.exp_log (by linarith), inv_eq_one_div]

lemma interp_num_eta {x ℓ q : ℝ} (hx : 1000 ≤ x) (hlx : 30 ≤ Real.log x) (hq : q ≤ 1 / x)
    {A B : ℝ} (hA : A ≤ (9 + 3 / 4 * Real.log x) / x) (hB : B ≤ (9 + 3 / 4 * Real.log x) / x) :
    A + B + 2 * q ≤ η₀ x ℓ := by
  unfold η₀
  have he := (Real.exp_pos (-ℓ / 5)).le
  have hx0 : 0 < x := by linarith
  have : (9 + 3 / 4 * Real.log x) / x + (9 + 3 / 4 * Real.log x) / x + 2 * (1 / x) ≤
      2 * (Real.log x + 4) / x := by
    have e1 : (9 + 3 / 4 * Real.log x) / x + (9 + 3 / 4 * Real.log x) / x + 2 * (1 / x) =
        (20 + 3 / 2 * Real.log x) / x := by field_simp; ring
    rw [e1, div_le_div_iff_of_pos_right hx0]
    linarith
  linarith

lemma interp_num_kappa0 {x q : ℝ} (hx : 1000 ≤ x) (hq : q ≤ 1 / x)
    {A : ℝ} (hA : A ≤ (9 + 3 / 4 * Real.log x) / x) : A + q ≤ 1 := by
  have hx0 : 0 < x := by linarith
  have hl := Real.log_le_sub_one_of_pos hx0
  have : (9 + 3 / 4 * Real.log x) / x + 1 / x ≤ 1 := by
    rw [← add_div, div_le_one hx0]; linarith
  linarith

lemma interp_num_growth {x ℓ r g w : ℝ} (hx : 2 ≤ x) (hr0 : 0 < r) (hr : r ≤ 3 * x / 2)
    (hg : g ≤ 2 * ℓ + Real.log r - 1 / 2) (hw : w ≤ 1 / 4) (hℓ : 0 ≤ ℓ) :
    (r + 1) / 2 + Real.exp (g + w) ≤ 3 * x * Real.exp (2 * ℓ) := by
  have h1 : Real.exp (g + w) ≤ Real.exp (2 * ℓ) * r := by
    calc Real.exp (g + w) ≤ Real.exp (2 * ℓ + Real.log r) := Real.exp_le_exp.mpr (by linarith)
      _ = _ := by rw [Real.exp_add, Real.exp_log hr0]
  have h2 : 1 ≤ Real.exp (2 * ℓ) := Real.one_le_exp (by linarith)
  have h3 : (r + 1) / 2 ≤ x * Real.exp (2 * ℓ) := by
    have := mul_le_mul_of_nonneg_left h2 (by linarith : (0 : ℝ) ≤ x)
    nlinarith
  have h4 : Real.exp (2 * ℓ) * r ≤ Real.exp (2 * ℓ) * (3 * x / 2) := by gcongr
  nlinarith

set_option maxHeartbeats 400000 in
lemma interp_num_approx {x L m : ℝ} {N : ℕ} (hx : 1000 ≤ x) (hlx : 30 ≤ Real.log x)
    (hL : 100 * Real.log x ≤ L / x) (hm1 : x / 2 ≤ m) (hm2 : m ≤ 3 * x / 2)
    (hN1 : x / 8 - 1 ≤ N) (hN2 : (N : ℝ) ≤ x / 8) :
    m ^ (2 * N + 2) * Real.exp (-(2 * N + 1) * (L / m)) ≤ Real.exp (-L / 8) := by
  have hx0 : 0 < x := by linarith
  have hm0 : 0 < m := by linarith
  have hL0 : 0 ≤ L := by
    have : 0 ≤ L / x := by linarith
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => by linarith [h.2])
  have hLx : 100 * x * Real.log x ≤ L := by
    rw [le_div_iff₀ hx0] at hL; linarith
  have hpow : m ^ (2 * N + 2) = Real.exp ((2 * N + 2) * Real.log m) := by
    rw [show ((2 : ℝ) * N + 2) = ((2 * N + 2 : ℕ) : ℝ) by push_cast; ring, Real.exp_nat_mul,
      Real.exp_log hm0]
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  -- a) `log m ≤ log x + 1/2`
  have ha : Real.log m ≤ Real.log x + 1 / 2 := by
    have h1 : Real.log m ≤ Real.log (3 / 2 * x) := Real.log_le_log hm0 (by linarith)
    rw [Real.log_mul (by norm_num) hx0.ne'] at h1
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 / 2 by norm_num)
    linarith
  have hlm : 0 ≤ Real.log m := Real.log_nonneg (by linarith)
  -- b) `L/m ≥ 2L/(3x)`
  have hb : 2 * L / (3 * x) ≤ L / m := by
    rw [div_le_div_iff₀ (by positivity) hm0]; nlinarith
  have hN0 : (0 : ℝ) ≤ 2 * N + 1 := by positivity
  -- d) `(2N+1) L/m ≥ (x/4 - 1)(2L/(3x))`
  have hd : (x / 4 - 1) * (2 * L / (3 * x)) ≤ (2 * N + 1) * (L / m) := by
    apply mul_le_mul (by linarith) hb (by positivity) hN0
  have hd' : (x / 4 - 1) * (2 * L / (3 * x)) = L / 6 - 2 * L / (3 * x) := by
    field_simp; ring
  -- f) `(2N+2) log m ≤ (x/4+2)(log x + 1/2)`
  have hf : (2 * N + 2) * Real.log m ≤ (x / 4 + 2) * (Real.log x + 1 / 2) :=
    mul_le_mul (by linarith) ha hlm (by linarith)
  have hg : (x / 4 + 2) * (Real.log x + 1 / 2) ≤ x * Real.log x := by nlinarith
  have hi : 2 * L / (3 * x) ≤ L / 1500 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  linarith

lemma interp_ball_geom {x : ℝ} (hx : 0 < x) {z : ℂ} (hz : z ∈ Metric.closedBall (x : ℂ) (x / 2)) :
    x / 2 ≤ z.re ∧ ‖z‖ ≤ 3 * x / 2 := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hz
  have h1 := Complex.abs_re_le_norm (z - x)
  simp only [Complex.sub_re, Complex.ofReal_re] at h1
  have h2 := norm_le_norm_add_norm_sub' z (x : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx] at h2
  constructor
  · linarith [neg_abs_le (z.re - x)]
  · linarith

lemma interp_inv_ball_geom {x : ℝ} (hx : 0 < x) {u : ℂ}
    (hu : u ∈ Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) :
    u ≠ 0 ∧ 0 < u.re ∧ 2 * x / 3 ≤ ‖u⁻¹‖ ∧ ‖u⁻¹‖ ≤ 2 * x ∧ x / 2 ≤ (u⁻¹).re := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hu
  set a : ℝ := x⁻¹ with ha
  have ha0 : 0 < a := inv_pos.mpr hx
  have hax : a * x = 1 := inv_mul_cancel₀ hx.ne'
  have hcast : ((x : ℂ))⁻¹ = (a : ℂ) := by rw [ha, Complex.ofReal_inv]
  rw [hcast] at hu
  have h1 := Complex.abs_re_le_norm (u - a)
  simp only [Complex.sub_re, Complex.ofReal_re] at h1
  have hre : a / 2 ≤ u.re := by linarith [neg_abs_le (u.re - a)]
  have h2 := norm_le_norm_add_norm_sub' u (a : ℂ)
  have h3 := norm_sub_norm_le (a : ℂ) u
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0] at h2 h3
  rw [norm_sub_rev] at h3
  have hn1 : a / 2 ≤ ‖u‖ := by linarith
  have hn2 : ‖u‖ ≤ 3 * a / 2 := by linarith
  have hu0 : u ≠ 0 := fun h => by rw [h, norm_zero] at hn1; linarith
  have hnorm0 : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  refine ⟨hu0, by linarith, ?_, ?_, ?_⟩
  · rw [norm_inv, le_inv_comm₀ (by positivity) hnorm0]
    calc ‖u‖ ≤ 3 * a / 2 := hn2
      _ = (2 * x / 3)⁻¹ := by rw [ha]; field_simp
  · rw [norm_inv, inv_le_comm₀ hnorm0 (by positivity)]
    calc (2 * x)⁻¹ = a / 2 := by rw [ha]; field_simp
      _ ≤ ‖u‖ := hn1
  · -- `|u - a|² ≤ a²/4` gives `|u|² ≤ 2 a Re u`
    have hsq : ‖u - (a : ℂ)‖ ^ 2 ≤ (a / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
    rw [Complex.sq_norm, Complex.normSq_apply] at hsq
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im,
      sub_zero] at hsq
    have hns : Complex.normSq u ≤ 2 * a * u.re := by
      rw [Complex.normSq_apply]; nlinarith
    have hnpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu0
    rw [Complex.inv_re, le_div_iff₀ hnpos]
    nlinarith

lemma interp_mu_eq (lg : ℂ → ℂ) {u : ℂ} (hre : 0 < u.re) :
    u * lg u⁻¹ + Complex.log u + 1 = lg u⁻¹ / u⁻¹ - Complex.log u⁻¹ + 1 := by
  have harg : u.arg ≠ π := fun h => by
    rw [Complex.arg_eq_pi_iff] at h; linarith [h.1]
  rw [Complex.log_inv u harg, div_inv_eq_mul]; ring

lemma interp_inv_mem_U {x : ℝ} (hx : 0 < x) {u : ℂ}
    (hu : u ∈ Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) : u⁻¹ ∈ interp_U x := by
  obtain ⟨_, _, _, h2, h3⟩ := interp_inv_ball_geom hx hu
  exact ⟨by linarith, by linarith⟩

lemma interp_mu_bound {lg : ℂ → ℂ}
    (hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖)
    {x : ℝ} (hx : 2 ≤ x) {u : ℂ} (hu : u ∈ Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) :
    ‖u * lg u⁻¹ + Complex.log u + 1‖ ≤ (9 + 3 / 4 * Real.log x) / x := by
  obtain ⟨_, hre, h1, h2, h3⟩ := interp_inv_ball_geom (by linarith) hu
  rw [interp_mu_eq lg hre]
  exact interp_D_mu hst hx h1 h2 (by linarith)

lemma interp_uform (lg v : ℂ → ℂ) (L : ℝ) {u : ℂ} (hu : u ≠ 0) :
    (u⁻¹ - 1) / 2 + Complex.exp (interp_G lg L u⁻¹ + v u⁻¹) =
      u⁻¹ * ((1 - u) / 2 + Complex.exp ((L : ℂ) * u +
        (u * lg u⁻¹ + Complex.log u + 1 + v u⁻¹)) / Complex.exp 1) := by
  unfold interp_G
  have h : Complex.exp ((L : ℂ) * u + (u * lg u⁻¹ + Complex.log u + 1 + v u⁻¹)) =
      Complex.exp (((L : ℂ) + lg u⁻¹) / u⁻¹ + v u⁻¹) * u * Complex.exp 1 := by
    rw [show (L : ℂ) * u + (u * lg u⁻¹ + Complex.log u + 1 + v u⁻¹) =
        ((L : ℂ) + lg u⁻¹) / u⁻¹ + v u⁻¹ + Complex.log u + 1 by rw [div_inv_eq_mul]; ring,
      Complex.exp_add, Complex.exp_add, Complex.exp_log hu]
  rw [h]
  have he : Complex.exp 1 ≠ 0 := Complex.exp_ne_zero 1
  field_simp

lemma interp_kappa_diff {lg v : ℂ → ℂ} (hlgd : DifferentiableOn ℂ lg {z : ℂ | 0 < z.re}) {x : ℝ}
    (hx : 3 ≤ x) (hv : DifferentiableOn ℂ v (interp_U x)) :
    DifferentiableOn ℂ (fun u => u * lg u⁻¹ + Complex.log u + 1 + v u⁻¹)
      (Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) := by
  have hx0 : 0 < x := by linarith
  have hinv : DifferentiableOn ℂ (fun u : ℂ => u⁻¹) (Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) :=
    differentiableOn_id.inv (fun u hu => (interp_inv_ball_geom hx0 hu).1)
  have hmapsU : Set.MapsTo (fun u : ℂ => u⁻¹) (Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2))
      (interp_U x) := fun u hu => interp_inv_mem_U hx0 hu
  have hmapsRe : Set.MapsTo (fun u : ℂ => u⁻¹) (Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2))
      {z : ℂ | 0 < z.re} := fun u hu => (interp_U_props hx (interp_inv_mem_U hx0 hu)).1
  have hlog : DifferentiableOn ℂ (fun u : ℂ => Complex.log u)
      (Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2)) :=
    differentiableOn_id.clog (fun u hu =>
      Complex.mem_slitPlane_iff.mpr (Or.inl (interp_inv_ball_geom hx0 hu).2.1))
  exact ((differentiableOn_id.mul (hlgd.comp hinv hmapsRe)).add hlog |>.add_const 1).add
    (hv.comp hinv hmapsU)

lemma interp_norm4 (A B a b : ℂ) : ‖(A + a) - (B + b)‖ ≤ ‖A‖ + ‖B‖ + (‖a‖ + ‖b‖) := by
  calc ‖(A + a) - (B + b)‖ = ‖(A - B) + (a - b)‖ := by ring_nf
    _ ≤ ‖A - B‖ + ‖a - b‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (norm_sub_le _ _) (norm_sub_le _ _)

/-- **Proposition 3.1.** -/
theorem interpolatingFunction : InterpolatingFunction := by
  obtain ⟨lg, hlgd, hlg, hst₀⟩ := stirlingFormula
  -- Lemma 2.1 is used on the sector `|z| ≤ 8 Re z`
  have hst : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 8 * z.re →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * π) / 2)‖ ≤ 1 / ‖z‖ :=
    fun z h1 h8 => hst₀ z (by linarith) h1
  refine ⟨max 1000 (Real.exp 30), fun t x₀ hX hℓ => ?_⟩
  set x : ℝ := (x₀ : ℝ) with hx_def
  set L : ℝ := Real.log t with hL_def
  have hxc : ((x : ℝ) : ℂ) = (x₀ : ℂ) := by rw [hx_def, Complex.ofReal_natCast]
  have hx : 1000 ≤ x := le_trans (le_max_left _ _) hX
  have hlx : 30 ≤ Real.log x := by
    have := le_trans (le_max_right _ _) hX
    calc (30 : ℝ) = Real.log (Real.exp 30) := (Real.log_exp 30).symm
      _ ≤ Real.log x := Real.log_le_log (Real.exp_pos _) this
  have hx0 : 0 < x := by linarith
  set ℓ := L / x with hℓ_def
  have hℓ1 : 100 * Real.log x ≤ ℓ := hℓ
  have hℓ0 : 3000 ≤ ℓ := by linarith
  have hL48 : 48 * x ≤ L := by
    have : L = ℓ * x := by rw [hℓ_def]; field_simp
    rw [this]; nlinarith
  set N : ℕ := x₀ / 8 with hN_def
  have hN2 : (N : ℝ) ≤ x / 8 := by
    rw [hN_def, hx_def]; exact_mod_cast Nat.cast_div_le
  have hN1 : x / 8 - 1 ≤ N := by
    have h := Nat.lt_div_mul_add (a := x₀) (b := 8) (by norm_num)
    have h' : (x₀ : ℝ) < (x₀ / 8 : ℕ) * 8 + 8 := by exact_mod_cast h
    rw [hx_def, hN_def]; linarith
  set q : ℝ := Real.exp (-ℓ / 20) with hq_def
  have hq4 : q ≤ 1 / 4 := interp_num_q_quarter (by linarith)
  have hqx : q ≤ 1 / x := interp_num_q_inv (by linarith) hℓ1
  have hbound : ∀ z ∈ interp_U x, ∑ j ∈ Finset.Icc 1 N,
      ‖interp_a lg L j z‖ * (2 * j) * Real.exp (2 * j) ≤ q := fun z hz =>
    le_trans (interp_hbound hst (by linarith) hL48 hN2 hz) (interp_num_q hx hlx hℓ1 hN2)
  obtain ⟨v, hvd, -, hvq, hvstab⟩ := analytic_fixed_point (interp_U_open x) N (interp_a lg L)
    (fun j => interp_a_diff hlgd (by linarith) L j) hq4 hbound
  have hball : ∀ z ∈ Metric.closedBall (x₀ : ℂ) (x / 2), x / 2 ≤ z.re ∧ ‖z‖ ≤ 3 * x / 2 :=
    fun z hz => interp_ball_geom hx0 (by rwa [hxc])
  have hsub : Metric.closedBall (x₀ : ℂ) (x / 2) ⊆ interp_U x := fun z hz => by
    obtain ⟨h1, h2⟩ := hball z hz
    exact ⟨by linarith, by linarith⟩
  have hball' : Metric.closedBall ((x₀ : ℂ)⁻¹) (x⁻¹ / 2) =
      Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2) := by rw [hxc]
  refine ⟨fun z => (z - 1) / 2 + Complex.exp (interp_G lg L z + v z),
    fun u => u * lg u⁻¹ + Complex.log u + 1 + v u⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- analyticity of `F`
    exact (((differentiableOn_id.sub_const 1).div_const 2).add
      ((interp_G_diff hlgd (by linarith) L).add hvd).cexp).mono hsub
  · -- part (a)
    intro n m hnm h2m hmx
    have hmx' := abs_le.mp hmx
    have hm1 : x / 2 ≤ m := by linarith
    have hm2 : (m : ℝ) ≤ 3 * x / 2 := by linarith
    have hm0 : 0 < m := by
      have : (0 : ℝ) < m := by linarith
      exact_mod_cast this
    have hmU : (m : ℂ) ∈ interp_U x := by
      refine ⟨?_, ?_⟩
      · rw [Complex.natCast_re]; linarith
      · rw [Complex.norm_natCast]; linarith
    have core := interp_approx_core hlg L N v (n := n) (m := m) (by rw [hL_def, hnm]) h2m hm0
      (le_trans (hvq _ hmU) hq4) (hvstab _ hmU)
    calc _ ≤ _ := core
      _ ≤ _ := interp_num_approx hx hlx hℓ1 hm1 hm2 hN1 hN2
  · -- analyticity of `κ`
    rw [hball']
    exact interp_kappa_diff hlgd (by linarith) hvd
  · -- `|κ(u) - κ(u₀)| ≤ η₀`
    intro u hu
    rw [hball'] at hu
    have hu0 : (x : ℂ)⁻¹ ∈ Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2) :=
      Metric.mem_closedBall_self (by positivity)
    rw [← hxc]
    have hA := interp_mu_bound hst (by linarith) hu
    have hB := interp_mu_bound hst (by linarith) hu0
    have hvA := hvq _ (interp_inv_mem_U hx0 hu)
    have hvB := hvq _ (interp_inv_mem_U hx0 hu0)
    beta_reduce
    refine le_trans (interp_norm4 _ _ _ _) ?_
    have := interp_num_eta (ℓ := ℓ) hx hlx hqx hA hB
    linarith
  · -- `|κ(u₀)| ≤ 1`
    have hu0 : (x : ℂ)⁻¹ ∈ Metric.closedBall ((x : ℂ)⁻¹) (x⁻¹ / 2) :=
      Metric.mem_closedBall_self (by positivity)
    rw [← hxc]
    have hB := interp_mu_bound hst (by linarith) hu0
    have hvB := hvq _ (interp_inv_mem_U hx0 hu0)
    beta_reduce
    refine le_trans (norm_add_le _ _) ?_
    linarith [interp_num_kappa0 hx hqx hB]
  · intro u hu _
    rw [hball'] at hu
    exact interp_uform lg v L (interp_inv_ball_geom hx0 hu).1
  · -- growth
    intro z hz
    obtain ⟨h1, h2⟩ := hball z hz
    have hzU := hsub hz
    have hr0 : 0 < ‖z‖ := by linarith [Complex.re_le_norm z]
    have hG := interp_reG_upper (lg := lg) (L := L) hst (by linarith) (by linarith) h1 h2
    have hw : (v z).re ≤ 1 / 4 := le_trans (Complex.re_le_norm _) (le_trans (hvq z hzU) hq4)
    have hnorm : ‖(z - 1) / 2 + Complex.exp (interp_G lg L z + v z)‖ ≤
        (‖z‖ + 1) / 2 + Real.exp ((interp_G lg L z).re + (v z).re) := by
      refine le_trans (norm_add_le _ _) ?_
      rw [Complex.norm_exp, Complex.add_re, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num]
      gcongr
      exact le_trans (norm_sub_le _ _) (by simp)
    refine le_trans hnorm (interp_num_growth (by linarith) hr0 h2 ?_ hw (by linarith))
    rw [hℓ_def]; linarith [show 2 * L / x = 2 * (L / x) by ring]

end Singmaster
