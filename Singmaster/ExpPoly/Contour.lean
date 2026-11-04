module

public import Mathlib

@[expose] public section

/-!
# Lemma 5.1: contour integrals

Cauchy's formula for the integrals `∮ e^{s w}/(w - a)^{p+1} dw`, and the derivatives at `0` of
`s^p e^{a s}`. These give the inversion formulas (5.1).
-/

open Complex Metric Real

namespace Singmaster

/-- The Cauchy-type integral `Φ_n(w) = ∮ (z - w)^{-(n+1)} e^{s z} dz`. -/
noncomputable def ctr_Phi (c s : ℂ) (r : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  ∮ z in C(c, r), (z - w) ^ (-((n : ℤ) + 1)) • cexp (s * z)

/-- `Φ_n(w) = 2πi s^n e^{s w} / n!` on the open disc, by induction on `n`: `Φ_0` is Cauchy's
integral formula, and `Φ_n' = (n+1) Φ_{n+1}` off the circle. -/
lemma ctr_Phi_eq (c s : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ n : ℕ, ∀ w ∈ ball c r,
      ctr_Phi c s r n w = 2 * π * I * (s ^ n * cexp (s * w) / n.factorial) := by
  have hci : CircleIntegrable (fun z => cexp (s * z)) c r :=
    (Continuous.continuousOn (by fun_prop)).circleIntegrable hr.le
  intro n
  induction n with
  | zero =>
    intro w hw
    have h := (DifferentiableOn.circleIntegral_sub_inv_smul (f := fun z => cexp (s * z))
      (c := c) (R := r) (by fun_prop) hw)
    simp only [ctr_Phi, Nat.cast_zero, zero_add, zpow_neg_one, pow_zero, one_mul,
      Nat.factorial_zero, Nat.cast_one, div_one]
    rw [h, smul_eq_mul]
  | succ n ih =>
    intro w hw
    have hsph : w ∉ sphere c |r| := by
      rw [abs_of_pos hr]
      exact fun h => (ne_of_lt (mem_ball.mp hw)) (mem_sphere.mp h)
    have hD := hasDerivAt_circleIntegral_sub_zpow_smul (n := -((n : ℤ) + 1)) hci hsph
    have hev : (fun w => ∮ z in C(c, r), (z - w) ^ (-((n : ℤ) + 1)) • cexp (s * z)) =ᶠ[nhds w]
        (fun w => 2 * π * I * (s ^ n * cexp (s * w) / n.factorial)) := by
      filter_upwards [isOpen_ball.mem_nhds hw] with x hx
      exact ih x hx
    have hG : HasDerivAt (fun w => 2 * π * I * (s ^ n * cexp (s * w) / n.factorial))
        (2 * π * I * (s ^ n * (cexp (s * w) * (s * 1)) / n.factorial)) w :=
      ((((hasDerivAt_id w).const_mul s).cexp.const_mul (s ^ n)).div_const _).const_mul _
    have huniq := (hD.congr_of_eventuallyEq hev.symm).unique hG
    have hexp : -((n : ℤ) + 1) - 1 = -(((n + 1 : ℕ) : ℤ) + 1) := by push_cast; ring
    rw [hexp] at huniq
    change (-(((-((n : ℤ) + 1)) : ℤ) : ℂ)) • ctr_Phi c s r (n + 1) w = _ at huniq
    rw [smul_eq_mul] at huniq
    have hn : (-(((-((n : ℤ) + 1)) : ℤ) : ℂ)) = (n : ℂ) + 1 := by push_cast; ring
    rw [hn] at huniq
    have hn0 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [Nat.factorial_succ, Nat.cast_mul]
    have hf0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    apply mul_left_cancel₀ hn0
    rw [huniq]
    push_cast
    field_simp
    ring

/-- Cauchy's formula for derivatives of `w ↦ e^{s w}`, at any point `a` inside the circle. -/
theorem circleIntegral_exp_div_sub_pow {c a s : ℂ} {r : ℝ} (hr : 0 < r) (ha : a ∈ ball c r)
    (p : ℕ) :
    (∮ w in C(c, r), cexp (s * w) / (w - a) ^ (p + 1)) =
      2 * π * I * (s ^ p * cexp (s * a) / p.factorial) := by
  rw [← ctr_Phi_eq c s hr p a ha, ctr_Phi]
  congr 1
  funext w
  rw [smul_eq_mul, div_eq_inv_mul, ← zpow_natCast, ← zpow_neg]
  push_cast
  rfl

/-- The same integral vanishes when `a` lies outside the closed disc. -/
theorem circleIntegral_exp_div_sub_pow_of_notMem {c a s : ℂ} {r : ℝ} (hr : 0 < r)
    (ha : a ∉ closedBall c r) (p : ℕ) :
    (∮ w in C(c, r), cexp (s * w) / (w - a) ^ (p + 1)) = 0 := by
  have hd : ∀ w ∈ closedBall c r,
      DifferentiableAt ℂ (fun w => cexp (s * w) / (w - a) ^ (p + 1)) w := by
    intro w hw
    have hne : w - a ≠ 0 := sub_ne_zero.mpr (fun h => ha (h ▸ hw))
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (pow_ne_zero _ hne)
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hr.le Set.countable_empty
    (fun w hw => (hd w hw).continuousAt.continuousWithinAt)
    (fun w hw => hd w (ball_subset_closedBall hw.1))

/-- Derivatives at `0` of `s^p e^{a s}`. -/
theorem iteratedDeriv_pow_mul_exp_zero (a : ℂ) (p m : ℕ) :
    iteratedDeriv m (fun s : ℂ => s ^ p * cexp (a * s)) 0 = (m.descFactorial p : ℂ) * a ^ (m - p) := by
  rw [iteratedDeriv_fun_mul (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_fun_pow_zero, iteratedDeriv_cexp_const_mul, mul_zero, Complex.exp_zero,
    mul_one]
  simp only [Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast; ring
  · simp only [Finset.mem_range, not_lt] at h
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
    simp

end Singmaster
