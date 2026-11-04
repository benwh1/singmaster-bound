module

public import Singmaster.Stirling.Series

@[expose] public section

/-!
# Stirling's formula at the integers

`S = σ + J` satisfies `S(m+1) - S(m) = log(m+1)`, because `J(m) - J(m+1) = j(m)`. Hence
`S(m) - log m!` is constant for `m ≥ 1`. It tends to `0` by Binet's bound (`J(m) → 0`) and
Mathlib's Stirling formula for `m!` (`Stirling.tendsto_stirlingSeq`), so `lg m = log m!`.
-/

open Complex Filter

namespace Singmaster

/-- The complex log of a natural number is the cast of its real log. -/
theorem st_ofReal_log_nat (n : ℕ) : ((Real.log n : ℝ) : ℂ) = Complex.log n := by
  rw [Complex.ofReal_log (Nat.cast_nonneg n)]; simp

theorem st_ofReal_log_nat_succ (n : ℕ) :
    ((Real.log ((n : ℝ) + 1) : ℝ) : ℂ) = Complex.log ((n : ℂ) + 1) := by
  have := st_ofReal_log_nat (n + 1); push_cast at this; exact this

/-- `σ(n)` at a natural number, as a real number. -/
theorem st_stirlingMain_nat (n : ℕ) :
    stirlingMain n = ((((n : ℝ) + 1 / 2) * Real.log n - n + Real.log (2 * Real.pi) / 2 : ℝ) : ℂ) := by
  unfold stirlingMain
  rw [← st_ofReal_log_nat]; push_cast; ring

/-- `j(n)` at a natural number, as a real number. -/
theorem st_binetTerm_nat (n : ℕ) :
    binetTerm n =
      ((((n : ℝ) + 1 / 2) * (Real.log ((n : ℝ) + 1) - Real.log n) - 1 : ℝ) : ℂ) := by
  unfold binetTerm
  rw [← st_ofReal_log_nat, ← st_ofReal_log_nat_succ]; push_cast; ring

/-- `J(n) = j(n) + J(n+1)`. -/
theorem st_binetJ_step {n : ℕ} (hn : 1 ≤ n) :
    binetJ n = binetTerm n + binetJ ((n + 1 : ℕ) : ℂ) := by
  have hre : 0 < (n : ℂ).re := by
    rw [Complex.natCast_re]; exact_mod_cast hn
  unfold binetJ
  rw [(binetJ_summable hre).tsum_eq_zero_add]
  congr 1
  · simp
  · congr 1; ext b; congr 1; push_cast; ring

/-- `D(n) = S(n) - log n!`. -/
noncomputable def st_D (n : ℕ) : ℂ := stirlingMain n + binetJ n - ((Real.log (n.factorial) : ℝ) : ℂ)

theorem st_D_succ {n : ℕ} (hn : 1 ≤ n) : st_D (n + 1) = st_D n := by
  unfold st_D
  have hfac : Real.log ((n + 1).factorial : ℕ) = Real.log ((n : ℝ) + 1) + Real.log (n.factorial) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    push_cast; ring
  rw [st_binetJ_step hn, st_stirlingMain_nat, st_stirlingMain_nat, st_binetTerm_nat, hfac]
  push_cast
  ring

theorem st_D_eq_one {n : ℕ} (hn : 1 ≤ n) : st_D n = st_D 1 := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_D_succ hk, ih]

/-- For `n ≥ 1`, `σ(n) - log n! = ½ log π - log (stirlingSeq n)`. -/
theorem st_sigma_sub_log_fac {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) + 1 / 2) * Real.log n - n + Real.log (2 * Real.pi) / 2 - Real.log (n.factorial) =
      Real.log Real.pi / 2 - Real.log (Stirling.stirlingSeq n) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact this.ne'
  rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hn0,
    Real.log_div hn0 (Real.exp_pos 1).ne', Real.log_exp,
    Real.log_mul (by norm_num) Real.pi_ne_zero]
  ring

theorem st_D_eq {n : ℕ} (hn : 1 ≤ n) :
    st_D n = ((Real.log Real.pi / 2 - Real.log (Stirling.stirlingSeq n) : ℝ) : ℂ) + binetJ n := by
  unfold st_D
  rw [st_stirlingMain_nat, ← st_sigma_sub_log_fac hn]
  push_cast
  ring

theorem st_D_tendsto : Tendsto st_D atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.log Real.pi / 2 - Real.log (Stirling.stirlingSeq n))
      atTop (nhds 0) := by
    have hl : Tendsto (fun n : ℕ => Real.log (Stirling.stirlingSeq n)) atTop
        (nhds (Real.log (Real.sqrt Real.pi))) :=
      Stirling.tendsto_stirlingSeq_sqrt_pi.log (Real.sqrt_ne_zero'.mpr Real.pi_pos)
    rw [Real.log_sqrt Real.pi_pos.le] at hl
    have := (tendsto_const_nhds (x := Real.log Real.pi / 2)).sub hl
    simpa using this
  have h1c : Tendsto (fun n : ℕ =>
      (((Real.log Real.pi / 2 - Real.log (Stirling.stirlingSeq n) : ℝ)) : ℂ)) atTop (nhds 0) := by
    have := (Complex.continuous_ofReal.tendsto 0).comp h1
    rw [Complex.ofReal_zero] at this
    exact this
  have h2 : Tendsto (fun n : ℕ => binetJ n) atTop (nhds 0) := by
    have hb : Tendsto (fun n : ℕ => (4 / 9 : ℝ) / n) atTop (nhds 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hre : 0 < (n : ℂ).re := by
      rw [Complex.natCast_re]; exact_mod_cast hn
    have hnorm : ‖(n : ℂ)‖ = n := by simp
    have h1n : 1 ≤ ‖(n : ℂ)‖ := by rw [hnorm]; exact_mod_cast hn
    calc ‖binetJ n‖ ≤ 4 / (9 * ‖(n : ℂ)‖) := binetJ_norm_le hre h1n
      _ = (4 / 9 : ℝ) / n := by rw [hnorm]; ring
  have := h1c.add h2
  rw [add_zero] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (st_D_eq hn).symm

theorem st_D_one : st_D 1 = 0 := by
  have hc : Tendsto st_D atTop (nhds (st_D 1)) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (st_D_eq_one hn).symm
  exact tendsto_nhds_unique hc st_D_tendsto

theorem lgStirling_nat (m : ℕ) : lgStirling m = Real.log (m.factorial) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [lgStirling]
  · have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have hD : st_D m = 0 := by rw [st_D_eq_one hm, st_D_one]
    unfold st_D at hD
    rw [lgStirling]
    simp only [hm0, ↓reduceIte]
    exact sub_eq_zero.mp hD

end Singmaster
