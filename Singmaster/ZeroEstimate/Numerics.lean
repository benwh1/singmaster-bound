module

public import Singmaster.Basic

@[expose] public section

/-!
# Proposition 6.1: the truncation inequality

`num_trunc` shows that the truncation error is small:
`4 k ν Q e^{(4k+2)T} max(1, (4ν/T)^ν) δ' ≤ 1/2`, where `Q = ((k+1) 2^{4k+2})^{ν_max}` and
`δ' = (1/5) (10/a₀)^{J+1}`. This combines (6.5) and (6.6).
-/

open Real

namespace Singmaster

/-- `x ^ n = exp (n log x)` for `x > 0`, in the form used below. -/
lemma num_pow_eq_exp {x : ℝ} (hx : 0 < x) (n : ℕ) : x ^ n = exp (n * log x) := by
  rw [Real.exp_nat_mul, Real.exp_log hx]

/-- `a₀ k = 10 exp c` with `c = (2k+3/2) log(16k+12) + 10.75k + 5.5`. -/
lemma num_a₀_eq (k : ℕ) :
    a₀ k = 10 * exp ((2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5)) := by
  have h16 : (0 : ℝ) < 16 * k + 12 := by positivity
  unfold a₀
  rw [Real.rpow_def_of_pos h16, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Factor 1: `4 k N ≤ e^T`. -/
lemma num_trunc_f1 {k N : ℕ} {T : ℝ} (hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ T)
    (hN : (N : ℝ) ≤ (4 * k + 3) * T) : 4 * (k : ℝ) * N ≤ exp T := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hT0 : (0 : ℝ) ≤ T := le_trans (by positivity) hT
  have hT10 : (10 : ℝ) ≤ T := by nlinarith
  have h1 : 4 * (k : ℝ) * N ≤ 4 * k * ((4 * k + 3) * T) :=
    mul_le_mul_of_nonneg_left hN (by positivity)
  have h2 : 4 * (k : ℝ) * (4 * k + 3) ≤ 1.6 * T := by nlinarith
  have h3 : 4 * (k : ℝ) * ((4 * k + 3) * T) ≤ 1.6 * T * T := by
    have := mul_le_mul_of_nonneg_right h2 hT0
    linarith
  have h4 : 1.6 * T * T ≤ T ^ 3 / 6 := by
    have := mul_le_mul_of_nonneg_left hT10 (mul_nonneg hT0 hT0)
    nlinarith
  have h5 := Real.pow_div_factorial_le_exp T hT0 3
  norm_num [Nat.factorial] at h5
  linarith

/-- Factor 2: `((k+1) 2^{4k+2})^{n_max} ≤ e^{(17.5k+7)T}`. -/
lemma num_trunc_f2 {k nmax : ℕ} {T : ℝ} (hT0 : 0 ≤ T) (hnmax : (nmax : ℝ) ≤ 5 * T) :
    (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ nmax ≤ exp ((17.5 * k + 7) * T) := by
  have hk1 : (k : ℝ) + 1 ≤ 2 ^ k := by exact_mod_cast Nat.lt_two_pow_self (n := k)
  have hQ : ((k : ℝ) + 1) * 2 ^ (4 * k + 2) ≤ 2 ^ (5 * k + 2) := by
    have e : (2 : ℝ) ^ (5 * k + 2) = 2 ^ k * 2 ^ (4 * k + 2) := by
      rw [← pow_add]; congr 1; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hk1 (by positivity)
  have h1 : (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ nmax ≤ ((2 : ℝ) ^ (5 * k + 2)) ^ nmax :=
    pow_le_pow_left₀ (by positivity) hQ nmax
  have e2 : (2 : ℝ) ^ ((5 * k + 2) * nmax) = exp (((5 * k + 2) * nmax : ℕ) * log 2) :=
    num_pow_eq_exp (by norm_num) _
  rw [← pow_mul, e2] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  push_cast
  have hl2 := Real.log_two_lt_d9
  have hl0 : 0 < log (2 : ℝ) := Real.log_pos (by norm_num)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : (5 * (k : ℝ) + 2) * nmax * log 2 ≤ (5 * (k : ℝ) + 2) * (5 * T) * log 2 := by
    apply mul_le_mul_of_nonneg_right _ hl0.le
    exact mul_le_mul_of_nonneg_left hnmax (by positivity)
  have h3 : (5 * (k : ℝ) + 2) * (5 * T) * log 2 ≤ (5 * (k : ℝ) + 2) * (5 * T) * 0.7 := by
    apply mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- Factor 4: `max 1 ((4N/T)^N) ≤ e^{(4k+3) T log(16k+12)}`. -/
lemma num_trunc_f4 {k N : ℕ} {T : ℝ} (hT0 : 0 < T) (hN : (N : ℝ) ≤ (4 * k + 3) * T) :
    max 1 ((4 * N / T) ^ N) ≤ exp ((4 * k + 3) * T * log (16 * k + 12)) := by
  have h16 : (1 : ℝ) ≤ 16 * k + 12 := by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hq : 4 * (N : ℝ) / T ≤ 16 * k + 12 := by
    rw [div_le_iff₀ hT0]; linarith
  have h1 : max 1 ((4 * N / T) ^ N) ≤ (16 * (k : ℝ) + 12) ^ N :=
    max_le (one_le_pow₀ h16) (pow_le_pow_left₀ (div_nonneg (by positivity) hT0.le) hq N)
  have e : (16 * (k : ℝ) + 12) ^ N = exp (N * log (16 * k + 12)) := num_pow_eq_exp (by linarith) _
  rw [e] at h1
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  exact mul_le_mul_of_nonneg_right hN (Real.log_nonneg h16)

/-- Factor 5: `(1/5)(10/a₀)^{J+1} ≤ e^{-2T c}`. -/
lemma num_trunc_f5 {k J : ℕ} {T : ℝ} (hJ : 2 * T ≤ J) :
    (1 / 5) * (10 / a₀ k) ^ (J + 1) ≤
      exp (-(2 * T) * ((2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5))) := by
  set c := (2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5) with hc
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hc0 : 0 ≤ c := by
    have : 0 ≤ log (16 * (k : ℝ) + 12) := Real.log_nonneg (by linarith)
    positivity
  have h10 : 10 / a₀ k = exp (-c) := by
    rw [num_a₀_eq, ← hc, Real.exp_neg]
    field_simp
  rw [h10, ← Real.exp_nat_mul]
  have h1 : (1 / 5) * exp (((J + 1 : ℕ) : ℝ) * -c) ≤ exp (((J + 1 : ℕ) : ℝ) * -c) := by
    have := (exp_pos (((J + 1 : ℕ) : ℝ) * -c)).le
    linarith
  refine h1.trans (Real.exp_le_exp.mpr ?_)
  push_cast
  have : 2 * T * c ≤ ((J : ℝ) + 1) * c := mul_le_mul_of_nonneg_right (by linarith) hc0
  linarith

theorem num_trunc {k N nmax J : ℕ} {T : ℝ} (hk : 1 ≤ k)
    (hT : 10 * ((k : ℝ) + 1) ^ 2 ≤ T) (hN : (N : ℝ) ≤ (4 * k + 3) * T)
    (hnmax : (nmax : ℝ) ≤ 5 * T) (hJ : 2 * T ≤ J) :
    4 * k * N * (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ nmax * exp ((4 * k + 2) * T) *
        max 1 ((4 * N / T) ^ N) * ((1 / 5) * (10 / a₀ k) ^ (J + 1)) ≤ 1 / 2 := by
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le (by positivity) hT
  have e1 := num_trunc_f1 hT hN
  have e2 := num_trunc_f2 (k := k) hT0.le hnmax
  have e4 := num_trunc_f4 hT0 hN
  have e5 := num_trunc_f5 (k := k) hJ
  have p5 : 0 ≤ (1 / 5) * (10 / a₀ k) ^ (J + 1) := by have := a₀_pos k; positivity
  have step : 4 * k * N * (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ nmax * exp ((4 * k + 2) * T) *
        max 1 ((4 * N / T) ^ N) * ((1 / 5) * (10 / a₀ k) ^ (J + 1)) ≤
      exp T * exp ((17.5 * k + 7) * T) * exp ((4 * k + 2) * T) *
        exp ((4 * k + 3) * T * log (16 * k + 12)) *
        exp (-(2 * T) * ((2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5))) := by
    gcongr
  refine step.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  have hsum : T + (17.5 * k + 7) * T + (4 * k + 2) * T + (4 * k + 3) * T * log (16 * k + 12) +
      -(2 * T) * ((2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5)) = -T := by
    ring
  rw [hsum, Real.exp_neg]
  have : T + 1 ≤ exp T := Real.add_one_le_exp T
  rw [inv_le_comm₀ (exp_pos T) (by norm_num)]
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h4 : (2 : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have : (40 : ℝ) ≤ T := by linarith
  linarith

/-- `log x ≤ 2 log 2 + x/4 - 1` for `x > 0`. -/
lemma num_log_le_quarter {x : ℝ} (hx : 0 < x) : log x ≤ 2 * log 2 + x / 4 - 1 := by
  have h := Real.log_le_sub_one_of_pos (show 0 < x / 4 by positivity)
  rw [Real.log_div hx.ne' (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow] at h
  push_cast at h
  linarith

end Singmaster
