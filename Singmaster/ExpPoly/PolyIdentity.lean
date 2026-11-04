module

public import Mathlib

@[expose] public section

/-!
# Lemma 5.1: the polynomial identity behind Laplace inversion

For `G₀(s) = s^p e^{a s}` the derivatives at `0` are `y_m = m^{(p)} a^{m-p}` (a falling factorial,
`m.descFactorial p`). If `χ` is divisible by `(X - a)^{p+1}`, then
`(X - a)^{p+1} ∑_{m<M} y_m χ_m = p! χ`, where `χ_m = divX^[m+1] χ = ∑_{l>m} χ_l X^{l-m-1}`
(`poly_laplace_identity`). Evaluated at `w`, this says that `∑_m y_m χ_m(w)/χ(w) = p!/(w-a)^{p+1}`,
which is the Laplace transform of `s^p e^{as}`.
-/

open Polynomial

namespace Singmaster

theorem lap_coeff_divX_iter (f : ℂ[X]) (m n : ℕ) : (divX^[m] f).coeff n = f.coeff (n + m) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', coeff_divX, ih]
    congr 1; omega

theorem lap_divX_iter_eq_zero (f : ℂ[X]) (N : ℕ) (hN : f.natDegree < N) : divX^[N] f = 0 := by
  ext n
  rw [lap_coeff_divX_iter, coeff_zero]
  exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem lap_X_mul_divX_iter (f : ℂ[X]) (m : ℕ) :
    X * divX^[m + 1] f = divX^[m] f - C (f.coeff m) := by
  have h := divX_mul_X_add (divX^[m] f)
  rw [Function.iterate_succ_apply', mul_comm]
  rw [lap_coeff_divX_iter, zero_add] at h
  exact eq_sub_of_add_eq h

theorem lap_general_step (a : ℂ) (f : ℂ[X]) (N : ℕ) (hN : divX^[N] f = 0) (y : ℕ → ℂ) :
    (X - C a) * ∑ m ∈ Finset.range N, C (y m) * divX^[m + 1] f
      = C (y 0) * f + ∑ m ∈ Finset.range N, C (y (m + 1) - a * y m) * divX^[m + 1] f
        - C (∑ m ∈ Finset.range N, y m * f.coeff m) := by
  have key : ∀ m, (X - C a) * (C (y m) * divX^[m + 1] f)
      = C (y m) * divX^[m] f - C (y m * f.coeff m) - C (a * y m) * divX^[m + 1] f := by
    intro m
    have h := lap_X_mul_divX_iter f m
    calc (X - C a) * (C (y m) * divX^[m + 1] f)
        = C (y m) * (X * divX^[m + 1] f) - C a * C (y m) * divX^[m + 1] f := by ring
      _ = _ := by rw [h, C_mul, C_mul]; ring
  have hshift : ∑ m ∈ Finset.range N, C (y m) * divX^[m] f
      = C (y 0) * f + ∑ m ∈ Finset.range N, C (y (m + 1)) * divX^[m + 1] f := by
    have h1 := Finset.sum_range_succ (fun m => C (y m) * divX^[m] f) N
    have h2 := Finset.sum_range_succ' (fun m => C (y m) * divX^[m] f) N
    simp only [hN, mul_zero, add_zero, Function.iterate_zero_apply] at h1 h2
    rw [← h1, h2, add_comm]
  rw [Finset.mul_sum, Finset.sum_congr rfl (fun m _ => key m), Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, hshift, map_sum]
  simp only [C_sub, sub_mul, Finset.sum_sub_distrib]
  ring

noncomputable def lap_Q (a : ℂ) (f : ℂ[X]) (N p : ℕ) : ℂ[X] :=
  ∑ m ∈ Finset.range N, C ((m.choose p : ℂ) * a ^ (m - p)) * divX^[m + 1] f

theorem lap_choose_rec (a : ℂ) (m p : ℕ) :
    ((m + 1).choose (p + 1) : ℂ) * a ^ (m + 1 - (p + 1))
        - a * ((m.choose (p + 1) : ℂ) * a ^ (m - (p + 1)))
      = (m.choose p : ℂ) * a ^ (m - p) := by
  rw [Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right]
  rcases lt_or_ge m (p + 1) with h | h
  · rw [Nat.choose_eq_zero_of_lt h]; simp
  · have : m - p = m - (p + 1) + 1 := by omega
    rw [this, pow_succ]; ring

theorem lap_base (a : ℂ) (f : ℂ[X]) (N : ℕ) (hN : divX^[N] f = 0) :
    ∃ c : ℂ, (X - C a) * lap_Q a f N 0 = f - C c := by
  have h := lap_general_step a f N hN (fun m => (m.choose 0 : ℂ) * a ^ (m - 0))
  have hz : ∀ m : ℕ, ((m + 1).choose 0 : ℂ) * a ^ (m + 1 - 0)
      - a * ((m.choose 0 : ℂ) * a ^ (m - 0)) = 0 := by
    intro m; simp [pow_succ]; ring
  simp only [hz, C_0, zero_mul, Finset.sum_const_zero, add_zero] at h
  refine ⟨∑ m ∈ Finset.range N, (m.choose 0 : ℂ) * a ^ (m - 0) * f.coeff m, ?_⟩
  unfold lap_Q
  rw [h]
  simp

theorem lap_step (a : ℂ) (f : ℂ[X]) (N : ℕ) (hN : divX^[N] f = 0) (p : ℕ) :
    ∃ c : ℂ, (X - C a) * lap_Q a f N (p + 1) = lap_Q a f N p - C c := by
  have h := lap_general_step a f N hN (fun m => (m.choose (p + 1) : ℂ) * a ^ (m - (p + 1)))
  simp only [lap_choose_rec, Nat.choose_zero_succ, Nat.cast_zero, zero_mul, C_0,
    zero_add] at h
  exact ⟨_, h⟩

theorem lap_main (a : ℂ) (f : ℂ[X]) (N : ℕ) (hN : divX^[N] f = 0) (p : ℕ) :
    ∃ R : ℂ[X], R.natDegree ≤ p ∧ (X - C a) ^ (p + 1) * lap_Q a f N p = f - R := by
  induction p with
  | zero =>
    obtain ⟨c, hc⟩ := lap_base a f N hN
    exact ⟨C c, by simp, by simpa using hc⟩
  | succ p ih =>
    obtain ⟨R, hR, hRe⟩ := ih
    obtain ⟨c, hc⟩ := lap_step a f N hN p
    refine ⟨R + C c * (X - C a) ^ (p + 1), ?_, ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le (hR.trans (Nat.le_succ p)) ?_)
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    · calc (X - C a) ^ (p + 1 + 1) * lap_Q a f N (p + 1)
          = (X - C a) ^ (p + 1) * ((X - C a) * lap_Q a f N (p + 1)) := by ring
        _ = (X - C a) ^ (p + 1) * (lap_Q a f N p - C c) := by rw [hc]
        _ = f - (R + C c * (X - C a) ^ (p + 1)) := by rw [mul_sub, hRe]; ring

theorem poly_laplace_identity (a : ℂ) (p M : ℕ) (f : ℂ[X]) (hdiv : (X - C a) ^ (p + 1) ∣ f)
    (hM : f.natDegree ≤ M) :
    (X - C a) ^ (p + 1) *
        ∑ m ∈ Finset.range M, C ((m.descFactorial p : ℂ) * a ^ (m - p)) * divX^[m + 1] f
      = C (p.factorial : ℂ) * f := by
  have hN : divX^[M + 1] f = 0 := lap_divX_iter_eq_zero f (M + 1) (by omega)
  obtain ⟨R, hR, hRe⟩ := lap_main a f (M + 1) hN p
  have hR0 : R = 0 := by
    have hdvd : (X - C a) ^ (p + 1) ∣ R := by
      have : R = f - (X - C a) ^ (p + 1) * lap_Q a f (M + 1) p := by rw [hRe]; ring
      rw [this]; exact dvd_sub hdiv (dvd_mul_right _ _)
    apply eq_zero_of_dvd_of_natDegree_lt hdvd
    rw [natDegree_pow, natDegree_X_sub_C]; omega
  rw [hR0, sub_zero] at hRe
  have hsum : ∑ m ∈ Finset.range M, C ((m.descFactorial p : ℂ) * a ^ (m - p)) * divX^[m + 1] f
      = C (p.factorial : ℂ) * lap_Q a f (M + 1) p := by
    unfold lap_Q
    rw [Finset.sum_range_succ, hN, mul_zero, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, C_mul, C_mul, C_mul]
    ring
  rw [hsum, mul_left_comm, hRe]

end Singmaster
