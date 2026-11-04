module

public import Mathlib

@[expose] public section

/-!
# Proposition 6.1: the change of variable `u = 1/z`

If `F(1/u) = u⁻¹ ((1 - u)/2 + E/e)`, then for `h = ∑_{b ≤ k} A_b F^b` with `deg A_b ≤ d` we have
`u^{d+k} h(1/u) = ∑_{j ≤ k} Q_j(u) E^j`, where
`Q_j = e^{-j} ∑_{b ≥ j} C(b, j) u^{k-b} ((1-u)/2)^{b-j} Â_b` and `Â_b = u^d A_b(1/u)` is the
reflection of `A_b` (`cv_identity`, identity (6.1)). The `Q_j` (`cvP`) have degree at most
`d + k`, and they are not all zero if the `A_b` are not all zero.
-/

open Polynomial Complex

namespace Singmaster

/-- The polynomials `Q_j` of the change of variable. -/
noncomputable def cvP (k d : ℕ) (A : Fin (k + 1) → ℂ[X]) (j : Fin (k + 1)) : ℂ[X] :=
  ∑ b : Fin (k + 1), if (j : ℕ) ≤ b then
    (A b).reflect d * X ^ (k - (b : ℕ)) * C (((b : ℕ).choose j : ℕ) : ℂ) *
      (C (1 / 2 : ℂ) * (1 - X)) ^ ((b : ℕ) - j) * C (cexp (-((j : ℕ) : ℂ)))
  else 0

lemma cv_eval_reflect {f : ℂ[X]} {d : ℕ} (hf : f.natDegree ≤ d) {u : ℂ} (hu : u ≠ 0) :
    (f.reflect d).eval u = u ^ d * f.eval u⁻¹ := by
  let _ : Invertible u⁻¹ := invertibleOfNonzero (inv_ne_zero hu)
  have h := eval₂_reflect_mul_pow (RingHom.id ℂ) u⁻¹ d f hf
  simp only [invOf_eq_inv, inv_inv] at h
  rw [eval, eval, ← h, inv_pow, mul_left_comm, mul_inv_cancel₀ (pow_ne_zero _ hu), mul_one]

lemma cv_sum_range_eq_fin {M : Type*} [AddCommMonoid M] {k b : ℕ} (hb : b ≤ k) (f : ℕ → M) :
    ∑ j ∈ Finset.range (b + 1), f j = ∑ j : Fin (k + 1), if (j : ℕ) ≤ b then f j else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => if j ≤ b then f j else 0) (k + 1), ← Finset.sum_filter]
  congr 1
  ext j
  simp only [Finset.mem_range, Finset.mem_filter]
  omega

lemma cv_exp_neg_mul_pow (E : ℂ) (j : ℕ) :
    cexp (-(j : ℂ)) * E ^ j = (E / cexp 1) ^ j := by
  rw [div_pow, ← Complex.exp_nat_mul, mul_one, Complex.exp_neg, div_eq_mul_inv, mul_comm]

theorem cv_identity {k d : ℕ} (A : Fin (k + 1) → ℂ[X]) (hA : ∀ b, (A b).natDegree ≤ d)
    {u E Fu : ℂ} (hu : u ≠ 0) (hF : Fu = u⁻¹ * ((1 - u) / 2 + E / cexp 1)) :
    u ^ (d + k) * ∑ b : Fin (k + 1), (A b).eval u⁻¹ * Fu ^ (b : ℕ) =
      ∑ j : Fin (k + 1), (cvP k d A j).eval u * E ^ (j : ℕ) := by
  subst hF
  simp only [cvP, eval_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hb : (b : ℕ) ≤ k := Nat.lt_succ_iff.mp b.isLt
  have key : u ^ (d + k) * ((A b).eval u⁻¹ * (u⁻¹ * ((1 - u) / 2 + E / cexp 1)) ^ (b : ℕ)) =
      ((A b).reflect d).eval u * u ^ (k - b) * (E / cexp 1 + (1 - u) / 2) ^ (b : ℕ) := by
    rw [cv_eval_reflect (hA b) hu]
    have hp : u ^ (d + k) = u ^ d * u ^ (k - b) * u ^ (b : ℕ) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    rw [hp, mul_pow, add_comm (E / cexp 1)]
    have : u ^ (b : ℕ) * u⁻¹ ^ (b : ℕ) = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hu, one_pow]
    linear_combination (u ^ d * (A b).eval u⁻¹ * u ^ (k - b) * ((1 - u) / 2 + E / cexp 1) ^ (b : ℕ)) * this
  rw [key, add_pow, Finset.mul_sum, cv_sum_range_eq_fin hb]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · simp only [eval_mul, eval_pow, eval_C, eval_X, eval_sub, eval_one]
    rw [← cv_exp_neg_mul_pow]
    ring
  · simp

theorem cvP_natDegree_le {k d : ℕ} (A : Fin (k + 1) → ℂ[X]) (hA : ∀ b, (A b).natDegree ≤ d)
    (j : Fin (k + 1)) : (cvP k d A j).natDegree ≤ d + k := by
  refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
  split_ifs with hj
  · have hb : (b : ℕ) ≤ k := Nat.lt_succ_iff.mp b.isLt
    have h1 : ((A b).reflect d).natDegree ≤ d := natDegree_reflect_le.trans (max_le le_rfl (hA b))
    have h2 : (X ^ (k - (b : ℕ)) : ℂ[X]).natDegree ≤ k - b := natDegree_X_pow_le _
    have h3 : (C (1 / 2 : ℂ) * (1 - X)).natDegree ≤ 1 := by compute_degree
    have h4 := natDegree_pow_le_of_le ((b : ℕ) - j) h3
    refine (natDegree_mul_le_of_le (natDegree_mul_le_of_le (natDegree_mul_le_of_le
      (natDegree_mul_le_of_le h1 h2) (natDegree_C _).le) h4) (natDegree_C _).le).trans ?_
    omega
  · simp

theorem cvP_exists_ne_zero {k d : ℕ} (A : Fin (k + 1) → ℂ[X])
    (hne : ∃ b, A b ≠ 0) : ∃ j, cvP k d A j ≠ 0 := by
  classical
  have hS : (Finset.univ.filter (fun b => A b ≠ 0)).Nonempty := by
    obtain ⟨b, hb⟩ := hne
    exact ⟨b, by simpa using hb⟩
  set m := (Finset.univ.filter (fun b => A b ≠ 0)).max' hS with hm
  have hmA : A m ≠ 0 := by
    have := Finset.max'_mem _ hS
    rw [← hm] at this
    simpa using this
  have hlarge : ∀ b, m < b → A b = 0 := by
    intro b hb
    by_contra h
    have : b ≤ m := Finset.le_max' _ b (by simpa using h)
    exact absurd hb (not_lt.mpr this)
  refine ⟨m, ?_⟩
  unfold cvP
  rw [Finset.sum_eq_single m]
  · simp only [le_refl, ite_true, Nat.choose_self, Nat.sub_self, pow_zero, Nat.cast_one, map_one,
      mul_one]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ X_ne_zero)) ?_
    · rwa [Ne, reflect_eq_zero_iff]
    · rw [Ne, C_eq_zero]
      exact Complex.exp_ne_zero _
  · intro b _ hbm
    split_ifs with h
    · have : m < b := lt_of_le_of_ne (Fin.le_iff_val_le_val.mpr h) (Ne.symm hbm)
      rw [hlarge b this, reflect_zero]
      simp
    · rfl
  · intro h
    exact absurd (Finset.mem_univ m) h

end Singmaster
