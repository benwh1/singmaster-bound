module

public import Mathlib

@[expose] public section

/-!
# Lemma 5.1: bounds for `χ_m / χ`

`χ(w) = ∏_{j ≤ k} (w - jT)^{ν_j}` has degree `ν = ∑ ν_j`, and `χ_m = divX^[m+1] χ`.

* On `|w| = ϱ` with `ϱ ≥ 2kT`: `|χ_m(w)/χ(w)| ≤ 3^ν / ϱ^{m+1}` (`chiPoly_bound_big`).
* On `|w - jT| = T/2`: `|χ_m(w)/χ(w)| ≤ 2 ((k+1) 2^{4k+2})^{ν_max} (2/T)^{m+1}`
  (`chiPoly_bound_small`).
-/

open Polynomial

namespace Singmaster

/-- `χ(X) = ∏_{j ≤ k} (X - jT)^{n_j}`. -/
noncomputable def chiPoly (k : ℕ) (T : ℝ) (n : Fin (k + 1) → ℕ) : ℂ[X] :=
  ∏ j : Fin (k + 1), (X - C (((j : ℕ) : ℂ) * (T : ℂ))) ^ (n j)

/-! ### Helpers -/

theorem chi_coeff_iterate_divX (p : ℂ[X]) (r i : ℕ) :
    (divX^[r] p).coeff i = p.coeff (i + r) := by
  induction r generalizing i with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', coeff_divX, ih]
    congr 1; omega

theorem chi_natDegree_iterate_divX_le (p : ℂ[X]) (r : ℕ) :
    (divX^[r] p).natDegree ≤ p.natDegree := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact natDegree_divX_le.trans ih

theorem chi_dom_mul {p₁ p₂ : ℂ[X]} {q₁ q₂ : ℝ[X]}
    (h₁ : ∀ l, ‖p₁.coeff l‖ ≤ q₁.coeff l) (h₂ : ∀ l, ‖p₂.coeff l‖ ≤ q₂.coeff l) :
    ∀ l, ‖(p₁ * p₂).coeff l‖ ≤ (q₁ * q₂).coeff l := by
  intro l
  rw [coeff_mul, coeff_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (h₁ _) (h₂ _) (norm_nonneg _) ((norm_nonneg _).trans (h₁ _))

theorem chi_dom_one : ∀ l, ‖(1 : ℂ[X]).coeff l‖ ≤ (1 : ℝ[X]).coeff l := by
  intro l
  rw [coeff_one, coeff_one]
  split_ifs <;> simp

theorem chi_dom_pow {p : ℂ[X]} {q : ℝ[X]} (h : ∀ l, ‖p.coeff l‖ ≤ q.coeff l) (e : ℕ) :
    ∀ l, ‖(p ^ e).coeff l‖ ≤ (q ^ e).coeff l := by
  induction e with
  | zero => simpa using chi_dom_one
  | succ e ih => rw [pow_succ, pow_succ]; exact chi_dom_mul ih h

theorem chi_dom_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (p : ι → ℂ[X]) (q : ι → ℝ[X])
    (h : ∀ i, ∀ l, ‖(p i).coeff l‖ ≤ (q i).coeff l) :
    ∀ l, ‖(∏ i ∈ s, p i).coeff l‖ ≤ (∏ i ∈ s, q i).coeff l := by
  induction s using Finset.induction_on with
  | empty => simpa using chi_dom_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact chi_dom_mul (h a) ih

theorem chi_dom_linear (a : ℂ) (b : ℝ) (h : ‖a‖ ≤ b) :
    ∀ l, ‖(X - C a).coeff l‖ ≤ (X + C b).coeff l := by
  intro l
  rcases l with _ | _ | l
  · simpa [coeff_X, coeff_C] using h
  · simp [coeff_X]
  · simp [coeff_X]

theorem chi_key {p : ℂ[X]} {q : ℝ[X]} (h : ∀ l, ‖p.coeff l‖ ≤ q.coeff l) (w : ℂ) (r : ℕ) :
    ‖(divX^[r] p).eval w‖ * ‖w‖ ^ r ≤ q.eval ‖w‖ ∧
    ‖(divX^[r] p).eval w‖ * ‖w‖ ^ r ≤ ‖p.eval w‖ + q.eval ‖w‖ := by
  set D := p.natDegree + q.natDegree + 1 with hD
  set x := ‖w‖ with hx
  have hx0 : 0 ≤ x := norm_nonneg _
  have hq0 : ∀ l, 0 ≤ q.coeff l := fun l => (norm_nonneg _).trans (h l)
  have hf0 : ∀ l, 0 ≤ q.coeff l * x ^ l := fun l => mul_nonneg (hq0 l) (pow_nonneg hx0 _)
  have hqeval : q.eval x = ∑ l ∈ Finset.range (r + D), q.coeff l * x ^ l :=
    eval_eq_sum_range' (by omega) x
  have hpeval : p.eval w = ∑ l ∈ Finset.range (r + D), p.coeff l * w ^ l :=
    eval_eq_sum_range' (by omega) w
  have hmeval : (divX^[r] p).eval w = ∑ i ∈ Finset.range D, p.coeff (r + i) * w ^ i := by
    rw [eval_eq_sum_range' (n := D) ((chi_natDegree_iterate_divX_le p r).trans_lt (by omega)) w]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [chi_coeff_iterate_divX, add_comm]
  have hsplit := Finset.sum_range_add (fun l => q.coeff l * x ^ l) r D
  have hlo0 : 0 ≤ ∑ l ∈ Finset.range r, q.coeff l * x ^ l := Finset.sum_nonneg fun l _ => hf0 l
  have hhi0 : 0 ≤ ∑ i ∈ Finset.range D, q.coeff (r + i) * x ^ (r + i) :=
    Finset.sum_nonneg fun l _ => hf0 _
  constructor
  · have hhi : ‖(divX^[r] p).eval w‖ * x ^ r ≤
        ∑ i ∈ Finset.range D, q.coeff (r + i) * x ^ (r + i) := by
      rw [hmeval]
      refine (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hx0 _)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, norm_pow, pow_add, mul_comm (x ^ r) (x ^ i), ← mul_assoc]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (h _) (pow_nonneg hx0 _)) (pow_nonneg hx0 _)
    rw [hqeval, hsplit]
    linarith
  · have hdecomp : p.eval w = ∑ l ∈ Finset.range r, p.coeff l * w ^ l +
        w ^ r * (divX^[r] p).eval w := by
      rw [hpeval, Finset.sum_range_add, hmeval, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [pow_add]; ring
    have hlow : ‖∑ l ∈ Finset.range r, p.coeff l * w ^ l‖ ≤
        ∑ l ∈ Finset.range r, q.coeff l * x ^ l := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_right (h _) (pow_nonneg hx0 _)
    have heq : ‖(divX^[r] p).eval w‖ * x ^ r =
        ‖p.eval w - ∑ l ∈ Finset.range r, p.coeff l * w ^ l‖ := by
      rw [hdecomp, add_sub_cancel_left, norm_mul, norm_pow, mul_comm]
    rw [heq, hqeval, hsplit]
    have := norm_sub_le (p.eval w) (∑ l ∈ Finset.range r, p.coeff l * w ^ l)
    linarith

/-- The comparison polynomial `χ⁺ = ∏ (X + jT)^{n_j}`. -/
noncomputable def chiPlus (k : ℕ) (T : ℝ) (n : Fin (k + 1) → ℕ) : ℝ[X] :=
  ∏ j : Fin (k + 1), (X + C (((j : ℕ) : ℝ) * T)) ^ (n j)

theorem chi_dom {k : ℕ} {T : ℝ} (hT : 0 ≤ T) (n : Fin (k + 1) → ℕ) :
    ∀ l, ‖(chiPoly k T n).coeff l‖ ≤ (chiPlus k T n).coeff l :=
  chi_dom_prod _ _ _ fun j => chi_dom_pow (chi_dom_linear _ _ (by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hT])) _

theorem chiPlus_eval (k : ℕ) (T : ℝ) (n : Fin (k + 1) → ℕ) (x : ℝ) :
    (chiPlus k T n).eval x = ∏ j : Fin (k + 1), (x + ((j : ℕ) : ℝ) * T) ^ (n j) := by
  simp [chiPlus, eval_prod]

theorem chi_eval_norm (k : ℕ) (T : ℝ) (n : Fin (k + 1) → ℕ) (w : ℂ) :
    ‖(chiPoly k T n).eval w‖ = ∏ j : Fin (k + 1), ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ ^ (n j) := by
  simp [chiPoly, eval_prod, norm_prod]

theorem chi_norm_natCast_mul {T : ℝ} (hT : 0 ≤ T) (j : ℕ) :
    ‖(j : ℂ) * (T : ℂ)‖ = (j : ℝ) * T := by
  rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_of_nonneg hT]

open scoped Nat in
theorem chi_prod_shift (j n : ℕ) : j ! * ∏ i ∈ Finset.range n, (i + j + 1) = (n + j)! := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ← mul_assoc, ih, show n + 1 + j = (n + j) + 1 by ring,
      Nat.factorial_succ]
    ring

open scoped Nat in
theorem chi_prod_dist (j e : ℕ) :
    ∏ i ∈ Finset.range (j + e + 1), max (i - j + (j - i)) 1 = j ! * e ! := by
  rw [show j + e + 1 = j + (e + 1) by ring, Finset.prod_range_add, Finset.prod_range_succ']
  have h1 : ∏ x ∈ Finset.range j, max (x - j + (j - x)) 1 = j ! := by
    rw [← Finset.prod_range_reflect (fun x => max (x - j + (j - x)) 1) j,
      ← Finset.prod_range_add_one_eq_factorial]
    refine Finset.prod_congr rfl fun x hx => ?_
    rw [Finset.mem_range] at hx
    rw [max_eq_left (by omega)]; omega
  have h2 : ∏ x ∈ Finset.range e, max (j + (x + 1) - j + (j - (j + (x + 1)))) 1 = e ! := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [max_eq_left (by omega)]; omega
  rw [h1, h2]
  simp

open scoped Nat in
theorem chi_nat_ineq (k j : ℕ) (hj : j ≤ k) :
    ∏ i : Fin (k + 1), ((i : ℕ) + j + 1) ≤
      (k + 1) * 2 ^ (3 * k + 1) * ∏ i : Fin (k + 1), max ((i : ℕ) - j + (j - (i : ℕ))) 1 := by
  rw [Fin.prod_univ_eq_prod_range (fun i => i + j + 1),
    Fin.prod_univ_eq_prod_range (fun i => max (i - j + (j - i)) 1)]
  obtain ⟨e, rfl⟩ : ∃ e, k = j + e := ⟨k - j, by omega⟩
  rw [chi_prod_dist]
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos j)
  rw [chi_prod_shift]
  have hc1 := Nat.add_choose_mul_factorial_mul_factorial (j + e + 1) j
  have hc2 := Nat.choose_mul_factorial_mul_factorial (show j ≤ j + e by omega)
  rw [show j + e - j = e by omega] at hc2
  have hb1 := Nat.choose_le_two_pow (j + e + 1 + j) j
  have hb2 := Nat.choose_le_two_pow (j + e) j
  have hC : (j + e + 1 + j).choose j * (j + e).choose j ≤ 2 ^ (3 * (j + e) + 1) :=
    calc (j + e + 1 + j).choose j * (j + e).choose j ≤ 2 ^ (j + e + 1 + j) * 2 ^ (j + e) :=
          Nat.mul_le_mul hb1 hb2
      _ = 2 ^ (3 * j + 2 * e + 1) := by rw [← pow_add]; ring_nf
      _ ≤ 2 ^ (3 * (j + e) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [← hc1, Nat.factorial_succ (j + e), ← hc2]
  calc (j + e + 1 + j).choose j * ((j + e + 1) * ((j + e).choose j * j ! * e !)) * j !
      = ((j + e + 1 + j).choose j * (j + e).choose j) * ((j + e + 1) * j ! * e ! * j !) := by ring
    _ ≤ 2 ^ (3 * (j + e) + 1) * ((j + e + 1) * j ! * e ! * j !) := Nat.mul_le_mul_right _ hC
    _ = j ! * ((j + e + 1) * 2 ^ (3 * (j + e) + 1) * (j ! * e !)) := by ring

theorem chi_small_dist {T : ℝ} (hT : 0 < T) (j : ℕ) {w : ℂ}
    (hw : ‖w - (j : ℂ) * (T : ℂ)‖ = T / 2) (i : ℕ) :
    ((max (i - j + (j - i)) 1 : ℕ) : ℝ) * T / 2 ≤ ‖w - (i : ℂ) * (T : ℂ)‖ := by
  rcases eq_or_ne i j with rfl | hij
  · simp [hw]
  · have h1 : ‖((j : ℂ) - i) * T‖ ≤ ‖w - (i : ℂ) * T‖ + ‖w - (j : ℂ) * T‖ := by
      have := norm_sub_le (w - (i : ℂ) * T) (w - (j : ℂ) * T)
      convert this using 2; ring
    have h2 : ‖((j : ℂ) - i) * T‖ = |(j : ℝ) - i| * T := by
      rw [show ((j : ℂ) - i) * T = ((((j : ℝ) - i) * T : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos hT]
    have h3 : (((i - j + (j - i) : ℕ)) : ℝ) = |(j : ℝ) - i| := by
      rcases lt_or_gt_of_ne hij with h | h
      · have h' : (i : ℝ) < j := by exact_mod_cast h
        rw [show i - j + (j - i) = j - i by omega, Nat.cast_sub h.le, abs_of_pos (by linarith)]
      · have h' : (j : ℝ) < i := by exact_mod_cast h
        rw [show i - j + (j - i) = i - j by omega, Nat.cast_sub h.le, abs_of_neg (by linarith)]
        ring
    have h4 : 1 ≤ i - j + (j - i) := by omega
    rw [max_eq_left h4, h3]
    have h5 : (1 : ℝ) ≤ |(j : ℝ) - i| := by rw [← h3]; exact_mod_cast h4
    rw [h2, hw] at h1
    nlinarith

theorem chi_small_ratio {T : ℝ} (hT : 0 < T) (j : ℕ) {w : ℂ}
    (hw : ‖w - (j : ℂ) * (T : ℂ)‖ = T / 2) (i : ℕ) :
    1 ≤ (‖w‖ + i * T) / ‖w - (i : ℂ) * (T : ℂ)‖ ∧
    (‖w‖ + i * T) / ‖w - (i : ℂ) * (T : ℂ)‖ ≤
      2 * ((i + j + 1 : ℕ) : ℝ) / ((max (i - j + (j - i)) 1 : ℕ) : ℝ) := by
  have hd := chi_small_dist hT j hw i
  set M : ℝ := ((max (i - j + (j - i)) 1 : ℕ) : ℝ) with hMdef
  have hM : (1 : ℝ) ≤ M := by rw [hMdef]; exact_mod_cast le_max_right _ _
  have hden : 0 < ‖w - (i : ℂ) * (T : ℂ)‖ := by nlinarith
  have hnormi := chi_norm_natCast_mul hT.le i
  have hnormj := chi_norm_natCast_mul hT.le j
  have hxup : ‖w‖ ≤ j * T + T / 2 := by
    have := norm_add_le (w - (j : ℂ) * T) ((j : ℂ) * T)
    rw [sub_add_cancel, hw, hnormj] at this; linarith
  constructor
  · rw [one_le_div hden]
    have := norm_sub_le w ((i : ℂ) * T)
    rw [hnormi] at this; linarith
  · rw [div_le_div_iff₀ hden (by linarith)]
    push_cast
    have : ‖w‖ + i * T ≤ (i + j + 1) * T := by linarith
    calc (‖w‖ + i * T) * M ≤ ((i + j + 1) * T) * M := mul_le_mul_of_nonneg_right this (by linarith)
      _ = (i + j + 1) * (M * T) := by ring
      _ ≤ (i + j + 1) * (2 * ‖w - (i : ℂ) * (T : ℂ)‖) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = _ := by ring

theorem chiPoly_bound_big {k : ℕ} {T ϱ : ℝ} (hT : 0 ≤ T) (n : Fin (k + 1) → ℕ)
    (hϱ : 2 * k * T ≤ ϱ) (hϱ0 : 0 < ϱ) {w : ℂ} (hw : ‖w‖ = ϱ) (m : ℕ) :
    ‖(divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w‖ ≤
      3 ^ (∑ j, n j) / ϱ ^ (m + 1) := by
  have hfac : ∀ j : Fin (k + 1), ϱ / 2 ≤ ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ ∧
      ϱ + ((j : ℕ) : ℝ) * T ≤ 3 * ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ := by
    intro j
    have hj : ((j : ℕ) : ℝ) * T ≤ k * T :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.lt_succ_iff.mp j.isLt) hT
    have h1 := norm_sub_norm_le w (((j : ℕ) : ℂ) * (T : ℂ))
    rw [chi_norm_natCast_mul hT, hw] at h1
    constructor <;> linarith
  have hpos : 0 < ‖(chiPoly k T n).eval w‖ := by
    rw [chi_eval_norm]
    exact Finset.prod_pos fun j _ => pow_pos (by linarith [(hfac j).1]) _
  have hkey := (chi_key (chi_dom hT n) w (m + 1)).1
  rw [chiPlus_eval, hw] at hkey
  have hbound : ∏ j : Fin (k + 1), (ϱ + ((j : ℕ) : ℝ) * T) ^ (n j) ≤
      3 ^ (∑ j, n j) * ‖(chiPoly k T n).eval w‖ := by
    rw [chi_eval_norm, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun j _ => pow_nonneg ?_ _) fun j _ => ?_
    · exact add_nonneg hϱ0.le (mul_nonneg (Nat.cast_nonneg _) hT)
    · rw [← mul_pow]
      exact pow_le_pow_left₀ (add_nonneg hϱ0.le (mul_nonneg (Nat.cast_nonneg _) hT)) (hfac j).2 _
  rw [norm_div, div_le_div_iff₀ hpos (pow_pos hϱ0 _)]
  linarith

theorem chiPoly_bound_small {k : ℕ} {T : ℝ} (hT : 0 < T) (n : Fin (k + 1) → ℕ) (j : Fin (k + 1))
    {w : ℂ} (hw : ‖w - ((j : ℕ) : ℂ) * (T : ℂ)‖ = T / 2) (m : ℕ) :
    ‖(divX^[m + 1] (chiPoly k T n)).eval w / (chiPoly k T n).eval w‖ ≤
      2 * (((k : ℝ) + 1) * 2 ^ (4 * k + 2)) ^ (Finset.univ.sup n) * (2 / T) ^ (m + 1) := by
  have hjk : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.isLt
  set Bc : ℝ := ((k : ℝ) + 1) * 2 ^ (4 * k + 2) with hBc
  set Q : ℝ := Bc ^ (Finset.univ.sup n) with hQdef
  set r : Fin (k + 1) → ℝ := fun i =>
    (‖w‖ + ((i : ℕ) : ℝ) * T) / ‖w - ((i : ℕ) : ℂ) * (T : ℂ)‖ with hrdef
  have hr1 : ∀ i, 1 ≤ r i := fun i => (chi_small_ratio hT (j : ℕ) hw (i : ℕ)).1
  have hrle : ∀ i, r i ≤ 2 * (((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) /
      ((max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 : ℕ) : ℝ) :=
    fun i => (chi_small_ratio hT (j : ℕ) hw (i : ℕ)).2
  -- the product of the ratios
  have hBpos : 0 < ∏ i : Fin (k + 1), max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 :=
    Finset.prod_pos fun i _ => lt_of_lt_of_le one_pos (le_max_right _ _)
  have hnat : ((∏ i : Fin (k + 1), ((i : ℕ) + (j : ℕ) + 1) : ℕ) : ℝ) ≤
      ((k : ℝ) + 1) * 2 ^ (3 * k + 1) *
        ((∏ i : Fin (k + 1), max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 : ℕ) : ℝ) := by
    exact_mod_cast chi_nat_ineq k j hjk
  have hprod : ∏ i, r i ≤ Bc := by
    calc ∏ i, r i ≤ ∏ i : Fin (k + 1), 2 * (((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ) /
          ((max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 : ℕ) : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => zero_le_one.trans (hr1 i)) fun i _ => hrle i
      _ = 2 ^ (k + 1) * ((∏ i : Fin (k + 1), ((i : ℕ) + (j : ℕ) + 1) : ℕ) : ℝ) /
          ((∏ i : Fin (k + 1), max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 : ℕ) : ℝ) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
            Finset.card_univ, Fintype.card_fin, Nat.cast_prod, Nat.cast_prod]
      _ ≤ Bc := by
          rw [div_le_iff₀ (by exact_mod_cast hBpos), hBc]
          calc (2 : ℝ) ^ (k + 1) * ((∏ i : Fin (k + 1), ((i : ℕ) + (j : ℕ) + 1) : ℕ) : ℝ)
              ≤ 2 ^ (k + 1) * (((k : ℝ) + 1) * 2 ^ (3 * k + 1) *
                ((∏ i : Fin (k + 1), max ((i : ℕ) - (j : ℕ) + ((j : ℕ) - (i : ℕ))) 1 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left hnat (by positivity)
            _ = _ := by ring
  have hQ : ∏ i, r i ^ (n i) ≤ Q := by
    calc ∏ i, r i ^ (n i) ≤ ∏ i, r i ^ (Finset.univ.sup n) :=
          Finset.prod_le_prod₀ (fun i _ => pow_nonneg (zero_le_one.trans (hr1 i)) _)
            fun i _ => pow_le_pow_right₀ (hr1 i) (Finset.le_sup (Finset.mem_univ i))
      _ = (∏ i, r i) ^ (Finset.univ.sup n) := Finset.prod_pow _ _ _
      _ ≤ Q := pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => zero_le_one.trans (hr1 i)) hprod _
  have hQ1 : 1 ≤ Q := by
    apply one_le_pow₀
    have : (1 : ℝ) ≤ 2 ^ (4 * k + 2) := one_le_pow₀ (by norm_num)
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    nlinarith
  -- the denominator
  have hden : ∀ i : ℕ, T / 2 ≤ ‖w - (i : ℂ) * (T : ℂ)‖ := by
    intro i
    have h := chi_small_dist hT (j : ℕ) hw i
    have hM : (1 : ℝ) ≤ ((max (i - (j : ℕ) + ((j : ℕ) - i)) 1 : ℕ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    nlinarith
  have hpos : 0 < ‖(chiPoly k T n).eval w‖ := by
    rw [chi_eval_norm]
    exact Finset.prod_pos fun i _ => pow_pos (by linarith [hden (i : ℕ)]) _
  have hxlow : T / 2 ≤ ‖w‖ := by simpa using hden 0
  have hratio : (chiPlus k T n).eval ‖w‖ = (∏ i, r i ^ (n i)) * ‖(chiPoly k T n).eval w‖ := by
    rw [chiPlus_eval, chi_eval_norm, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hrdef, div_pow, div_mul_cancel₀]
    exact pow_ne_zero _ (by linarith [hden (i : ℕ)])
  have hkey := (chi_key (chi_dom hT.le n) w (m + 1)).2
  have hplus : (chiPlus k T n).eval ‖w‖ ≤ Q * ‖(chiPoly k T n).eval w‖ := by
    rw [hratio]; exact mul_le_mul_of_nonneg_right hQ hpos.le
  have h2QP : ‖(divX^[m + 1] (chiPoly k T n)).eval w‖ * ‖w‖ ^ (m + 1) ≤
      2 * Q * ‖(chiPoly k T n).eval w‖ := by
    have : ‖(chiPoly k T n).eval w‖ ≤ Q * ‖(chiPoly k T n).eval w‖ :=
      le_mul_of_one_le_left hpos.le hQ1
    linarith
  have hxpow : 1 ≤ (2 / T) ^ (m + 1) * ‖w‖ ^ (m + 1) := by
    rw [← mul_pow]
    apply one_le_pow₀
    rw [div_mul_eq_mul_div, le_div_iff₀ hT]
    linarith
  rw [norm_div, div_le_iff₀ hpos]
  calc ‖(divX^[m + 1] (chiPoly k T n)).eval w‖
      ≤ ‖(divX^[m + 1] (chiPoly k T n)).eval w‖ * ((2 / T) ^ (m + 1) * ‖w‖ ^ (m + 1)) :=
        le_mul_of_one_le_right (norm_nonneg _) hxpow
    _ = (‖(divX^[m + 1] (chiPoly k T n)).eval w‖ * ‖w‖ ^ (m + 1)) * (2 / T) ^ (m + 1) := by ring
    _ ≤ (2 * Q * ‖(chiPoly k T n).eval w‖) * (2 / T) ^ (m + 1) :=
        mul_le_mul_of_nonneg_right h2QP (by positivity)
    _ = 2 * Q * (2 / T) ^ (m + 1) * ‖(chiPoly k T n).eval w‖ := by ring

end Singmaster
