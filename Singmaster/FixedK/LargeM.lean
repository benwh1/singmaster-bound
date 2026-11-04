module

public import Singmaster.Basic

@[expose] public section

/-!
# Lemma 7.1: solutions with large `m`

With `L = log t`, every `(n, m) ∈ Sol(t)` with `m ≥ L/(log L)^{7/5}` lies in the region
`exp((log n)^{2/3 + 1/30}) ≤ m ≤ n/2` of Theorem 2.3 once `t` is large, so there are at most
two of them (`card_halfSolutions_large_le`).
-/

open Real Filter

namespace Singmaster

/-- `n^m ≤ m^m · C(n, m)`, i.e. `C(n, m) ≥ (n/m)^m`. -/
lemma lm_pow_le_choose {n m : ℕ} (h : m ≤ n) : n ^ m ≤ m ^ m * n.choose m := by
  have key : ∏ i ∈ Finset.range m, (n * (m - i)) ≤ ∏ i ∈ Finset.range m, (m * (n - i)) := by
    apply Finset.prod_le_prod
    intro i _
    rw [Nat.mul_sub, Nat.mul_sub, Nat.mul_comm n m]
    exact Nat.sub_le_sub_left (Nat.mul_le_mul_right i h) (m * n)
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
    Finset.card_range, ← Nat.descFactorial_eq_prod_range, ← Nat.descFactorial_eq_prod_range,
    Nat.descFactorial_self, Nat.descFactorial_eq_factorial_mul_choose] at key
  have hf := m.factorial_pos
  have : n ^ m * m.factorial ≤ (m ^ m * n.choose m) * m.factorial := by
    calc n ^ m * m.factorial ≤ m ^ m * (m.factorial * n.choose m) := key
      _ = (m ^ m * n.choose m) * m.factorial := by ring
  exact Nat.le_of_mul_le_mul_right this hf

/-- The conditions on `y = log log t` that hold for large `y`. -/
lemma lm_eventually :
    ∀ᶠ y : ℝ in atTop, 1 ≤ y ∧ y + 1 ≤ y ^ ((7 : ℝ) / 5) ∧
      2 * y ^ ((49 : ℝ) / 50) + 7 / 5 * log y ≤ y := by
  have h1 : ∀ᶠ y : ℝ in atTop, 2 ≤ y ^ ((2 : ℝ) / 5) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 2
  have h2 : ∀ᶠ y : ℝ in atTop, 4 ≤ y ^ ((1 : ℝ) / 50) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 4
  have h3 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 4 by norm_num)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 1] with y h1 h2 h3 hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  rw [Real.norm_eq_abs, id, Real.norm_of_nonneg hy0] at h3
  have e1 : y ^ ((7 : ℝ) / 5) = y * y ^ ((2 : ℝ) / 5) := by
    rw [← Real.rpow_one_add' hy0 (by norm_num)]; norm_num
  have e2 : y = y ^ ((49 : ℝ) / 50) * y ^ ((1 : ℝ) / 50) := by
    rw [← Real.rpow_add' hy0 (by norm_num)]; norm_num
  have hp : 0 ≤ y ^ ((49 : ℝ) / 50) := by positivity
  refine ⟨hy, ?_, ?_⟩
  · rw [e1]; nlinarith
  · have : 4 * y ^ ((49 : ℝ) / 50) ≤ y := by
      calc 4 * y ^ ((49 : ℝ) / 50) ≤ y ^ ((49 : ℝ) / 50) * y ^ ((1 : ℝ) / 50) := by nlinarith
        _ = y := e2.symm
    have := le_abs_self (log y)
    linarith

/-- The real-variable core: with `y = log L`, a solution `(n, m)` of `C(n, m) = e^L` with
`2m ≤ n` and
`m ≥ L / y^{7/5}` has `exp((log n)^{7/10}) ≤ m`. The binomial input is `n^m ≤ m^m e^L`. -/
lemma lm_pointwise {L n m : ℝ} (hL0 : 0 ≤ L) (hy1 : 1 ≤ log L)
    (hyb : log L + 1 ≤ log L ^ ((7 : ℝ) / 5))
    (hyc : 2 * log L ^ ((49 : ℝ) / 50) + 7 / 5 * log (log L) ≤ log L)
    (hm1 : 1 ≤ m) (hmn : 2 * m ≤ n) (hbin : m * log n ≤ m * log m + L)
    (hm : L / log L ^ ((7 : ℝ) / 5) ≤ m) :
    exp (log n ^ ((7 : ℝ) / 10)) ≤ m := by
  set y := log L with hy
  have hL1 : 1 < L := (Real.log_pos_iff hL0).1 (by linarith)
  have hm0 : 0 < m := by linarith
  have hn0 : 0 < n := by linarith
  have hY : 0 < y ^ ((7 : ℝ) / 5) := by positivity
  -- `log n ≥ log 2 + log m`
  have hlogn : log 2 + log m ≤ log n := by
    rw [← Real.log_mul (by norm_num) hm0.ne']
    exact Real.log_le_log (by positivity) hmn
  -- `m log 2 ≤ L`, so `m ≤ 2 L` and `log m ≤ log 2 + y`
  have hm2 : m * log 2 ≤ L := by nlinarith
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hm2L : m ≤ 2 * L := by nlinarith
  have hlogm : log m ≤ log 2 + y := by
    rw [hy, ← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log hm0 hm2L
  -- `log n - log m ≤ L / m ≤ y^{7/5}`
  have h1 : log n - log m ≤ L / m := by
    rw [le_div_iff₀ hm0]; nlinarith
  have h2 : L / m ≤ y ^ ((7 : ℝ) / 5) := by
    rw [div_le_iff₀ hm0]
    rw [div_le_iff₀ hY] at hm
    linarith
  have hlogn2 : log n ≤ 2 * y ^ ((7 : ℝ) / 5) := by linarith
  have hlogn0 : 0 ≤ log n := Real.log_nonneg (by linarith)
  -- `(log n)^{7/10} ≤ 2 y^{49/50}`
  have h3 : log n ^ ((7 : ℝ) / 10) ≤ 2 * y ^ ((49 : ℝ) / 50) := by
    calc log n ^ ((7 : ℝ) / 10) ≤ (2 * y ^ ((7 : ℝ) / 5)) ^ ((7 : ℝ) / 10) :=
          Real.rpow_le_rpow hlogn0 hlogn2 (by norm_num)
      _ = 2 ^ ((7 : ℝ) / 10) * y ^ ((49 : ℝ) / 50) := by
          rw [Real.mul_rpow (by norm_num) hY.le, ← Real.rpow_mul (by linarith)]
          norm_num
      _ ≤ 2 * y ^ ((49 : ℝ) / 50) := by
          gcongr
          calc (2 : ℝ) ^ ((7 : ℝ) / 10) ≤ 2 ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := Real.rpow_one 2
  -- `log m ≥ y - (7/5) log y`
  have h4 : y - 7 / 5 * log y ≤ log m := by
    have := Real.log_le_log (by positivity) hm
    rw [Real.log_div (by linarith) hY.ne', Real.log_rpow (by linarith)] at this
    linarith
  calc exp (log n ^ ((7 : ℝ) / 10)) ≤ exp (log m) := Real.exp_le_exp.2 (by linarith)
    _ = m := Real.exp_log hm0

/-- An element `(n, m)` of `Sol(t)` with `m ≥ L / y^{7/5}` (`L = log t`, `y = log L`) lies in
the region `exp((log n)^{2/3 + 1/30}) ≤ m` of Theorem 2.3, provided `y` satisfies the conditions
of `lm_eventually`. -/
lemma lm_mem_region {t n m : ℕ} (ht : 2 ≤ t) (h : n.choose m = t) (hmn : 2 * m ≤ n)
    (hy1 : 1 ≤ log (log t)) (hyb : log (log t) + 1 ≤ log (log t) ^ ((7 : ℝ) / 5))
    (hyc : 2 * log (log t) ^ ((49 : ℝ) / 50) + 7 / 5 * log (log (log t)) ≤ log (log t))
    (hm : log t / log (log t) ^ ((7 : ℝ) / 5) ≤ m) :
    exp (log n ^ ((2 : ℝ) / 3 + 1 / 30)) ≤ m := by
  obtain ⟨hm1, hmn', -⟩ := bounds_of_choose_eq ht h
  have hpow := lm_pow_le_choose hmn'.le
  rw [h] at hpow
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hpowR : (n : ℝ) ^ m ≤ (m : ℝ) ^ m * t := by exact_mod_cast hpow
  have hbin : (m : ℝ) * log n ≤ m * log m + log t := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have := Real.log_le_log (by positivity) hpowR
    rwa [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at this
  rw [show (2 : ℝ) / 3 + 1 / 30 = 7 / 10 by norm_num]
  exact lm_pointwise (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ t))) hy1 hyb hyc hm1'
    (by exact_mod_cast hmn) hbin hm

/-- **Lemma 7.1.** If `log log t` is large, then at most two elements `(n, m)` of `Sol(t)` have
`m ≥ log t / (log log t)^{7/5}`. -/
theorem card_halfSolutions_large_le (hM : MRSTT) : ∃ Λ : ℝ, ∀ t : ℕ, Λ ≤ log (log t) →
    ((halfSolutions t).filter fun p => log t / log (log t) ^ ((7 : ℝ) / 5) ≤ p.2).card ≤ 2 := by
  obtain ⟨t₁, ht₁⟩ := hM (1 / 30) (by norm_num) (by norm_num)
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 lm_eventually
  refine ⟨max (max Λ₀ 1) (log (log ((max t₁ 2 : ℕ) : ℝ)) + 1), fun t hΛ => ?_⟩
  have hΛ₀' : Λ₀ ≤ log (log t) := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hΛ)
  have hΛ1 : 1 ≤ log (log t) := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hΛ)
  have hΛ2 : log (log ((max t₁ 2 : ℕ) : ℝ)) + 1 ≤ log (log t) := le_trans (le_max_right _ _) hΛ
  obtain ⟨hy1, hyb, hyc⟩ := hΛ₀ _ hΛ₀'
  have ht2 : 2 ≤ t := by
    by_contra hlt
    interval_cases t <;> simp at hΛ1 <;> linarith
  have htt₁ : t₁ ≤ t := by
    by_contra hlt
    have hle : t ≤ max t₁ 2 := by omega
    have hlog : 0 < log (t : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < t))
    have : log (log (t : ℝ)) ≤ log (log ((max t₁ 2 : ℕ) : ℝ)) :=
      Real.log_le_log hlog (Real.log_le_log (by positivity) (by exact_mod_cast hle))
    linarith
  have hfin : {p : ℕ × ℕ | p.1.choose p.2 = t ∧ exp (log p.1 ^ ((2 : ℝ) / 3 + 1 / 30)) ≤ p.2 ∧
      2 * p.2 ≤ p.1}.Finite :=
    (finite_setOf_choose_eq ht2).subset fun p hp => hp.1
  rw [← Set.ncard_coe_finset]
  refine le_trans (Set.ncard_le_ncard ?_ hfin) (ht₁ t htt₁)
  intro p hp
  rw [Finset.coe_filter, Set.mem_ofPred_eq, mem_halfSolutions ht2] at hp
  obtain ⟨⟨h, hmn⟩, hm⟩ := hp
  exact ⟨h, lm_mem_region ht2 h hmn hy1 hyb hyc hm, hmn⟩

end Singmaster
