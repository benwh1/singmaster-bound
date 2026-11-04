module

public import Singmaster.FixedK.LargeM
public import Singmaster.FixedK.Window

@[expose] public section

/-!
# Theorem 1.3

This is the proof of Theorem 1.3 in Section 7. With the notation of `Singmaster.FixedK.Window`:

* `ct_block`: inequality (7.3), a block `[M, 2M]` with `M₀ ≤ M ≤ M₁` contains at most
  `6 e^{2a₀+1} L M^{-α}` elements of `Sol(t)`;
* `ct_middle`: summing over dyadic blocks, at most `21 e^{2a₀+1} L^θ` of them have
  `M₀ < m < M₁`;
* `ct_final`: adding the at most `M₀` elements with `m ≤ M₀` and the at most `2` with
  `m ≥ M₁` (Lemma 7.1), and using (1.2), gives `N(t) ≤ 50 e^{2a₀+1} L^θ`;
* `fixedKBound_of_mrstt`: Theorem 1.3.

`WindowBound t k` is the conclusion of Lemma 7.2 for all admissible `M` and `x₀`.
-/

open Real Filter Polynomial Topology

namespace Singmaster

/-- `2 ≤ r_M ≤ M` for every block `[M, 2M]` with `M ≥ M₀`. -/
lemma ct_rad_bounds {t k : ℕ} {X M : ℝ} (hk : 1 ≤ k)
    (hL : 0 < log (t : ℝ)) (hgood : GoodLam X (log (log t)))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5))
    (hM0 : log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ M) :
    2 ≤ rad k M ∧ rad k M ≤ M := by
  obtain ⟨hlam9, -, -, -⟩ := hgood
  set L := log (t : ℝ) with hLdef
  set lam := log L with hlamdef
  have hlam1 : 1 ≤ lam := by linarith
  have hL1 : 1 ≤ L := by rw [← exp_log hL]; exact one_le_exp (by linarith)
  obtain ⟨-, ha160⟩ := ct_standing hk (by linarith) hst
  have ha := a₀_ge k
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have he : (1 : ℝ) / 2 ≤ ((k : ℝ) + 1) / (2 * k + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hM0' : exp (lam / 2) ≤ M := by
    calc exp (lam / 2) = L ^ ((1 : ℝ) / 2) := by rw [rpow_def_of_pos hL]; congr 1; ring
      _ ≤ L ^ (((k : ℝ) + 1) / (2 * k + 1)) := rpow_le_rpow_of_exponent_le hL1 he
      _ ≤ M := hM0
  have hlam25 : lam ^ ((2 : ℝ) / 5) ≤ lam := by
    calc lam ^ ((2 : ℝ) / 5) ≤ lam ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hlam1 (by norm_num)
      _ = lam := rpow_one _
  have hl2 := Real.log_two_lt_d9
  have hl8 : log (8 : ℝ) = 3 * log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  -- `M/2 ≥ 4 e^{4a+2}`
  have h8 : 8 * exp (4 * a₀ k + 2) ≤ exp (lam / 2) := by
    rw [show (8 : ℝ) = exp (log 8) from (exp_log (by norm_num)).symm, ← exp_add]
    apply exp_le_exp.2
    linarith
  have hsq : (2 * exp (2 * a₀ k + 1)) ^ 2 ≤ M / 2 := by
    have : (2 * exp (2 * a₀ k + 1)) ^ 2 = 4 * exp (4 * a₀ k + 2) := by
      rw [mul_pow, sq (exp _), ← exp_add]; ring_nf
    rw [this]; linarith
  have hα1 : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have hαh : (1 : ℝ) / 2 ≤ (k : ℝ) / (k + 1) := by
    rw [div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hexp_lam : lam / 2 + 1 ≤ exp (lam / 2) := by
    have := add_one_le_exp (lam / 2); linarith
  have hM2' : 1 ≤ M / 2 := by linarith
  have hsqrt : 2 * exp (2 * a₀ k + 1) ≤ (M / 2) ^ ((k : ℝ) / (k + 1)) := by
    calc 2 * exp (2 * a₀ k + 1) ≤ √(M / 2) := Real.le_sqrt_of_sq_le hsq
      _ = (M / 2) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      _ ≤ (M / 2) ^ ((k : ℝ) / (k + 1)) := rpow_le_rpow_of_exponent_le hM2' hαh
  have hE : exp (2 * a₀ k + 1) * exp (-(2 * a₀ k) - 1) = 1 := by
    rw [← exp_add]; ring_nf; exact exp_zero
  constructor
  · unfold rad
    have := mul_le_mul_of_nonneg_right hsqrt (exp_pos (-(2 * a₀ k) - 1)).le
    nlinarith
  · unfold rad
    have h1 : (M / 2) ^ ((k : ℝ) / (k + 1)) ≤ M / 2 := by
      calc (M / 2) ^ ((k : ℝ) / (k + 1)) ≤ (M / 2) ^ (1 : ℝ) :=
            rpow_le_rpow_of_exponent_le hM2' hα1
        _ = M / 2 := rpow_one _
    have h2 : exp (-(2 * a₀ k) - 1) ≤ 1 := by
      rw [exp_le_one_iff]; linarith
    have h3 : 0 ≤ (M / 2) ^ ((k : ℝ) / (k + 1)) := by positivity
    nlinarith

/-- The conclusion of Lemma 7.2: every window of radius `r_M` around an integer `x₀ ∈ [M, 2M]`,
with `M₀ ≤ M ≤ M₁`, contains at most `L/M` elements of `Sol(t)`. -/
def WindowBound (t k : ℕ) : Prop :=
  ∀ (x₀ : ℕ) (M : ℝ), log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ M →
    M ≤ log (t : ℝ) / log (log t) ^ ((7 : ℝ) / 5) → M ≤ x₀ → (x₀ : ℝ) ≤ 2 * M →
    (((halfSolutions t).filter fun p => |(p.2 : ℝ) - x₀| ≤ rad k M).card : ℝ) ≤ log t / M

set_option maxHeartbeats 2000000 in
/-- **Inequality (7.3).** For `M₀ ≤ M ≤ M₁` the block `[M, 2M]` contains at most
`6 e^{2a₀+1} L M^{-k/(k+1)}` elements of `Sol(t)`. -/
theorem ct_block {t k : ℕ} {X M : ℝ} (hk : 1 ≤ k) (hW : WindowBound t k)
    (hL : 0 < log (t : ℝ)) (hgood : GoodLam X (log (log t)))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5))
    (hM0 : log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ M)
    (hM1 : M ≤ log (t : ℝ) / log (log t) ^ ((7 : ℝ) / 5)) :
    (((halfSolutions t).filter fun p => M ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * M).card : ℝ) ≤
      6 * exp (2 * a₀ k + 1) * log t * M ^ (-((k : ℝ) / (k + 1))) := by
  classical
  obtain ⟨hr2, hrM⟩ := ct_rad_bounds hk hL hgood hst hM0
  have hM2 : 2 ≤ M := by linarith
  have hMpos : 0 < M := by linarith
  have hrpos : 0 < rad k M := by linarith
  obtain ⟨s, hs⟩ : ∃ s, s = ⌊rad k M⌋₊ := ⟨_, rfl⟩
  have hs2 : 2 ≤ s := by rw [hs]; exact Nat.le_floor (by exact_mod_cast hr2)
  have hsr : (s : ℝ) ≤ rad k M := by rw [hs]; exact Nat.floor_le hrpos.le
  have hsr' : rad k M < s + 1 := by rw [hs]; exact Nat.lt_floor_add_one _
  have hspos : (0 : ℝ) < s := by have : (2 : ℝ) ≤ s := by exact_mod_cast hs2
                                 linarith
  obtain ⟨c, hc⟩ : ∃ c, c = ⌈M⌉₊ := ⟨_, rfl⟩
  have hc1 : M ≤ c := by rw [hc]; exact Nat.le_ceil M
  set B := (halfSolutions t).filter fun p => M ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * M with hB
  have hcp : ∀ p ∈ B, c ≤ p.2 := fun p hp => by
    rw [hc]; exact Nat.ceil_le.2 (Finset.mem_filter.1 hp).2.1
  obtain ⟨I, hI⟩ : ∃ I, I = ⌊M / s⌋₊ + 1 := ⟨_, rfl⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => (p.2 - c) / s) B (Finset.range I) := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    simp only [Finset.coe_range, Set.mem_Iio, hI]
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    calc (((p.2 - c) / s : ℕ) : ℝ) ≤ ((p.2 - c : ℕ) : ℝ) / s := Nat.cast_div_le
      _ ≤ M / s := by
        apply div_le_div_of_nonneg_right _ hspos.le
        rw [Nat.cast_sub (hcp p hp)]; linarith [hp'.2]
  have hcount := Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ i ∈ Finset.range I,
      (((B.filter fun p => (p.2 - c) / s = i).card : ℕ) : ℝ) ≤ log t / M := by
    intro i _
    by_cases hne : (B.filter fun p => (p.2 - c) / s = i).Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hp0' := Finset.mem_filter.1 hp0
      have hp0B := (Finset.mem_filter.1 hp0'.1).2
      have hc0 := hcp p0 hp0'.1
      have hx₁ : M ≤ ((c + s * i : ℕ) : ℝ) := by push_cast; nlinarith [hspos]
      have hx₂ : ((c + s * i : ℕ) : ℝ) ≤ 2 * M := by
        have h1 : c + s * i ≤ p0.2 := by
          rw [← hp0'.2]; have := Nat.mul_div_le (p0.2 - c) s; omega
        have h2 : ((c + s * i : ℕ) : ℝ) ≤ p0.2 := by exact_mod_cast h1
        linarith [hp0B.2]
      have hsub : B.filter (fun p => (p.2 - c) / s = i) ⊆
          (halfSolutions t).filter fun p => |(p.2 : ℝ) - ((c + s * i : ℕ) : ℝ)| ≤ rad k M := by
        intro p hp
        obtain ⟨hpB, hpi⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpB).1, ?_⟩
        have hcp' := hcp p hpB
        have h1 := Nat.div_add_mod (p.2 - c) s
        have h2 := Nat.mod_lt (p.2 - c) (show 0 < s by omega)
        have h3 : p.2 = (c + s * i) + (p.2 - c) % s := by rw [← hpi]; omega
        have h4 : (((p.2 - c) % s : ℕ) : ℝ) < s := by exact_mod_cast h2
        rw [h3]; push_cast
        rw [show ((c : ℝ) + s * i + (((p.2 - c) % s : ℕ) : ℝ)) - (c + s * i) =
          (((p.2 - c) % s : ℕ) : ℝ) by ring, abs_of_nonneg (by positivity)]
        linarith
      calc (((B.filter fun p => (p.2 - c) / s = i).card : ℕ) : ℝ)
          ≤ ((((halfSolutions t).filter fun p =>
              |(p.2 : ℝ) - ((c + s * i : ℕ) : ℝ)| ≤ rad k M).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ log t / M := hW _ M hM0 hM1 hx₁ hx₂
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]
      positivity
  have hsum : (B.card : ℝ) ≤ I * (log t / M) := by
    rw [hcount]; push_cast
    calc ∑ i ∈ Finset.range I, (((B.filter fun p => (p.2 - c) / s = i).card : ℕ) : ℝ)
        ≤ ∑ _i ∈ Finset.range I, log t / M := Finset.sum_le_sum hfib
      _ = I * (log t / M) := by simp
  have hI' : (I : ℝ) ≤ 3 * M / rad k M := by
    rw [hI]; push_cast
    have h1 : (⌊M / s⌋₊ : ℝ) ≤ M / s := Nat.floor_le (by positivity)
    have h2 : M / s ≤ 2 * M / rad k M := by
      rw [div_le_div_iff₀ hspos hrpos]; nlinarith
    have h3 : 1 ≤ M / rad k M := by rw [le_div_iff₀ hrpos]; linarith
    have : 3 * M / rad k M = 2 * M / rad k M + M / rad k M := by ring
    linarith
  have hLM : 0 ≤ log (t : ℝ) / M := by positivity
  -- `3 L / r_M ≤ 6 e^{2a+1} L M^{-α}`
  have hfinal : 3 * log (t : ℝ) ≤
      6 * exp (2 * a₀ k + 1) * log t * M ^ (-((k : ℝ) / (k + 1))) * rad k M := by
    have hα1 : (k : ℝ) / (k + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
    have hMM : M ^ (-((k : ℝ) / (k + 1))) * (M / 2) ^ ((k : ℝ) / (k + 1)) =
        (1 / 2 : ℝ) ^ ((k : ℝ) / (k + 1)) := by
      rw [rpow_neg hMpos.le, ← inv_rpow hMpos.le, ← mul_rpow (by positivity) (by positivity)]
      congr 1; field_simp
    have hhalf : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ ((k : ℝ) / (k + 1)) := by
      calc (1 / 2 : ℝ) = (1 / 2 : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
        _ ≤ _ := rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hα1
    have hE : exp (2 * a₀ k + 1) * exp (-(2 * a₀ k) - 1) = 1 := by
      rw [← exp_add]; ring_nf; exact exp_zero
    have : 6 * exp (2 * a₀ k + 1) * log t * M ^ (-((k : ℝ) / (k + 1))) * rad k M =
        6 * log t * (M ^ (-((k : ℝ) / (k + 1))) * (M / 2) ^ ((k : ℝ) / (k + 1))) *
          (exp (2 * a₀ k + 1) * exp (-(2 * a₀ k) - 1)) := by unfold rad; ring
    rw [this, hMM, hE]
    nlinarith
  calc (B.card : ℝ) ≤ I * (log t / M) := hsum
    _ ≤ 3 * M / rad k M * (log t / M) := mul_le_mul_of_nonneg_right hI' hLM
    _ = 3 * log t / rad k M := by field_simp
    _ ≤ 6 * exp (2 * a₀ k + 1) * log t * M ^ (-((k : ℝ) / (k + 1))) := by
        rw [div_le_iff₀ hrpos]; exact hfinal

/-! ## Summing over dyadic blocks -/

set_option maxHeartbeats 2000000 in
/-- **The middle range.** At most `21 e^{2a₀+1} L^θ` elements of `Sol(t)` have `M₀ < m < M₁`. -/
theorem ct_middle {t k : ℕ} {X : ℝ} (hk : 1 ≤ k) (hW : WindowBound t k)
    (hL : 0 < log (t : ℝ)) (hgood : GoodLam X (log (log t)))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5)) :
    (((halfSolutions t).filter fun p => log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) < (p.2 : ℝ) ∧
        (p.2 : ℝ) < log (t : ℝ) / log (log t) ^ ((7 : ℝ) / 5)).card : ℝ) ≤
      21 * exp (2 * a₀ k + 1) * log (t : ℝ) ^ (((k : ℝ) + 1) / (2 * k + 1)) := by
  classical
  have hlam9 := hgood.1
  have hL1 : 1 ≤ log (t : ℝ) := by
    rw [← exp_log hL]; exact one_le_exp (by linarith)
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set L := log (t : ℝ) with hLdef
  set e := ((k : ℝ) + 1) / (2 * k + 1) with hedef
  set α := (k : ℝ) / (k + 1) with hαdef
  set M₀ := L ^ e with hM₀def
  set M₁ := L / log L ^ ((7 : ℝ) / 5) with hM₁def
  have he0 : 0 ≤ e := by positivity
  have hM₀1 : 1 ≤ M₀ := one_le_rpow hL1 he0
  have hM₀pos : 0 < M₀ := by linarith
  have hex : ∀ m : ℝ, ∃ j : ℕ, m < M₀ * 2 ^ (j + 1) := fun m => by
    obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (m / M₀) (by norm_num : (1 : ℝ) < 2)
    refine ⟨j, ?_⟩
    rw [div_lt_iff₀ hM₀pos] at hj
    have : (2 : ℝ) ^ j ≤ 2 ^ (j + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    nlinarith
  set Mid := (halfSolutions t).filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁ with hMid
  have hg1 : ∀ p : ℕ × ℕ, (p.2 : ℝ) < M₀ * 2 ^ (Nat.find (hex (p.2 : ℝ)) + 1) :=
    fun p => Nat.find_spec (hex _)
  have hg2 : ∀ p ∈ Mid, M₀ * 2 ^ (Nat.find (hex (p.2 : ℝ))) ≤ (p.2 : ℝ) := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    rcases Nat.eq_zero_or_pos (Nat.find (hex (p.2 : ℝ))) with h0 | hpos
    · rw [h0, pow_zero, mul_one]; exact hp'.1.le
    · obtain ⟨j, hj⟩ : ∃ j, Nat.find (hex (p.2 : ℝ)) = j + 1 := ⟨Nat.find (hex (p.2 : ℝ)) - 1, by omega⟩
      have := Nat.find_min (hex (p.2 : ℝ)) (show j < Nat.find (hex (p.2 : ℝ)) by omega)
      push Not at this
      rw [hj]; exact this
  obtain ⟨J, hJ⟩ : ∃ J, J = ⌈M₁⌉₊ := ⟨_, rfl⟩
  have hmaps : Set.MapsTo (fun p : ℕ × ℕ => Nat.find (hex (p.2 : ℝ))) Mid (Finset.range J) := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    have h1 := hg2 p hp
    have h2 : (2 : ℝ) ^ (Nat.find (hex (p.2 : ℝ))) < M₁ := by
      have : (2 : ℝ) ^ (Nat.find (hex (p.2 : ℝ))) ≤ M₀ * 2 ^ (Nat.find (hex (p.2 : ℝ))) :=
        le_mul_of_one_le_left (by positivity) hM₀1
      linarith [hp'.2]
    have h3 : ((Nat.find (hex (p.2 : ℝ)) : ℕ) : ℝ) < M₁ :=
      lt_trans (by exact_mod_cast Nat.lt_two_pow_self) h2
    simp only [Finset.coe_range, Set.mem_Iio, hJ]
    exact Nat.lt_ceil.2 h3
  set E := exp (2 * a₀ k + 1) with hE
  have hfib : ∀ j ∈ Finset.range J,
      (((Mid.filter fun p => Nat.find (hex (p.2 : ℝ)) = j).card : ℕ) : ℝ) ≤
        6 * E * L * (M₀ * 2 ^ j) ^ (-α) := by
    intro j _
    by_cases hne : (Mid.filter fun p => Nat.find (hex (p.2 : ℝ)) = j).Nonempty
    · obtain ⟨p0, hp0⟩ := hne
      have hp0' := Finset.mem_filter.1 hp0
      have hj0 := hg2 p0 hp0'.1
      rw [hp0'.2] at hj0
      have hp0M := (Finset.mem_filter.1 hp0'.1).2
      have hMj0 : M₀ ≤ M₀ * 2 ^ j := le_mul_of_one_le_right hM₀pos.le (one_le_pow₀ (by norm_num))
      have hMj1 : M₀ * 2 ^ j ≤ M₁ := by linarith [hp0M.2]
      have hsub : Mid.filter (fun p => Nat.find (hex (p.2 : ℝ)) = j) ⊆
          (halfSolutions t).filter fun p => M₀ * 2 ^ j ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * (M₀ * 2 ^ j) := by
        intro p hp
        obtain ⟨hpM, hpj⟩ := Finset.mem_filter.1 hp
        refine Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hpM).1, ?_, ?_⟩
        · have := hg2 p hpM; rwa [hpj] at this
        · have := hg1 p; rw [hpj, pow_succ] at this; linarith
      calc (((Mid.filter fun p => Nat.find (hex (p.2 : ℝ)) = j).card : ℕ) : ℝ)
          ≤ ((((halfSolutions t).filter fun p => M₀ * 2 ^ j ≤ (p.2 : ℝ) ∧
              (p.2 : ℝ) ≤ 2 * (M₀ * 2 ^ j)).card : ℕ) : ℝ) := by
            exact_mod_cast Finset.card_le_card hsub
        _ ≤ 6 * E * L * (M₀ * 2 ^ j) ^ (-α) := ct_block hk hW hL hgood hst hMj0 hMj1
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne, Finset.card_empty, Nat.cast_zero]
      positivity
  -- the geometric series
  set q := (2 : ℝ) ^ (-α) with hq
  have hα1 : α ≤ 1 := by rw [hαdef, div_le_one (by positivity)]; linarith
  have hαh : (1 : ℝ) / 2 ≤ α := by
    rw [hαdef, div_le_div_iff₀ (by norm_num) (by positivity)]; linarith
  have hq0 : 0 ≤ q := by positivity
  have h2α : (1.414 : ℝ) ≤ (2 : ℝ) ^ α := by
    calc (1.414 : ℝ) ≤ √2 := Real.le_sqrt_of_sq_le (by norm_num)
      _ = (2 : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
      _ ≤ (2 : ℝ) ^ α := rpow_le_rpow_of_exponent_le (by norm_num) hαh
  have hqα : q * (2 : ℝ) ^ α = 1 := by
    rw [hq, rpow_neg (by norm_num)]; exact inv_mul_cancel₀ (by positivity)
  have hq57 : q ≤ 5 / 7 := by nlinarith
  have hgeom : ∑ j ∈ Finset.range J, q ^ j ≤ 7 / 2 := by
    rw [Finset.range_eq_Ico]
    calc ∑ j ∈ Finset.Ico 0 J, q ^ j ≤ q ^ 0 / (1 - q) :=
          geom_sum_Ico_le_of_lt_one hq0 (by linarith)
      _ ≤ 7 / 2 := by rw [pow_zero, div_le_iff₀ (by linarith)]; linarith
  have hterm : ∀ j : ℕ, (M₀ * 2 ^ j) ^ (-α) = M₀ ^ (-α) * q ^ j := by
    intro j
    rw [mul_rpow hM₀pos.le (by positivity), hq]
    congr 1
    rw [← rpow_natCast, ← rpow_natCast, ← rpow_mul (by norm_num), ← rpow_mul (by norm_num),
      mul_comm]
  have hLM : L * M₀ ^ (-α) = L ^ e := by
    rw [hM₀def, ← rpow_mul (by linarith)]
    calc L * L ^ (e * -α) = L ^ ((1 : ℝ) + e * -α) := by
          rw [rpow_add (by linarith), rpow_one]
      _ = L ^ e := by
          congr 1; rw [hedef, hαdef]; field_simp; ring
  rw [Finset.card_eq_sum_card_fiberwise hmaps]; push_cast
  have hE0 : 0 ≤ E := (exp_pos _).le
  have hM₀α : 0 ≤ M₀ ^ (-α) := by positivity
  calc ∑ j ∈ Finset.range J, (((Mid.filter fun p => Nat.find (hex (p.2 : ℝ)) = j).card : ℕ) : ℝ)
      ≤ ∑ j ∈ Finset.range J, 6 * E * L * (M₀ * 2 ^ j) ^ (-α) := Finset.sum_le_sum hfib
    _ = 6 * E * (L * M₀ ^ (-α)) * ∑ j ∈ Finset.range J, q ^ j := by
        rw [Finset.mul_sum]; congr 1; ext j; rw [hterm]; ring
    _ ≤ 6 * E * (L * M₀ ^ (-α)) * (7 / 2) := by
        apply mul_le_mul_of_nonneg_left hgeom; positivity
    _ ≤ 21 * E * L ^ e := by rw [hLM]; nlinarith [rpow_nonneg (show (0 : ℝ) ≤ L by linarith) e]

/-! ## Putting the ranges together -/

/-- `N(t) ≤ 50 e^{2a₀+1} (log t)^{(k+1)/(2k+1)}` under the hypotheses of Lemmas 7.1 and 7.2. -/
theorem ct_final {t k : ℕ} {X : ℝ} (hk : 1 ≤ k) (hW : WindowBound t k)
    (hL : 0 < log (t : ℝ)) (hgood : GoodLam X (log (log t)))
    (hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5))
    (hlarge : ((halfSolutions t).filter fun p =>
      log t / log (log t) ^ ((7 : ℝ) / 5) ≤ p.2).card ≤ 2) :
    (N t : ℝ) ≤ 50 * exp (2 * a₀ k + 1) * log t ^ (((k : ℝ) + 1) / (2 * k + 1)) := by
  classical
  have ht2 : 2 ≤ t := by
    by_contra h; push Not at h; interval_cases t <;> simp at hL
  have hL1 : 1 ≤ log (t : ℝ) := by
    rw [← exp_log hL]; exact one_le_exp (by linarith [hgood.1])
  set L := log (t : ℝ) with hLdef
  set e := ((k : ℝ) + 1) / (2 * k + 1) with hedef
  set M₀ := L ^ e with hM₀def
  set M₁ := L / log L ^ ((7 : ℝ) / 5) with hM₁def
  set H := halfSolutions t
  have hsplit : H ⊆ (H.filter fun p => (p.2 : ℝ) ≤ M₀) ∪
      (H.filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁) ∪
      (H.filter fun p => M₁ ≤ (p.2 : ℝ)) := by
    intro p hp
    simp only [Finset.mem_union, Finset.mem_filter]
    by_cases h1 : (p.2 : ℝ) ≤ M₀
    · exact Or.inl (Or.inl ⟨hp, h1⟩)
    · by_cases h2 : (p.2 : ℝ) < M₁
      · exact Or.inl (Or.inr ⟨hp, lt_of_not_ge h1, h2⟩)
      · exact Or.inr ⟨hp, le_of_not_gt h2⟩
  have hcardH : (H.card : ℝ) ≤ ((H.filter fun p => (p.2 : ℝ) ≤ M₀).card : ℝ) +
      ((H.filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁).card : ℝ) +
      ((H.filter fun p => M₁ ≤ (p.2 : ℝ)).card : ℝ) := by
    have h1 := Finset.card_le_card hsplit
    have h2 := Finset.card_union_le ((H.filter fun p => (p.2 : ℝ) ≤ M₀) ∪
      (H.filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁)) (H.filter fun p => M₁ ≤ (p.2 : ℝ))
    have h3 := Finset.card_union_le (H.filter fun p => (p.2 : ℝ) ≤ M₀)
      (H.filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁)
    have : H.card ≤ (H.filter fun p => (p.2 : ℝ) ≤ M₀).card +
      (H.filter fun p => M₀ < (p.2 : ℝ) ∧ (p.2 : ℝ) < M₁).card +
      (H.filter fun p => M₁ ≤ (p.2 : ℝ)).card := by omega
    exact_mod_cast this
  have hM₀0 : 0 ≤ M₀ := by positivity
  have hsmall := card_halfSolutions_le ht2 hM₀0
  have hmid := ct_middle hk hW hL hgood hst
  have hlarge' : ((H.filter fun p => M₁ ≤ (p.2 : ℝ)).card : ℝ) ≤ 2 := by exact_mod_cast hlarge
  have hN : (N t : ℝ) ≤ 2 * H.card := by exact_mod_cast N_le_two_mul_card_halfSolutions ht2
  have hE1 : 1 ≤ exp (2 * a₀ k + 1) := one_le_exp (by have := a₀_pos k; linarith)
  have hM₀1 : 1 ≤ M₀ := one_le_rpow hL1 (by positivity)
  have hprod : M₀ ≤ exp (2 * a₀ k + 1) * M₀ := le_mul_of_one_le_left hM₀0 hE1
  have hprod1 : 1 ≤ exp (2 * a₀ k + 1) * M₀ := by linarith
  linarith

/-! ## Theorem 1.3 -/

/-- Theorem 1.3 from Theorem 2.3 and Lemma 7.2 for all large `t` satisfying (7.1). Here
`c₀ = log Λ` for a large absolute constant `Λ`. -/
theorem fixedKBound_of_windows (hM : MRSTT)
    (hW : ∃ X : ℝ, ∀ t k : ℕ, 1 ≤ k → 0 < log (t : ℝ) → GoodLam X (log (log t)) →
      40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5) → WindowBound t k) :
    FixedKBound := by
  obtain ⟨ΛM, hΛM⟩ := card_halfSolutions_large_le hM
  obtain ⟨X, hX⟩ := hW
  obtain ⟨Λ₀, hΛ₀⟩ := eventually_atTop.1 (ct_eventually_goodLam X)
  refine ⟨log (max (max Λ₀ ΛM) (exp 1)), fun k hk t ht => ?_⟩
  set Λ := max (max Λ₀ ΛM) (exp 1) with hΛ
  have hΛe : exp 1 ≤ Λ := le_max_right _ _
  have hΛpos : 0 < Λ := lt_of_lt_of_le (exp_pos 1) hΛe
  have h1 : log Λ ≤ log (log (log t)) := le_of_max_le_left ht
  have h2 : (5 / 2) * log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k) ≤ log (log (log t)) :=
    le_of_max_le_right ht
  have hlogΛ : 1 ≤ log Λ := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hΛe
  obtain ⟨hL, hlam⟩ := ct_lam_of_logloglog t (hlogΛ.trans h1)
  have hlampos : 0 < log (log (t : ℝ)) := lt_of_lt_of_le (exp_pos 1) hlam
  have hlamΛ : Λ ≤ log (log (t : ℝ)) := (log_le_log_iff hΛpos hlampos).1 h1
  have hgood : GoodLam X (log (log t)) :=
    hΛ₀ _ (le_trans ((le_max_left _ _).trans (le_max_left _ _)) hlamΛ)
  have hst : 40 * ((k : ℝ) + 1) ^ 2 * a₀ k ≤ log (log t) ^ ((2 : ℝ) / 5) := by
    have hpos : 0 < 40 * ((k : ℝ) + 1) ^ 2 * a₀ k := by have := a₀_pos k; positivity
    rw [← log_le_log_iff hpos (by positivity), log_rpow hlampos]
    linarith
  exact ct_final hk (hX t k hk hL hgood hst) hL hgood hst
    (hΛM t (le_trans ((le_max_right _ _).trans (le_max_left _ _)) hlamΛ))

/-- **Theorem 1.3.** -/
theorem fixedKBound_of_mrstt (hM : MRSTT) : FixedKBound := by
  obtain ⟨X, hX⟩ := interpolatingFunction_iff.1 interpolatingFunction
  refine fixedKBound_of_windows hM
    ⟨max X (exp (10 ^ 7)), fun t k hk hL hgood hst x₀ M h0 h1 h2 h3 => ?_⟩
  have hgood' : GoodLam X (log (log t)) :=
    ⟨hgood.1, (le_max_left _ _).trans hgood.2.1, hgood.2.2.1, hgood.2.2.2⟩
  have hlam : 2 * 10 ^ 7 ≤ log (log (t : ℝ)) := by
    have := (le_max_right _ _).trans hgood.2.1
    have := exp_le_exp.1 this
    linarith
  exact ct_window hk (hX t) hL hgood' hst h0 h1 h2 h3 (ct_H hk hL hlam hst h0 h1)

end Singmaster
