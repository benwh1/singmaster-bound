module

public import Singmaster.Basic

@[expose] public section

/-!
# Theorem 1.3 implies Theorem 1.2

This is Section 8 of the paper. With `s = log log log t`, the proof takes
`k = ⌊s / (100 log s)⌋` in Theorem 1.3 and uses inequality (8.1),
`log(40 (k+1)² a₀(k)) ≤ 37.5 k log(k+2)` (`log_a₀_bound`). The pointwise argument is
`main_pointwise`, the implication is `mainBound_of_fixedKBound`, and `statement_of_mainBound`
deduces the `O`-statement with `c = 51`.
-/

open Real Filter Asymptotics Topology

namespace Singmaster

lemma log_three_gt : (1.0974 : ℝ) < log 3 := by
  have h : log ((2 : ℝ) ^ 19) < log ((3 : ℝ) ^ 12) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  have := Real.log_two_gt_d9
  push_cast at h
  linarith

/-- Inequality (8.1): `log(40 (k+1)² a₀(k)) ≤ 37.5 k log(k+2)` for all `k ≥ 1`. -/
theorem log_a₀_bound {k : ℕ} (hk : 1 ≤ k) :
    log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k) ≤ 37.5 * k * log (k + 2) := by
  have hK : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h16 : (0 : ℝ) < 16 * k + 12 := by positivity
  have hX : (0 : ℝ) < (16 * (k : ℝ) + 12) ^ (2 * (k : ℝ) + 3 / 2) := by positivity
  have ha : log (a₀ k) =
      log 10 + (2 * k + 3 / 2) * log (16 * k + 12) + (10.75 * k + 5.5) := by
    unfold a₀
    rw [Real.log_mul (mul_pos (by norm_num) hX).ne' (exp_pos _).ne',
      Real.log_mul (by norm_num) hX.ne', Real.log_rpow h16, Real.log_exp]
  have hexpand : log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k) =
      log 40 + 2 * log ((k : ℝ) + 1) + log (a₀ k) := by
    rw [Real.log_mul (by positivity) (a₀_pos k).ne', Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast; ring
  rw [hexpand, ha]
  have hl2 := Real.log_two_lt_d9
  have hl3 := log_three_gt
  have hL : log 3 ≤ log ((k : ℝ) + 2) := Real.log_le_log (by norm_num) (by linarith)
  have hL1 : log ((k : ℝ) + 1) ≤ log ((k : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by linarith)
  have h40 : log (40 : ℝ) ≤ 6 * log 2 := by
    have := log_le_of_le_two_pow (x := 40) (m := 6) (by norm_num) (by norm_num)
    push_cast at this; linarith
  have h10 : log (10 : ℝ) ≤ 4 * log 2 := by
    have := log_le_of_le_two_pow (x := 10) (m := 4) (by norm_num) (by norm_num)
    push_cast at this; linarith
  have hL16 : log (16 * (k : ℝ) + 12) ≤ 4 * log 2 + log ((k : ℝ) + 2) := by
    have h1 : log (16 * (k : ℝ) + 12) ≤ log (16 * ((k : ℝ) + 2)) :=
      Real.log_le_log h16 (by linarith)
    rw [Real.log_mul (by norm_num) (by positivity)] at h1
    have h2 : log (16 : ℝ) = 4 * log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith
  have p1 : (2 * (k : ℝ) + 3 / 2) * log (16 * k + 12) ≤
      (2 * (k : ℝ) + 3 / 2) * (4 * log 2 + log ((k : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left hL16 (by positivity)
  have p2 : (35.5 * (k : ℝ) - 3.5) * 1.0974 ≤ (35.5 * (k : ℝ) - 3.5) * log ((k : ℝ) + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have p3 : (k : ℝ) * log 2 ≤ (k : ℝ) * 0.6931471808 :=
    mul_le_mul_of_nonneg_left hl2.le (by linarith)
  nlinarith

/-! ## Eventual inequalities -/

lemma tendsto_log1 : Tendsto (fun t : ℕ => log (t : ℝ)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_log2 : Tendsto (fun t : ℕ => log (log (t : ℝ))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log1

lemma tendsto_log3 : Tendsto (fun t : ℕ => log (log (log (t : ℝ)))) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log2

/-- Conditions on `s = log log log t` that hold for large `s`. -/
lemma eventually_s (c : ℝ) :
    ∀ᶠ s : ℝ in atTop, c ≤ s ∧ 3 ≤ s ∧ 1 ≤ log s ∧ 100 * log s ≤ s := by
  have h1 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 100 by norm_num)
  have h2 : ∀ᶠ s : ℝ in atTop, 1 ≤ log s := tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [h1, h2, eventually_ge_atTop c, eventually_ge_atTop 3] with s h1 h2 h3 h4
  refine ⟨h3, h4, h2, ?_⟩
  rw [Real.norm_of_nonneg (by linarith), id, Real.norm_of_nonneg (by linarith)] at h1
  linarith

/-- The condition on `x = log log t` that makes
`50 e^{2 x^{2/5} + 1} ≤ (log t)^{log log log log t / log log log t}`. -/
lemma eventually_x :
    ∀ᶠ x : ℝ in atTop, 0 < log x ∧ log 50 + 1 + 2 * x ^ ((2 : ℝ) / 5) ≤ x / log x := by
  have h1 := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 3 / 5 by norm_num)).bound
    (show (0 : ℝ) < 1 / 4 by norm_num)
  have h2 : ∀ᶠ x : ℝ in atTop, 3 ≤ x ^ ((2 : ℝ) / 5) :=
    (tendsto_rpow_atTop (by norm_num)).eventually_ge_atTop 3
  have h3 : ∀ᶠ x : ℝ in atTop, 1 ≤ log x := tendsto_log_atTop.eventually_ge_atTop 1
  filter_upwards [h1, h2, h3, eventually_ge_atTop 1] with x h1 h2 h3 h4
  have hx0 : (0 : ℝ) ≤ x := by linarith
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (by positivity)] at h1
  have hxx : x ^ ((2 : ℝ) / 5) * x ^ ((3 : ℝ) / 5) = x := by
    rw [← Real.rpow_add (by linarith)]; norm_num
  have h50 : log (50 : ℝ) ≤ 6 * log 2 := by
    have := log_le_of_le_two_pow (x := 50) (m := 6) (by norm_num) (by norm_num)
    push_cast at this; linarith
  have hl2 := Real.log_two_lt_d9
  refine ⟨by linarith, ?_⟩
  rw [le_div_iff₀ (by linarith)]
  have hA0 : (0 : ℝ) ≤ x ^ ((2 : ℝ) / 5) := by positivity
  have p1 : (log 50 + 1 + 2 * x ^ ((2 : ℝ) / 5)) * log x ≤ (4 * x ^ ((2 : ℝ) / 5)) * log x :=
    mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have p2 : (4 * x ^ ((2 : ℝ) / 5)) * log x ≤ (4 * x ^ ((2 : ℝ) / 5)) * (1 / 4 * x ^ ((3 : ℝ) / 5)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  nlinarith

/-! ## Theorem 1.3 implies Theorem 1.2 -/

/-- The proof of Theorem 1.2, written with `L = log t` and `Nt = N(t)` as real variables. With
`s = log log L`, it takes `k = ⌊s / (100 log s)⌋` in Theorem 1.3 and collects the error
terms. -/
theorem main_pointwise {c₀ Nt L : ℝ}
    (hA : ∀ k : ℕ, 1 ≤ k →
      max c₀ ((5 / 2) * log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k)) ≤ log (log L) →
        Nt ≤ 50 * exp (2 * a₀ k + 1) * L ^ (((k : ℝ) + 1) / (2 * k + 1)))
    (hL : 1 < L)
    (hs : c₀ ≤ log (log L) ∧ 3 ≤ log (log L) ∧ 1 ≤ log (log (log L)) ∧
      100 * log (log (log L)) ≤ log (log L))
    (hx : 0 < log (log L) ∧ log 50 + 1 + 2 * (log L) ^ ((2 : ℝ) / 5) ≤ log L / log (log L)) :
    Nt ≤ L ^ ((1 : ℝ) / 2 + 51 * log (log (log L)) / log (log L)) := by
  obtain ⟨hcs, hs3, hls, hs100⟩ := hs
  obtain ⟨-, hxb⟩ := hx
  have hxpos : 0 < log L := Real.log_pos hL
  generalize hxdef : log L = x at *
  generalize hsdef : log x = s at *
  have hs0 : 0 < s := by linarith
  have hlogs : 0 < log s := by linarith
  -- the choice `k = ⌊y⌋`, with `y = s / (100 log s)`
  obtain ⟨y, hy⟩ : ∃ y, y = s / (100 * log s) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ (by positivity)]; linarith
  obtain ⟨k, hk⟩ : ∃ k, k = ⌊y⌋₊ := ⟨_, rfl⟩
  have hk1 : 1 ≤ k := by rw [hk]; exact Nat.le_floor (by simpa using hy1)
  have hK1 : (1 : ℝ) ≤ k := by exact_mod_cast hk1
  have hky : (k : ℝ) ≤ y := by rw [hk]; exact Nat.floor_le (by linarith)
  have hky' : y < k + 1 := by rw [hk]; exact Nat.lt_floor_add_one y
  have hk_half : y ≤ 2 * k := by linarith
  -- the hypothesis of Theorem 1.3 holds for this `k`
  have hy100 : y ≤ s / 100 := by
    rw [hy]; exact div_le_div_of_nonneg_left hs0.le (by norm_num) (by linarith)
  have hlogk : log ((k : ℝ) + 2) ≤ log s := Real.log_le_log (by positivity) (by linarith)
  have hylog : y * log s = s / 100 := by rw [hy]; field_simp
  have hklog : (k : ℝ) * log ((k : ℝ) + 2) ≤ s / 100 := by
    rw [← hylog]
    exact mul_le_mul hky hlogk (Real.log_nonneg (by linarith)) (by linarith)
  have hA0 := log_a₀_bound hk1
  have hstand : (5 / 2) * log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k) ≤ s := by linarith
  have hN := hA k hk1 (max_le hcs hstand)
  -- `a₀(k) ≤ (log L)^{2/5}`
  have ha0 : a₀ k ≤ x ^ ((2 : ℝ) / 5) := by
    have hpos : 0 < 40 * ((k : ℝ) + 1) ^ 2 * a₀ k := by have := a₀_pos k; positivity
    have h1 : log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k) ≤ (2 / 5) * s := by linarith
    rw [Real.log_le_iff_le_exp hpos] at h1
    have h3 : exp ((2 / 5) * s) = x ^ ((2 : ℝ) / 5) := by
      rw [Real.rpow_def_of_pos hxpos, hsdef, mul_comm]
    have h4 : a₀ k ≤ 40 * ((k : ℝ) + 1) ^ 2 * a₀ k := by
      have := a₀_pos k
      have : (1 : ℝ) ≤ 40 * ((k : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith
    linarith
  -- the exponent: `(k+1)/(2k+1) ≤ 1/2 + 1/(4k) ≤ 1/2 + 50 log s / s`
  have hexp : ((k : ℝ) + 1) / (2 * k + 1) ≤ 1 / 2 + 50 * log s / s := by
    have h200 : s ≤ 200 * k * log s := by
      have := hk_half
      rw [hy, div_le_iff₀ (by positivity)] at this
      linarith
    have hq : 1 ≤ 4 * k * (50 * log s / s) := by
      rw [show 4 * (k : ℝ) * (50 * log s / s) = 200 * k * log s / s by ring,
        le_div_iff₀ hs0]
      linarith
    have hq0 : 0 ≤ 50 * log s / s := by positivity
    rw [div_le_iff₀ (by positivity)]
    generalize 50 * log s / s = q at hq hq0 ⊢
    nlinarith
  have hpow : L ^ (((k : ℝ) + 1) / (2 * k + 1)) ≤ L ^ ((1 : ℝ) / 2 + 50 * log s / s) :=
    Real.rpow_le_rpow_of_exponent_le hL.le hexp
  -- the constant: `50 e^{2 a₀ + 1} ≤ L^{log s / s}`
  have hconst : 50 * exp (2 * a₀ k + 1) ≤ L ^ (log s / s) := by
    rw [Real.rpow_def_of_pos (by linarith), hxdef,
      show (50 : ℝ) * exp (2 * a₀ k + 1) = exp (log 50 + (2 * a₀ k + 1)) by
        rw [Real.exp_add (log 50), Real.exp_log (by norm_num : (0 : ℝ) < 50)]]
    apply Real.exp_le_exp.mpr
    have h1 : x / s ≤ x * (log s / s) := by
      rw [mul_div_assoc']
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_right hxpos.le hls) hs0.le
    linarith
  have hL0 : (0 : ℝ) ≤ L := by linarith
  calc Nt ≤ 50 * exp (2 * a₀ k + 1) * L ^ (((k : ℝ) + 1) / (2 * k + 1)) := hN
    _ ≤ L ^ (log s / s) * L ^ ((1 : ℝ) / 2 + 50 * log s / s) :=
        mul_le_mul hconst hpow (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hL0 _)
    _ = L ^ ((1 : ℝ) / 2 + 51 * log s / s) := by
        rw [← Real.rpow_add (by linarith)]; congr 1; ring

/-- **Theorem 1.3 implies Theorem 1.2.** -/
theorem mainBound_of_fixedKBound (hA : FixedKBound) : MainBound := by
  obtain ⟨c₀, hA⟩ := hA
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.1
    ((tendsto_log3.eventually (eventually_s c₀)).and
      ((tendsto_log2.eventually eventually_x).and (tendsto_log1.eventually (eventually_gt_atTop 1))))
  refine ⟨t₀, fun t ht => ?_⟩
  obtain ⟨h1, h2, h3⟩ := ht₀ t ht
  exact main_pointwise (fun k hk h => hA k hk t h) h3 h1 h2

/-! ## The `O`-statement -/

/-- Theorem 1.2 gives `Statement` with `c = 51` and implied constant `1`. -/
theorem statement_of_mainBound (hB : MainBound) : Statement := by
  obtain ⟨t₀, ht⟩ := hB
  refine ⟨51, IsBigO.of_bound 1 ?_⟩
  filter_upwards [eventually_ge_atTop t₀, eventually_ge_atTop 1] with t h h1
  have hlog : 0 ≤ log (t : ℝ) := Real.log_nonneg (by exact_mod_cast h1)
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _), Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    one_mul]
  exact ht t h

/-- Sanity check that `Statement` has the intended strength: for every `c` the exponent
`1/2 + c log log log log a / log log log a` tends to `1/2`. So `Statement` says
`N(a) ≤ (log a)^{1/2 + o(1)}`, with the `o(1)` given explicitly. -/
theorem exponent_tendsto (c : ℝ) :
    Tendsto (fun a : ℕ => (1 : ℝ) / 2 + c * log (log (log (log (a : ℝ)))) / log (log (log a)))
      atTop (𝓝 (1 / 2)) := by
  have h : Tendsto (fun s : ℝ => log s / s) atTop (𝓝 0) := by
    simpa using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have := ((h.comp tendsto_log3).const_mul c).const_add (1 / 2)
  simpa [mul_div_assoc] using this

end Singmaster
