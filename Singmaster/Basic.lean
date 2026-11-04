module

public import Mathlib

@[expose] public section

/-!
# Basic definitions and the statements of the main theorems

`N t` is the number of pairs `(n, m)` with `n.choose m = t`, and `halfSolutions t` is the set
`Sol(t)` of the paper, the solutions with `2m ≤ n`. This file proves inequality (1.2),
`N(t) ≤ 2 |Sol(t)|` (`N_le_two_mul_card_halfSolutions`), and states:

* `Statement`: `N(t) = O((log t)^{1/2 + c log log log log t / log log log t})` for some `c`;
* `MainBound`: Theorem 1.2;
* `FixedKBound`: Theorem 1.3, with the constant `a₀ k`;
* `MRSTT`: Theorem 2.3, that is, Theorem 1.3 of Matomäki, Radziwiłł, Shao, Tao and
  Teräväinen. It is a hypothesis of the main theorem.
-/

open Real Filter Asymptotics Topology

namespace Singmaster

/-! ## The main statement

`N`, `Statement` and `MRSTT` come first, in the same order as in `../Challenge.lean`. Lean shares
auxiliary proofs (for numerals such as `3 : ℝ`) with earlier declarations, so the definitions
only elaborate to the same terms as in the challenge if nothing precedes them. -/

/-- `N a` is the number of times `a` occurs in Pascal's triangle: the number of pairs
`(n, k) : ℕ × ℕ` with `n.choose k = a`. Pairs with `k > n` have `n.choose k = 0`, so they
never count when `a ≥ 1`. For `a ≤ 1` the set of solutions is infinite and `Set.ncard`
returns the junk value `0`. That does not matter for an asymptotic statement. For `a ≥ 2`
the set is finite (`finite_setOf_choose_eq`), so `N a` is the true count. -/
noncomputable def N (a : ℕ) : ℕ := {p : ℕ × ℕ | p.1.choose p.2 = a}.ncard

/-- **The main statement.** There is a constant `c` such that, as `a → ∞`,
`N(a) = O((log a) ^ (1/2 + c · log log log log a / log log log a))`. -/
def Statement : Prop :=
  ∃ c : ℝ, (fun a : ℕ => (N a : ℝ)) =O[atTop] fun a : ℕ =>
    log a ^ ((1 : ℝ) / 2 + c * log (log (log (log a))) / log (log (log a)))

/-- **Theorem 2.3** (Matomäki, Radziwiłł, Shao, Tao and Teräväinen, Theorem 1.3). For
`0 < ε < 1` and `t` large enough in terms of `ε`, there are at most two solutions of
`C(n, m) = t` with `exp((log n)^{2/3+ε}) ≤ m ≤ n/2`. This is a hypothesis of the main
theorem. -/
def MRSTT : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
    {p : ℕ × ℕ | p.1.choose p.2 = t ∧ exp (log p.1 ^ ((2 : ℝ) / 3 + ε)) ≤ p.2 ∧
      2 * p.2 ≤ p.1}.ncard ≤ 2

/-! ## Elementary facts about `N` -/

theorem le_choose_of_one_le_of_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) : n ≤ n.choose k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    rw [Nat.choose_succ_succ']
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [Nat.choose_one_right]
    · have h1 : n ≤ n.choose j := ih hj (by omega)
      have h2 : 0 < n.choose (j + 1) := Nat.choose_pos (by omega)
      omega

/-- Every solution of `n.choose k = a` with `a ≥ 2` has `0 < k < n ≤ a`. -/
theorem bounds_of_choose_eq {a n k : ℕ} (ha : 2 ≤ a) (h : n.choose k = a) :
    0 < k ∧ k < n ∧ n ≤ a := by
  have hkn : k ≤ n := by
    by_contra hc
    rw [Nat.choose_eq_zero_of_lt (by omega)] at h
    omega
  have hk0 : k ≠ 0 := by rintro rfl; simp at h; omega
  have hkn' : k ≠ n := by rintro rfl; simp at h; omega
  have := le_choose_of_one_le_of_lt (n := n) (k := k) (by omega) (by omega)
  omega

/-- The solutions of `n.choose k = a`, listed inside the finite box `[0, a] × [0, a]`. -/
def solutions (a : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (a + 1) ×ˢ Finset.range (a + 1)).filter fun p => p.1.choose p.2 = a

theorem coe_solutions {a : ℕ} (ha : 2 ≤ a) :
    (solutions a : Set (ℕ × ℕ)) = {p : ℕ × ℕ | p.1.choose p.2 = a} := by
  ext ⟨n, k⟩
  simp only [solutions, Finset.coe_filter, Finset.mem_product, Finset.mem_range,
    Set.mem_ofPred_eq]
  constructor
  · exact fun h => h.2
  · intro h
    obtain ⟨-, h2, h3⟩ := bounds_of_choose_eq ha h
    exact ⟨⟨by omega, by omega⟩, h⟩

theorem finite_setOf_choose_eq {a : ℕ} (ha : 2 ≤ a) :
    {p : ℕ × ℕ | p.1.choose p.2 = a}.Finite := by
  rw [← coe_solutions ha]
  exact Finset.finite_toSet _

theorem N_eq_card {a : ℕ} (ha : 2 ≤ a) : N a = (solutions a).card := by
  rw [N, ← coe_solutions ha, Set.ncard_coe_finset]

/-- Sanity check: `6 = C(6,1) = C(6,5) = C(4,2)`. -/
example : N 6 = 3 := by rw [N_eq_card (by norm_num)]; decide

/-- Sanity check: `10 = C(10,1) = C(10,9) = C(5,2) = C(5,3)`. -/
example : N 10 = 4 := by rw [N_eq_card (by norm_num)]; decide

/-! ## Theorems 1.2 and 1.3 -/

/-- The constant `a₀(k) = 10 (16k+12)^{2k+3/2} e^{10.75k+5.5}` of Theorem 1.3. -/
noncomputable def a₀ (k : ℕ) : ℝ :=
  10 * (16 * (k : ℝ) + 12) ^ (2 * (k : ℝ) + 3 / 2) * exp (10.75 * k + 5.5)

/-- **Theorem 1.3.** There is an absolute constant `c₀` such that, for every `k ≥ 1` and every
`t` with `log log log t ≥ max(c₀, (5/2) log(40 (k+1)² a₀(k)))`,
`N(t) ≤ 50 e^{2 a₀(k) + 1} (log t)^{(k+1)/(2k+1)}`. -/
def FixedKBound : Prop :=
  ∃ c₀ : ℝ, ∀ k : ℕ, 1 ≤ k → ∀ t : ℕ,
    max c₀ ((5 / 2) * log (40 * ((k : ℝ) + 1) ^ 2 * a₀ k)) ≤ log (log (log t)) →
      (N t : ℝ) ≤ 50 * exp (2 * a₀ k + 1) * log t ^ (((k : ℝ) + 1) / (2 * k + 1))

/-- **Theorem 1.2.** For all sufficiently large `t`,
`N(t) ≤ (log t)^{1/2 + 51 log log log log t / log log log t}`. -/
def MainBound : Prop :=
  ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
    (N t : ℝ) ≤ log t ^ ((1 : ℝ) / 2 + 51 * log (log (log (log t))) / log (log (log t)))

lemma a₀_pos (k : ℕ) : 0 < a₀ k := by unfold a₀; positivity

lemma log_le_of_le_two_pow {x : ℝ} {m : ℕ} (hx : 0 < x) (h : x ≤ 2 ^ m) :
    log x ≤ m * log 2 := by
  have := Real.log_le_log hx h
  rwa [Real.log_pow] at this

/-- `a₀(k) ≥ 10 (16k+12) = 40 (4k+3)`. -/
lemma a₀_ge (k : ℕ) : 10 * (16 * (k : ℝ) + 12) ≤ a₀ k := by
  unfold a₀
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (1 : ℝ) ≤ 16 * k + 12 := by linarith
  have h2 : (16 * (k : ℝ) + 12) ≤ (16 * (k : ℝ) + 12) ^ (2 * (k : ℝ) + 3 / 2) := by
    calc (16 * (k : ℝ) + 12) = (16 * (k : ℝ) + 12) ^ (1 : ℝ) := (rpow_one _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le h1 (by linarith)
  have h3 : 1 ≤ exp (10.75 * k + 5.5) := one_le_exp (by positivity)
  have h4 : 0 ≤ (16 * (k : ℝ) + 12) ^ (2 * (k : ℝ) + 3 / 2) := by positivity
  nlinarith


/-! ## The set `Sol(t)` -/

/-- The set `Sol(t)`: the solutions `(n, m)` of `n.choose m = t` with `2m ≤ n`. -/
def halfSolutions (t : ℕ) : Finset (ℕ × ℕ) :=
  (solutions t).filter fun p => 2 * p.2 ≤ p.1

theorem mem_halfSolutions {t : ℕ} (ht : 2 ≤ t) {p : ℕ × ℕ} :
    p ∈ halfSolutions t ↔ p.1.choose p.2 = t ∧ 2 * p.2 ≤ p.1 := by
  have := congrArg (p ∈ ·) (coe_solutions ht)
  simp only [Finset.mem_coe, Set.mem_ofPred_eq, eq_iff_iff] at this
  simp [halfSolutions, this]

theorem choose_lt_choose_succ {n m : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n + 1) :
    n.choose m < (n + 1).choose m := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  rw [Nat.choose_succ_succ']
  have : 0 < n.choose j := Nat.choose_pos (by omega)
  omega

theorem choose_strictMonoOn {m : ℕ} (hm : 1 ≤ m) {n n' : ℕ} (hmn : m ≤ n) (h : n < n') :
    n.choose m < n'.choose m := by
  induction n' with
  | zero => omega
  | succ n' ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact (ih h).trans (choose_lt_choose_succ hm (by omega))
    · exact choose_lt_choose_succ hm (by omega)

/-- Statement (1.3): for `t ≥ 2`, an element `(n, m)` of `Sol(t)` is determined by `m`. -/
theorem halfSolutions_injOn_snd {t : ℕ} (ht : 2 ≤ t) :
    Set.InjOn Prod.snd (halfSolutions t : Set (ℕ × ℕ)) := by
  rintro ⟨n, m⟩ hp ⟨n', m'⟩ hp' (rfl : m = m')
  rw [Finset.mem_coe, mem_halfSolutions ht] at hp hp'
  dsimp only at hp hp'
  obtain ⟨hm, hmn, -⟩ := bounds_of_choose_eq ht hp.1
  obtain ⟨-, hmn', -⟩ := bounds_of_choose_eq ht hp'.1
  simp only [Prod.mk.injEq, and_true]
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := choose_strictMonoOn hm hmn.le h; omega
  · have := choose_strictMonoOn hm hmn'.le h; omega

/-- Inequality (1.2), `N(t) ≤ 2 |Sol(t)|`, from the reflection `m ↦ n - m`. -/
theorem N_le_two_mul_card_halfSolutions {t : ℕ} (ht : 2 ≤ t) :
    N t ≤ 2 * (halfSolutions t).card := by
  classical
  let f : ℕ × ℕ → ℕ × ℕ := fun p => if 2 * p.2 ≤ p.1 then p else (p.1, p.1 - p.2)
  have himage : (solutions t).image f ⊆ halfSolutions t := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    rw [← Finset.mem_coe, coe_solutions ht, Set.mem_ofPred_eq] at hp
    rw [mem_halfSolutions ht]
    obtain ⟨-, hkn, -⟩ := bounds_of_choose_eq ht hp
    by_cases h : 2 * p.2 ≤ p.1
    · simp only [f, h, ite_true]; exact ⟨hp, trivial⟩
    · simp only [f, h, ite_false]
      refine ⟨?_, by omega⟩
      rw [Nat.choose_symm hkn.le]; exact hp
  have hfib : ∀ q ∈ (solutions t).image f, ((solutions t).filter fun p => f p = q).card ≤ 2 := by
    intro q _
    calc ((solutions t).filter fun p => f p = q).card ≤ ({q, (q.1, q.1 - q.2)} : Finset _).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          obtain ⟨hp, rfl⟩ := hp
          rw [← Finset.mem_coe, coe_solutions ht, Set.mem_ofPred_eq] at hp
          obtain ⟨-, hkn, -⟩ := bounds_of_choose_eq ht hp
          by_cases h : 2 * p.2 ≤ p.1
          · simp [f, h]
          · simp only [f, h, ite_false, Finset.mem_insert, Finset.mem_singleton]
            right; ext <;> simp; omega
      _ ≤ 2 := Finset.card_le_two
  rw [N_eq_card ht]
  calc (solutions t).card ≤ 2 * ((solutions t).image f).card :=
        Finset.card_le_mul_card_image _ 2 hfib
    _ ≤ 2 * (halfSolutions t).card := by gcongr

/-- There are at most `M` elements `(n, m)` of `Sol(t)` with `m ≤ M`. -/
theorem card_halfSolutions_le {t : ℕ} (ht : 2 ≤ t) {M : ℝ} (hM : 0 ≤ M) :
    (((halfSolutions t).filter fun p => (p.2 : ℝ) ≤ M).card : ℝ) ≤ M := by
  classical
  have hsub : ((halfSolutions t).filter fun p => (p.2 : ℝ) ≤ M).image Prod.snd ⊆
      Finset.Icc 1 ⌊M⌋₊ := by
    intro m hm
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hm
    rw [Finset.mem_filter, mem_halfSolutions ht] at hp
    obtain ⟨h1, -, -⟩ := bounds_of_choose_eq ht hp.1.1
    exact Finset.mem_Icc.2 ⟨h1, Nat.le_floor hp.2⟩
  have hinj : Set.InjOn Prod.snd
      (((halfSolutions t).filter fun p => (p.2 : ℝ) ≤ M) : Set (ℕ × ℕ)) :=
    (halfSolutions_injOn_snd ht).mono (by intro p hp; simp at hp ⊢; exact hp.1)
  have := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Nat.card_Icc] at this
  calc (((halfSolutions t).filter fun p => (p.2 : ℝ) ≤ M).card : ℝ) ≤ (⌊M⌋₊ : ℝ) := by
        exact_mod_cast this.trans (by omega)
    _ ≤ M := Nat.floor_le hM

/-- The quantity `η₀ = 2 (log x₀ + 4)/x₀ + 2 e^{-ℓ/5}` of Proposition 3.1, which bounds the
variation of `κ`. -/
noncomputable def η₀ (x₀ ℓ : ℝ) : ℝ := 2 * (log x₀ + 4) / x₀ + 2 * exp (-ℓ / 5)

end Singmaster
