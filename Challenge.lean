module

public import Mathlib

@[expose] public section

/-!
# Challenge for `lake comparator`

The statement of the main theorem, together with the definitions it depends on, written out
from Mathlib alone. `lake comparator` checks that `Singmaster.statement_of_mrstt` in the
module `Singmaster` proves exactly this statement, using only the axioms listed in
`comparator.json`. To trust the result you need to read this file, not the development.

The three definitions must stay identical to, and in the same order as, the first three
declarations of `Singmaster/Basic.lean`: Lean shares auxiliary proofs (for numerals such as
`3 : ℝ`) with earlier declarations, so any other order changes the elaborated terms.

* `N a` is the number of pairs `(n, m)` with `n.choose m = a`.
* `MRSTT` is Theorem 1.3 of Matomäki, Radziwiłł, Shao, Tao and Teräväinen, *Singmaster's
  conjecture in the interior of Pascal's triangle*: for `0 < ε < 1` and `t` large enough,
  at most two solutions of `C(n, m) = t` satisfy `exp((log n)^{2/3+ε}) ≤ m ≤ n/2`.
* `Statement` says `N(a) = O((log a)^{1/2 + c log log log log a / log log log a})` for some `c`.
-/

open Real Filter Asymptotics Topology

namespace Singmaster

noncomputable def N (a : ℕ) : ℕ := {p : ℕ × ℕ | p.1.choose p.2 = a}.ncard

def Statement : Prop :=
  ∃ c : ℝ, (fun a : ℕ => (N a : ℝ)) =O[atTop] fun a : ℕ =>
    log a ^ ((1 : ℝ) / 2 + c * log (log (log (log a))) / log (log (log a)))

def MRSTT : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ t₁ : ℕ, ∀ t : ℕ, t₁ ≤ t →
    {p : ℕ × ℕ | p.1.choose p.2 = t ∧ exp (log p.1 ^ ((2 : ℝ) / 3 + ε)) ≤ p.2 ∧
      2 * p.2 ≤ p.1}.ncard ≤ 2

theorem statement_of_mrstt (hM : MRSTT) : Statement := sorry

end Singmaster
