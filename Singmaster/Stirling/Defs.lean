module

public import Mathlib

@[expose] public section

/-!
# Stirling's formula: definitions

We construct `lg z = σ(z) + J(z)`. Here `σ(z) = (z + 1/2) log z - z + ½ log 2π` is the main
term of Lemma 2.1, and `J(z) = ∑_{n ≥ 0} j(z + n)` is Gudermann's series, with
`j(w) = (w + 1/2)(log(w+1) - log w) - 1`. The function `lg` equals `log Γ(z+1)`, but the Gamma
function is not used: `lg m = log m!` is checked by telescoping, together with Mathlib's
Stirling formula for factorials.
-/

open Complex

namespace Singmaster

/-- `j(w) = (w + 1/2)(log(w+1) - log w) - 1`. -/
noncomputable def binetTerm (w : ℂ) : ℂ := (w + 1 / 2) * (Complex.log (w + 1) - Complex.log w) - 1

/-- Gudermann's series `J(z) = ∑_{n ≥ 0} j(z + n)`. -/
noncomputable def binetJ (z : ℂ) : ℂ := ∑' n : ℕ, binetTerm (z + n)

/-- The Stirling main term `σ(z) = (z + 1/2) log z - z + ½ log 2π`. -/
noncomputable def stirlingMain (z : ℂ) : ℂ :=
  (z + 1 / 2) * Complex.log z - z + Real.log (2 * Real.pi) / 2

/-- `lg z = σ(z) + J(z)` (with the convention `lg 0 = 0`). -/
noncomputable def lgStirling (z : ℂ) : ℂ := if z = 0 then 0 else stirlingMain z + binetJ z

end Singmaster
