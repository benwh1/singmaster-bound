module

public import Singmaster.Stirling.Integers

@[expose] public section

/-!
# Lemma 2.1: Stirling's formula

`lgStirling = σ + J` is holomorphic on `Re z > 0`, equals `log m!` at every natural number `m`,
and satisfies `|lgStirling z - σ(z)| = |J(z)| ≤ 4/(9|z|) ≤ 1/|z|` for `Re z > 0` and `|z| ≥ 1`
(`stirlingFormula`).
-/

open Complex

namespace Singmaster

/-- **Lemma 2.1** (Stirling's formula). There is a function `lg`, holomorphic on `Re z > 0`, with
`lg m = log m!` for every `m : ℕ` and `|lg z - σ(z)| ≤ 1/|z|` for `Re z > 0` and `|z| ≥ 1`,
where `σ(z) = (z + 1/2) log z - z + ½ log 2π`. (The function is `log Γ(z+1)`.) -/
def StirlingFormula : Prop :=
  ∃ lg : ℂ → ℂ, DifferentiableOn ℂ lg {z : ℂ | 0 < z.re} ∧
    (∀ m : ℕ, lg m = Real.log (m.factorial)) ∧
    (∀ z : ℂ, 0 < z.re → 1 ≤ ‖z‖ →
      ‖lg z - ((z + 1 / 2) * Complex.log z - z + Real.log (2 * Real.pi) / 2)‖ ≤ 1 / ‖z‖)

theorem stirlingMain_differentiableOn : DifferentiableOn ℂ stirlingMain {z : ℂ | 0 < z.re} := by
  intro z hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.2 (Or.inl hz)
  apply DifferentiableAt.differentiableWithinAt
  unfold stirlingMain
  have hlog : DifferentiableAt ℂ Complex.log z := Complex.differentiableAt_log hslit
  exact ((((differentiableAt_id.add_const _).mul hlog).sub differentiableAt_id).add_const _)

/-- **Lemma 2.1.** -/
theorem stirlingFormula : StirlingFormula := by
  refine ⟨lgStirling, ?_, lgStirling_nat, ?_⟩
  · refine (stirlingMain_differentiableOn.add binetJ_differentiableOn).congr fun z hz => ?_
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    simp [lgStirling, hz0]
  · intro z hre hz1
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hre
    have hzpos : 0 < ‖z‖ := by linarith
    simp only [lgStirling, hz0, ite_false]
    have h : stirlingMain z + binetJ z -
        ((z + 1 / 2) * Complex.log z - z + (Real.log (2 * Real.pi) : ℂ) / 2) = binetJ z := by
      unfold stirlingMain; ring
    calc ‖stirlingMain z + binetJ z -
          ((z + 1 / 2) * Complex.log z - z + (Real.log (2 * Real.pi) : ℂ) / 2)‖
        = ‖binetJ z‖ := by rw [h]
      _ ≤ 4 / (9 * ‖z‖) := binetJ_norm_le hre hz1
      _ ≤ 1 / ‖z‖ := by
          rw [div_le_div_iff₀ (by positivity) hzpos]; nlinarith

end Singmaster
