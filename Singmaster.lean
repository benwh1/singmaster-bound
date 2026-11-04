module

public import Singmaster.FixedK.Main
public import Singmaster.MainBound

@[expose] public section

/-!
# Singmaster's problem

A formalisation of the paper `../paper/singmaster.tex`. The main result is

* `Singmaster.statement_of_mrstt : MRSTT → Statement`.

Here `MRSTT` is Theorem 2.3 of the paper (Theorem 1.3 of Matomäki, Radziwiłł, Shao, Tao and
Teräväinen), which is a hypothesis, and `Statement` says that there is a constant `c` with
`N(t) = O((log t)^{1/2 + c log log log log t / log log log t})`. The proof gives `c = 51`.
Running `lake run` prints the axioms that `statement_of_mrstt` depends on.

## Layout

The modules follow the sections of the paper.

* `Singmaster.Basic`: the function `N`, the set `Sol(t)` (`halfSolutions`), the constant
  `a₀(k)`, and the statements of Theorem 1.2 (`MainBound`), Theorem 1.3 (`FixedKBound`) and
  Theorem 2.3 (`MRSTT`).
* `Singmaster.Stirling.*`: Lemma 2.1, Stirling's formula (`stirlingFormula`).
* `Singmaster.Bernoulli`: Lemma 2.2 (`powSumPoly_eval_nat`, `bernC_eval_norm_le`).
* `Singmaster.Interpolation.*`: Section 3, Proposition 3.1 (`interpolatingFunction`).
* `Singmaster.Determinant.*`: Section 4, Proposition 4.1 (`solutions_on_curve`), with the Schwarz
  lemma for interpolation determinants (`interpolation_det_le`).
* `Singmaster.ExpPoly.*`: Section 5, Lemma 5.1 (`expPoly_bound`).
* `Singmaster.ZeroEstimate.*`: Section 6, Proposition 6.1 (`zero_estimate`).
* `Singmaster.FixedK.*`: Section 7, Lemmas 7.1 and 7.2 and Theorem 1.3 (`fixedKBound_of_mrstt`).
* `Singmaster.MainBound`: Section 8, Theorem 1.2 from Theorem 1.3 (`mainBound_of_fixedKBound`).
-/

namespace Singmaster

/-- **Main theorem.** Theorem 2.3 implies that
`N(t) = O((log t)^{1/2 + c log log log log t / log log log t})`, with `c = 51`. -/
theorem statement_of_mrstt (hM : MRSTT) : Statement :=
  statement_of_mainBound (mainBound_of_fixedKBound (fixedKBound_of_mrstt hM))

end Singmaster
