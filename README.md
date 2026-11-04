# Singmaster's Conjecture in Lean 4

This is a Lean 4 and Mathlib formalisation of an upper bound on the number of representations of an
integer as a binomial coefficient. The paper shows that the number `N(t)` of pairs `(n, m)` with
`C(n, m) = t` satisfies

```
N(t) ≤ (log t)^(1/2 + 51 · log log log log t / log log log t)
```

for all sufficiently large `t`.

## Main theorem

```lean
theorem Singmaster.statement_of_mrstt : MRSTT → Statement
```

- `Statement` says that there is a constant `c` with
  `N(t) = O((log t)^(1/2 + c · log log log log t / log log log t))`. The proof gives `c = 51`.
- `MRSTT` is Theorem 2.3 of the paper, which is Theorem 1.3 of Matomäki, Radziwiłł, Shao, Tao and
  Teräväinen, *Singmaster's conjecture in the interior of Pascal's triangle* (arXiv:2106.03335).
  It is a hypothesis of the theorem, not an axiom.

Everything else, including Stirling's formula for complex arguments, is proved from Mathlib. The
development contains no `sorry`. The main theorem depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Building

You need [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.35.0`) and
the Mathlib version are pinned in `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get   # download prebuilt Mathlib files
lake build           # check the whole development
lake run             # build, then print the main theorem and its axioms
```

`lake run` runs `PrintAxioms.lean` and should print

```
Singmaster.statement_of_mrstt : Singmaster.MRSTT → Singmaster.Statement
'Singmaster.statement_of_mrstt' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Checking with comparator

`Challenge.lean` states the main theorem using only Mathlib and the three definitions it needs
(`N`, `Statement`, `MRSTT`), with the proof left as `sorry`. `comparator.json` tells
`lake comparator` to check that `Singmaster.statement_of_mrstt` in the module `Singmaster`
proves exactly this statement, using only `propext`, `Quot.sound` and `Classical.choice`:

```sh
lake comparator      # needs bubblewrap (`bwrap`) on PATH; exit code 0 means accepted
```

So to trust the result you only need to read `Challenge.lean`. Its three definitions must stay
identical to the first three declarations of `Singmaster/Basic.lean`, in the same order. Lean
shares auxiliary proofs (for numerals such as `3 : ℝ`) with earlier declarations, so any other
order produces different terms.

## Layout

The modules follow the sections of the paper. All declarations are in the namespace
`Singmaster`.

| Paper | Module | Main declarations |
|---|---|---|
| §1: statements, (1.2); Theorem 2.3 | `Singmaster/Basic.lean` | `N`, `halfSolutions`, `a₀`, `Statement`, `MainBound`, `FixedKBound`, `MRSTT`, `N_le_two_mul_card_halfSolutions` |
| Lemma 2.1 (Stirling's formula) | `Singmaster/Stirling/` | `StirlingFormula`, `stirlingFormula` |
| Lemma 2.2 (Bernoulli polynomials) | `Singmaster/Bernoulli.lean` | `powSumPoly_eval_nat`, `bernC_eval_norm_le` |
| §3, Proposition 3.1 | `Singmaster/Interpolation/` | `InterpolatingFunction`, `interpolatingFunction`, `analytic_fixed_point` |
| §4, Proposition 4.1 | `Singmaster/Determinant/` | `solutions_on_curve`, `interpolation_det_le` |
| §5, Lemma 5.1 | `Singmaster/ExpPoly/` | `expPoly_bound` |
| §6, Proposition 6.1 | `Singmaster/ZeroEstimate/` | `zero_estimate`, `taylor_trunc`, `card_zeros_le_of_jensen` |
| §7, Lemma 7.1 | `Singmaster/FixedK/LargeM.lean` | `card_halfSolutions_large_le` |
| §7, Lemma 7.2 | `Singmaster/FixedK/Window.lean` | `ct_window`, `ct_delta3`, `ct_delta5` |
| §7, Theorem 1.3 | `Singmaster/FixedK/Main.lean` | `ct_block`, `ct_middle`, `ct_final`, `fixedKBound_of_mrstt` |
| §8, Theorem 1.2 | `Singmaster/MainBound.lean` | `log_a₀_bound`, `main_pointwise`, `mainBound_of_fixedKBound`, `statement_of_mainBound` |
| Main theorem | `Singmaster.lean` | `statement_of_mrstt` |

Section 9 of the paper describes this correspondence in more detail.

## Notes on the formal statements

- `N t` is defined with `Set.ncard`. For `t ≤ 1` the set of solutions is infinite, so `N t` takes
  the junk value `0`. This does not affect an asymptotic statement. For `t ≥ 2` the set is finite
  and `N t` is the true count (`N_eq_card`).
- `halfSolutions t` is the set `Sol(t)` of the paper: the solutions with `2m ≤ n`.
- Stirling's formula is proved for the function `σ + J`, where `J` is Gudermann's series. This
  function equals `log Γ(z+1)`, but the proof never uses the Gamma function. It shows directly
  that `σ + J` is holomorphic on `Re z > 0`, equals `log m!` at every natural number `m`, and
  satisfies the bound of Lemma 2.1.
- Several results with an unspecified threshold ("for `x₀` large", "for `log log t` large") are
  stated with an existential constant, for example `∃ X, ∀ x₀ ≥ X, …`.
