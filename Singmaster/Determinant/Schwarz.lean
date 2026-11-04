module

public import Mathlib

@[expose] public section

/-!
# The Schwarz lemma for interpolation determinants

Let `φ_j` (`j ∈ ι`, `D = #ι`) be holomorphic on `|z - c| ≤ R` with `|φ_j| ≤ B_j` there, and let
`z_i` (`i ∈ ι`) lie in `|z - c| ≤ r`, where `0 < r ≤ R`. Then
`|det [φ_j(z_i)]| ≤ D! (r/R)^{D(D-1)/2} ∏_j B_j` (`interpolation_det_le`). This is the form
used in the proof of Proposition 4.1.
-/

open Metric

namespace Singmaster

/-- Sum of a finset of naturals of size `q` is at least `q(q-1)/2` (doubled form). -/
lemma schwarz_finset_nat_sum (T : Finset ℕ) : T.card * (T.card - 1) ≤ 2 * ∑ x ∈ T, x := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | insert a s ha ih =>
    have hnot : a ∉ s := fun h => lt_irrefl a (ha a h)
    have hcard : s.card ≤ a := by
      have : s ⊆ Finset.range a := fun x hx => Finset.mem_range.2 (ha x hx)
      simpa using Finset.card_le_card this
    rw [Finset.card_insert_of_notMem hnot, Finset.sum_insert hnot]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm] at ih hcard ⊢
      simp only [Nat.add_sub_cancel] at ih ⊢
      nlinarith

/-- Combinatorial heart: if `k` is injective on the indices where it is `< D = #ι`,
then `∑ k ≥ D(D-1)/2`. -/
lemma schwarz_sum_ge {ι : Type*} [Fintype ι] (k : ι → ℕ)
    (hk : ∀ j j', j ≠ j' → k j = k j' → Fintype.card ι ≤ k j) :
    Fintype.card ι * (Fintype.card ι - 1) / 2 ≤ ∑ j, k j := by
  classical
  set D := Fintype.card ι with hD
  set S := Finset.univ.filter (fun j => k j < D) with hS
  set S' := Finset.univ.filter (fun j => ¬ k j < D) with hS'
  have hinj : Set.InjOn k S := by
    intro j hj j' hj' hjj'
    by_contra hne
    have := hk j j' hne hjj'
    simp [hS] at hj
    omega
  have hsplit : ∑ j, k j = ∑ j ∈ S, k j + ∑ j ∈ S', k j :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have himg : ∑ j ∈ S, k j = ∑ x ∈ S.image k, x := (Finset.sum_image (f := fun x => x) hinj).symm
  have hcardimg : (S.image k).card = S.card := Finset.card_image_of_injOn hinj
  have h1 := schwarz_finset_nat_sum (S.image k)
  rw [hcardimg, ← himg] at h1
  have h2 : S'.card * D ≤ ∑ j ∈ S', k j := by
    have := Finset.card_nsmul_le_sum S' k D (fun j hj => by simp [hS'] at hj; omega)
    simpa using this
  have hcard : S.card + S'.card = D := by
    rw [hS, hS', Finset.card_filter_add_card_filter_not]; simp [hD]
  apply Nat.div_le_of_le_mul
  rw [hsplit]
  set q := S.card
  set p := S'.card
  set A := ∑ j ∈ S, k j
  set B := ∑ j ∈ S', k j
  rcases Nat.eq_zero_or_pos q with hq | hq
  · rw [hq] at hcard
    have : D * (D - 1) ≤ D * D := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  · obtain ⟨m, hm⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
    rw [hm] at h1 hcard
    simp only [Nat.add_sub_cancel] at h1
    have he : D = m + p + 1 := by omega
    rw [he]
    simp only [Nat.add_sub_cancel]
    rw [he] at h2
    nlinarith

/-- Iterated `dslope`. -/
noncomputable def schwarz_iter (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ → ℂ :=
  (fun g => dslope g c)^[n] f

lemma schwarz_iter_succ (f : ℂ → ℂ) (c : ℂ) (n : ℕ) :
    schwarz_iter f c (n + 1) = dslope (schwarz_iter f c n) c := by
  simp [schwarz_iter, Function.iterate_succ_apply']

lemma schwarz_iter_diff {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall c R)) (n : ℕ) :
    DifferentiableOn ℂ (schwarz_iter f c n) (closedBall c R) := by
  induction n with
  | zero => simpa [schwarz_iter] using hf
  | succ n ih =>
    rw [schwarz_iter_succ]
    exact (Complex.differentiableOn_dslope (closedBall_mem_nhds c hR)).2 ih

lemma schwarz_taylor (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (u : ℂ) :
    f u = ∑ n ∈ Finset.range N, schwarz_iter f c n c * (u - c) ^ n +
      (u - c) ^ N * schwarz_iter f c N u := by
  induction N with
  | zero => simp [schwarz_iter]
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, schwarz_iter_succ]
    have := sub_smul_dslope (schwarz_iter f c N) c u
    rw [smul_eq_mul] at this
    rw [pow_succ]
    linear_combination (-(u - c) ^ N) * this

/-- Multilinear expansion of a determinant whose columns are finite sums. -/
lemma schwarz_det_sum_expand {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*}
    (t : Finset κ) (f : ι → ι → κ → ℂ) :
    (Matrix.of fun i j => ∑ n ∈ t, f i j n).det =
      ∑ k ∈ Fintype.piFinset (fun _ : ι => t), (Matrix.of fun i j => f i j (k j)).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  simp_rw [Finset.prod_univ_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Leibniz bound for a determinant with column bounds. -/
lemma schwarz_det_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (B : ι → ℝ)
    (hM : ∀ i j, ‖M i j‖ ≤ B j) :
    ‖M.det‖ ≤ (Fintype.card ι).factorial * ∏ j, B j := by
  have hB0 : ∀ j, 0 ≤ B j := fun j => (norm_nonneg _).trans (hM j j)
  rw [Matrix.det_apply']
  calc ‖∑ σ : Equiv.Perm ι, (Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i‖
      ≤ ∑ σ : Equiv.Perm ι, ‖(Equiv.Perm.sign σ : ℂ) * ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ j, B j := by
        apply Finset.sum_le_sum
        intro σ _
        have hs : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
        rw [norm_mul, hs, one_mul, norm_prod]
        exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hM _ _)
    _ = (Fintype.card ι).factorial * ∏ j, B j := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

/-- Differentiability of a determinant of differentiable entries. -/
lemma schwarz_det_diff {ι : Type*} [Fintype ι] [DecidableEq ι] (M : ι → ι → ℂ → ℂ) (S : Set ℂ)
    (hM : ∀ i j, DifferentiableOn ℂ (M i j) S) :
    DifferentiableOn ℂ (fun ζ => (Matrix.of fun i j => M i j ζ).det) S := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  apply DifferentiableOn.fun_sum
  intro σ _
  apply DifferentiableOn.const_mul
  exact DifferentiableOn.fun_finsetProd (fun i _ => hM _ _)

/-- Maximum modulus on a disc. -/
lemma schwarz_maxmod {h : ℂ → ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hd : DifferentiableOn ℂ h (closedBall 0 ρ))
    {C : ℝ} (hC : ∀ ζ ∈ sphere (0 : ℂ) ρ, ‖h ζ‖ ≤ C) {ζ : ℂ} (hζ : ζ ∈ closedBall (0 : ℂ) ρ) :
    ‖h ζ‖ ≤ C := by
  have hcl : closure (ball (0 : ℂ) ρ) = closedBall 0 ρ := closure_ball 0 hρ.ne'
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball (0 : ℂ) ρ) isBounded_ball
  · apply DifferentiableOn.diffContOnCl
    rwa [hcl]
  · intro z hz
    rw [frontier_ball 0 hρ.ne'] at hz
    exact hC z hz
  · rwa [hcl]

/-- The determinant of a matrix whose columns are expanded in powers of `ζ` with low-order
parts all proportional to a common column vanishes to order `D(D-1)/2` at `ζ = 0`. -/
lemma schwarz_det_factor {ι : Type*} [Fintype ι] [DecidableEq ι] (α : ι → ℕ → ℂ)
    (N : ι → ι → ℕ → ℂ → ℂ) (S : Set ℂ)
    (hcol : ∀ i j j' n ζ, n < Fintype.card ι → N i j n ζ = N i j' n ζ)
    (hdiff : ∀ i j n, DifferentiableOn ℂ (N i j n) S) :
    ∃ h : ℂ → ℂ, DifferentiableOn ℂ h S ∧ ∀ ζ,
      (Matrix.of fun i j => ∑ n ∈ Finset.range (Fintype.card ι + 1),
          ζ ^ n * (α j n * N i j n ζ)).det =
        ζ ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) * h ζ := by
  set D := Fintype.card ι with hD
  set W := D * (D - 1) / 2 with hW
  let T : (ι → ℕ) → ℂ → ℂ := fun k ζ => (Matrix.of fun i j => N i j (k j) ζ).det
  have hT0 : ∀ k ζ, (∃ j j', j ≠ j' ∧ k j = k j' ∧ k j < D) → T k ζ = 0 := by
    rintro k ζ ⟨j, j', hne, hkj, hlt⟩
    apply Matrix.det_zero_of_column_eq hne
    intro l
    simp only [Matrix.of_apply]
    rw [← hkj]
    exact hcol l j j' (k j) ζ hlt
  have hgood : ∀ k : ι → ℕ, ¬ (∃ j j', j ≠ j' ∧ k j = k j' ∧ k j < D) → W ≤ ∑ j, k j := by
    intro k hk
    apply schwarz_sum_ge
    intro j j' hne hkj
    by_contra hlt
    exact hk ⟨j, j', hne, hkj, by omega⟩
  refine ⟨fun ζ => ∑ k ∈ Fintype.piFinset (fun _ : ι => Finset.range (D + 1)),
      ζ ^ (∑ j, k j - W) * ((∏ j, α j (k j)) * T k ζ), ?_, ?_⟩
  · apply DifferentiableOn.fun_sum
    intro k _
    apply DifferentiableOn.mul
    · exact (differentiable_id.pow _).differentiableOn
    · apply DifferentiableOn.const_mul
      exact schwarz_det_diff (fun i j => N i j (k j)) S (fun i j => hdiff _ _ _)
  · intro ζ
    rw [schwarz_det_sum_expand, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    have hM : (Matrix.of fun i j => ζ ^ k j * (α j (k j) * N i j (k j) ζ)) =
        Matrix.of fun i j => (ζ ^ k j * α j (k j)) *
          (Matrix.of fun i j => N i j (k j) ζ) i j := by
      ext i j; simp [mul_assoc]
    rw [hM, Matrix.det_mul_row, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    change ζ ^ (∑ j, k j) * (∏ j, α j (k j)) * T k ζ = _
    by_cases hb : ∃ j j', j ≠ j' ∧ k j = k j' ∧ k j < D
    · rw [hT0 k ζ hb]; simp
    · have hle := hgood k hb
      conv_lhs => rw [← Nat.add_sub_cancel' hle, pow_add]
      ring

/-- **The Schwarz lemma for interpolation determinants.** -/
theorem interpolation_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → ℂ → ℂ) (c : ℂ) {R r : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hφ : ∀ j, DifferentiableOn ℂ (φ j) (closedBall c R))
    (B : ι → ℝ) (hB : ∀ j, ∀ z ∈ closedBall c R, ‖φ j z‖ ≤ B j)
    (z : ι → ℂ) (hz : ∀ i, z i ∈ closedBall c r) :
    ‖(Matrix.of fun i j => φ j (z i)).det‖ ≤
      (Fintype.card ι).factorial * (r / R) ^ (Fintype.card ι * (Fintype.card ι - 1) / 2) *
        ∏ j, B j := by
  set D := Fintype.card ι with hD
  set W := D * (D - 1) / 2 with hW
  have hR : 0 < R := hr.trans_le hrR
  set ρ := R / r with hρdef
  have hρ : 0 < ρ := div_pos hR hr
  have hρ1 : 1 ≤ ρ := (one_le_div hr).2 hrR
  set w : ι → ℂ := fun i => z i - c with hwdef
  have hw : ∀ i, ‖w i‖ ≤ r := fun i => by
    have := hz i
    rwa [mem_closedBall, dist_eq_norm] at this
  have hmaps : ∀ i, ∀ ζ ∈ closedBall (0 : ℂ) ρ, c + ζ * w i ∈ closedBall c R := by
    intro i ζ hζ
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_mul]
    have : ‖ζ‖ ≤ ρ := by simpa using hζ
    calc ‖ζ‖ * ‖w i‖ ≤ ρ * r := mul_le_mul this (hw i) (norm_nonneg _) hρ.le
      _ = R := by rw [hρdef]; field_simp
  let ψ : ι → ℂ → ℂ := fun j => schwarz_iter (φ j) c D
  let a : ι → ℕ → ℂ := fun j n => schwarz_iter (φ j) c n c
  let α : ι → ℕ → ℂ := fun j n => if n < D then a j n else 1
  let N : ι → ι → ℕ → ℂ → ℂ := fun i j n ζ =>
    if n < D then w i ^ n else w i ^ D * ψ j (c + ζ * w i)
  have hcol : ∀ i j j' n ζ, n < D → N i j n ζ = N i j' n ζ := by
    intro i j j' n ζ hn
    simp [N, hn]
  have hdiff : ∀ i j n, DifferentiableOn ℂ (N i j n) (closedBall 0 ρ) := by
    intro i j n
    by_cases hn : n < D
    · simp only [N, hn, ↓reduceIte]
      exact differentiableOn_const _
    · simp only [N, hn, ↓reduceIte]
      apply DifferentiableOn.const_mul
      refine (schwarz_iter_diff hR (hφ j) D).comp ?_ (fun ζ hζ => hmaps i ζ hζ)
      exact ((differentiable_const c).add (differentiable_id.mul_const _)).differentiableOn
  obtain ⟨h, hhd, hgh⟩ := schwarz_det_factor α N (closedBall 0 ρ) hcol hdiff
  rw [← hD, ← hW] at hgh
  have hg : ∀ ζ, (Matrix.of fun i j => φ j (c + ζ * w i)).det = ζ ^ W * h ζ := by
    intro ζ
    rw [← hgh ζ]
    congr 1
    ext i j
    simp only [Matrix.of_apply]
    rw [schwarz_taylor (φ j) c D (c + ζ * w i), Finset.sum_range_succ, add_sub_cancel_left]
    congr 1
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mem_range] at hn
      simp only [α, N, a, hn, ↓reduceIte]
      ring_nf
    · simp only [α, N, ψ, lt_irrefl, ↓reduceIte]
      ring_nf
  have hsph : ∀ ζ ∈ sphere (0 : ℂ) ρ,
      ‖h ζ‖ ≤ (D.factorial * ∏ j, B j) / ρ ^ W := by
    intro ζ hζ
    have hnorm : ‖ζ‖ = ρ := by simpa using hζ
    have hbound := schwarz_det_norm_le (Matrix.of fun i j => φ j (c + ζ * w i)) B
      (fun i j => hB j _ (hmaps i ζ (sphere_subset_closedBall hζ)))
    rw [hg ζ, norm_mul, norm_pow, hnorm] at hbound
    rw [le_div_iff₀ (pow_pos hρ W)]
    linarith
  have h1 := schwarz_maxmod hρ hhd hsph (ζ := 1) (by simpa using hρ1)
  have hdet : (Matrix.of fun i j => φ j (z i)).det = h 1 := by
    have := hg 1
    simpa [w] using this
  rw [hdet]
  calc ‖h 1‖ ≤ (D.factorial * ∏ j, B j) / ρ ^ W := h1
    _ = D.factorial * (r / R) ^ W * ∏ j, B j := by
      rw [hρdef, div_pow, div_pow]
      field_simp

end Singmaster
