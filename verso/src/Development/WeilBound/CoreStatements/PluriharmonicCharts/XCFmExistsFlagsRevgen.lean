import Mathlib
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenUIsGenFam
import Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

/- English proof (translation)
Establish `hup : (Mᵀ).BlockTriangular id`. Introduce `i j hij`. Rewrite using `[Matrix.transpose_apply]`. Conclude with `hl j i hij`. Establish `hunit : IsUnit (Mᵀ).det`.

Rewrite using `[Matrix.det_of_isUpperTriangular hup]`. Simplify using `[Matrix.transpose_apply, hd]`. Use `letI : Invertible (Mᵀ) := Matrix.invertibleOfIsUnitDet _ hunit`. Establish `hup' : (Mᵀ)⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hup`. Establish `hdiag : ∀ i, (Mᵀ)⁻¹ i i = 1`.

Introduce `i`. Establish `h1 : ((Mᵀ)⁻¹ * Mᵀ) i i = 1`. Rewrite using `[Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]`. Rewrite `h1` using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Simplify `h1` using `[Matrix.transpose_apply, hd]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[hup' h, zero_mul]`. Rewrite using `[hup h, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i) h`. Establish `hrev : ∀ a b, revInv M a b = (Mᵀ)⁻¹ a.rev b.rev` using `fun a b => rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[hrev]`.

Conclude with `hdiag _`. Introduce `a b hab`. Rewrite using `[hrev]`. Conclude with `hup' (Fin.rev_lt_rev.mpr hab)`. Introduce `F hF a b`.

Establish `hmem : ∀ x y, (Mᵀ)⁻¹ x y ∈ F`. Introduce `x y`. Use `hF x.rev y.rev` as an intermediate fact. Rewrite `this` using `[hrev, Fin.rev_rev, Fin.rev_rev]`. Then use the resulting hypothesis. Establish `hdet' : IsUnit ((Mᵀ)⁻¹).det` using `Matrix.isUnit_nonsing_inv_det _ hunit`.

Use `PositivityTheory.Xgp.GenFam.inv_mem F ((Mᵀ)⁻¹) hdet' hmem b a` as an intermediate fact. Rewrite `this` using `[Matrix.nonsing_inv_nonsing_inv _ hunit, Matrix.transpose_apply]`. Then use the resulting hypothesis.
-/
private theorem revInv_unitriangular_and_mem_of_unitriangular {Ω G : Type} [Field Ω] [Field G] [Algebra Ω G] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) G) (hd : ∀ a, M a a = 1) (hl : ∀ a b, a < b → M a b = 0) :
    (∀ a, revInv M a a = 1) ∧ (∀ a b, a < b → revInv M a b = 0) ∧
      ∀ F : IntermediateField Ω G, (∀ a b, revInv M a b ∈ F) → ∀ a b, M a b ∈ F := by
  classical
  have hup : (Mᵀ).BlockTriangular id := by
    intro i j hij
    rw [Matrix.transpose_apply]
    exact hl j i hij
  have hunit : IsUnit (Mᵀ).det := by
    rw [Matrix.det_of_isUpperTriangular hup]
    simp [Matrix.transpose_apply, hd]
  letI : Invertible (Mᵀ) := Matrix.invertibleOfIsUnitDet _ hunit
  have hup' : (Mᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hup
  have hdiag : ∀ i, (Mᵀ)⁻¹ i i = 1 := by
    intro i
    have h1 : ((Mᵀ)⁻¹ * Mᵀ) i i = 1 := by
      rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa [Matrix.transpose_apply, hd] using h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hup' h, zero_mul]
      · rw [hup h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrev : ∀ a b, revInv M a b = (Mᵀ)⁻¹ a.rev b.rev := fun a b => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hrev]
    exact hdiag _
  · intro a b hab
    rw [hrev]
    exact hup' (Fin.rev_lt_rev.mpr hab)
  · intro F hF a b
    have hmem : ∀ x y, (Mᵀ)⁻¹ x y ∈ F := by
      intro x y
      have := hF x.rev y.rev
      rwa [hrev, Fin.rev_rev, Fin.rev_rev] at this
    have hdet' : IsUnit ((Mᵀ)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hunit
    have := PositivityTheory.Xgp.GenFam.inv_mem F ((Mᵀ)⁻¹) hdet' hmem b a
    rwa [Matrix.nonsing_inv_nonsing_inv _ hunit, Matrix.transpose_apply] at this

/- English proof (translation)
Introduce `Ω G _ _ _ S _ r u P _ hu`. Establish `hu'` using `hu`. Take `⟨hd, hl, -, -⟩` from `hu'`. Establish `key` using `fun s => revInv_unitriangular_and_mem_of_unitriangular (Ω := Ω) (u s) (hd s) (hl s)`. Use `PositivityTheory.Xgp.GenFam.of_gen hu ?_ ?_ ?_` and prove the remaining obligations.

Introduce `s a`. Distinguish the cases in `h : P s`. Rewrite using `[if_pos h]`. Conclude with `(key s).1 a`. Rewrite using `[if_neg h]`.

Conclude with `hd s a`. Introduce `s a b hab`. Distinguish the cases in `h : P s`. Rewrite using `[if_pos h]`. Conclude with `(key s).2.1 a b hab`.

Rewrite using `[if_neg h]`. Conclude with `hl s a b hab`. Introduce `s a b`. Establish `hsub : ∀ x y, (if P s then revInv (u s) else u s) x y ∈ IntermediateField.adjoin Ω (Set.range fun (q : (σ : S) × Fin (r σ) × Fin (r σ)) => (if P q.fst then revInv (u q.fst) else u q.fst) q.snd.1 q.snd.2)` using `fun x y => IntermediateField.subset_adjoin _ _ ⟨⟨s, x, y⟩, rfl⟩`. Distinguish the cases in `h : P s`.

Rewrite `hsub` using `[if_pos h]`. Conclude with `(key s).2.2 _ hsub a b`. Rewrite `hsub` using `[if_neg h]`. Conclude with `hsub a b`.
-/
theorem PositivityTheory.Xgp.t_c_fm_exists_flags_revgen : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  intro Ω G _ _ _ S _ r u P _ hu
  have hu' := hu
  obtain ⟨hd, hl, -, -⟩ := hu'
  have key := fun s => revInv_unitriangular_and_mem_of_unitriangular (Ω := Ω) (u s) (hd s) (hl s)
  refine PositivityTheory.Xgp.GenFam.of_gen hu ?_ ?_ ?_
  · intro s a
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).1 a
    · rw [if_neg h]
      exact hd s a
  · intro s a b hab
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).2.1 a b hab
    · rw [if_neg h]
      exact hl s a b hab
  · intro s a b
    have hsub : ∀ x y, (if P s then revInv (u s) else u s) x y ∈
        IntermediateField.adjoin Ω (Set.range fun (q : (σ : S) × Fin (r σ) × Fin (r σ)) =>
          (if P q.fst then revInv (u q.fst) else u q.fst) q.snd.1 q.snd.2) :=
      fun x y => IntermediateField.subset_adjoin _ _ ⟨⟨s, x, y⟩, rfl⟩
    by_cases h : P s
    · rw [if_pos h] at hsub
      exact (key s).2.2 _ hsub a b
    · rw [if_neg h] at hsub
      exact hsub a b
