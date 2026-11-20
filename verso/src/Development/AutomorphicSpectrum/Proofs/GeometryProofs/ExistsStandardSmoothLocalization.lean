import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncChartPoint
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCoordArithOfFnField
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.SegreChart

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 GroundTheory.Heights₂.Heights.HilbertSamuel

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

omit [CharZero Ω] in

/- English proof (translation)
Rewrite using `[← Finset.prod_div_distrib, Finset.prod_eq_single k]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[Function.update_of_ne hb, div_self (hc b)]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ k) h`.
-/
theorem segre_update_ratio [DecidableEq K] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (k : K) (i : ι k) :
    (∏ k', y ⟨k', Function.update c k i k'⟩) / ∏ k', y ⟨k', c k'⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by
  rw [← Finset.prod_div_distrib, Finset.prod_eq_single k]
  · simp
  · intro b _ hb
    rw [Function.update_of_ne hb, div_self (hc b)]
  · intro h
    exact absurd (Finset.mem_univ k) h

/- English proof (translation)
Rewrite using `[← CoordArithOfFnField.ratioField_eq y (E c₀) hc]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨j, rfl⟩`. Simplify using `only [← Finset.prod_div_distrib]`.

Conclude with `prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, rfl⟩`. Rewrite using `[GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨⟨k, i⟩, rfl⟩`. Use `IntermediateField.subset_adjoin _ _ ⟨E.symm (Function.update (E c₀) k i), ?_⟩` and prove the remaining obligations. Simplify using `using segre_update_ratio y (E c₀) hc k i`.
-/
theorem adjoin_segre_eq (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    IntermediateField.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) =
      blockFnField y := by
  classical
  rw [← CoordArithOfFnField.ratioField_eq y (E c₀) hc]
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨j, rfl⟩
    simp only [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => IntermediateField.subset_adjoin _ _ ⟨⟨k, E j k⟩, rfl⟩
  · rw [GroundTheory.Heights₂.Heights.CoordinateConeArithVar.ratioField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    refine IntermediateField.subset_adjoin _ _ ⟨E.symm (Function.update (E c₀) k i), ?_⟩
    simpa using segre_update_ratio y (E c₀) hc k i

/- English proof (translation)
Take `⟨_, _, _, hdim⟩` from `hA`. Rewrite `hdim` using `[CoordArithOfFnField.dim_eq y c hc]`. Establish `h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = e`. Generalize the expression as in `(Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢`. Proceed by induction on `n using ENat.recTopCoe with`.

Consider the case `top`. It suffices to derive a contradiction. Simplify using `only [top_add] at hdim`. Normalize the coercions in `at hdim`. Consider the case `coe n`.

Normalize the coercions in `at hdim ⊢`. Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[Cardinal.toENat_eq_natCast]`. Establish `: Algebra.IsAlgebraic ℤ ℚ` using `IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)`. Rewrite using `[← h1, ← trdeg_add_eq ℤ ℚ (A := blockFnField y), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]`.
-/
theorem trdeg_blockFnField {y : (Σ k, ι k) → Ω} {e : ℕ} (hA : IsArithVar (mCoordIdeal y) (e + 1))
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) : Algebra.trdeg ℚ (blockFnField y) = e := by
  obtain ⟨_, _, _, hdim⟩ := hA
  rw [CoordArithOfFnField.dim_eq y c hc] at hdim
  have h1 : (Algebra.trdeg ℤ (blockFnField y)).toENat = e := by
    generalize (Algebra.trdeg ℤ (blockFnField y)).toENat = n at hdim ⊢
    induction n using ENat.recTopCoe with
    | top =>
      exfalso
      simp only [top_add] at hdim
      norm_cast at hdim
    | coe n =>
      norm_cast at hdim ⊢
      omega
  rw [Cardinal.toENat_eq_natCast] at h1
  have : Algebra.IsAlgebraic ℤ ℚ := IsLocalization.isAlgebraic _ (nonZeroDivisors ℤ)
  rw [← h1, ← trdeg_add_eq ℤ ℚ (A := blockFnField y), trdeg_eq_zero (R := ℤ) (A := ℚ), zero_add]

open scoped IntermediateField.algebraAdjoinAdjoin in

/- English proof (translation)
Establish `hfin : Algebra.FiniteType ℚ (Algebra.adjoin ℚ S)` using `(Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)`. Establish `h2 : Algebra.trdeg ℚ (Algebra.adjoin ℚ S) = e`. Rewrite using `[← h]`. Conclude with `(GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := ℚ) (A := Algebra.adjoin ℚ S) (IntermediateField.adjoin ℚ S)).symm`. Conclude with `GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension (GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℚ _ h2)`.
-/
theorem exists_away_of_trdeg (S : Set Ω) (hS : S.Finite) {e : ℕ}
    (h : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ S) = e) :
    ∃ s : Algebra.adjoin ℚ S, s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  have hfin : Algebra.FiniteType ℚ (Algebra.adjoin ℚ S) :=
    (Subalgebra.fg_iff_finiteType _).1 (Subalgebra.fg_def.2 ⟨S, hS, rfl⟩)
  have h2 : Algebra.trdeg ℚ (Algebra.adjoin ℚ S) = e := by
    rw [← h]
    exact (GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := ℚ) (A := Algebra.adjoin ℚ S)
      (IntermediateField.adjoin ℚ S)).symm
  exact GlobalTheory.AffinePoints.exists_ne_zero_isStandardSmoothOfRelativeDimension
    (GlobalTheory.ringKrullDim_eq_of_trdeg_eq ℚ _ h2)

/- English proof (translation)
Use `exists_away_of_trdeg _ (Set.finite_range _) ?_` and prove the remaining obligations. Rewrite using `[adjoin_segre_eq y E c₀ hc]`. Conclude with `trdeg_blockFnField hA (E c₀) hc`.
-/
theorem exists_away_standardSmooth (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ) (hA : IsArithVar (mCoordIdeal y) (e + 1)) (N : ℕ)
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1)) (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) :
    ∃ s : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), s ≠ 0 ∧
      Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away s) := by
  refine exists_away_of_trdeg _ (Set.finite_range _) ?_
  rw [adjoin_segre_eq y E c₀ hc]
  exact trdeg_blockFnField hA (E c₀) hc

end GlobalTheory.CompanionTheory.Ar.SegreChart
