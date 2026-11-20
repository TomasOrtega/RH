import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicChartSmooth
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

set_option autoImplicit false

namespace GlobalTheory.LogPair

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem smooth_of_relSnc :
    ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (d : ℕ) (s : ℕ) (L : Fin s → LB X)
      (σ : ∀ i, (L i).Sec), RelSnc f d L σ → SmoothOfRelativeDimension d f := by
  intro R _ X f d s L σ h
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  choose C hC using h.chart
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension d) (fun x => (C x).U) ?_
    fun x => ?_
  · rw [← top_le_iff]
    rintro x -
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hC x⟩
  · exact GlobalTheory.ChartSmooth.smooth_of_etale f (C x).affine (C x).t (C x).etale

end GlobalTheory.LogPair
