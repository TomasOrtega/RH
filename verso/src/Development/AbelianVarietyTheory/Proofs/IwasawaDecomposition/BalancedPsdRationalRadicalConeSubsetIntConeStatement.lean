import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BalancedPsdRationalRadicalConeSubsetIntCone
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdConeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FBalancedPsdRationalRadicalConeSubsetIntCone.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.balancedPsdRationalRadicalCone_subset_intCone : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] [Module.Free ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X], psdCone bar X ⊆ psdCone (id : ℤ → ℤ) X := by
  first | exact @GlobalTheory.PolFan.psdCone_subset_psdCone_int | exact GlobalTheory.PolFan.psdCone_subset_psdCone_int | (intros; apply GlobalTheory.PolFan.psdCone_subset_psdCone_int <;> assumption)
