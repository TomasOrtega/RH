import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open TensorProduct

namespace GlobalTheory.Vert.Model

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem topologicalKrullDim_open_of_le_gen : ∀ (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (M : GlobalTheory.Vert.Model O) (V : M.X.Opens), V ≤ M.gen →
    (V : Set M.X).Nonempty → topologicalKrullDim (V : Set M.X) = M.relDim := by
  intro O _ _ _ M V hV hne
  refine le_antisymm ((QCoh.topologicalKrullDim_mono hV).trans_eq (topologicalKrullDim_gen O M)) ?_
  have hη : genericPoint M.X ∈ (V : Set M.X) := by
    obtain ⟨x, hx⟩ := hne
    exact VB.genericPoint_mem hx
  obtain ⟨A, _, _, _, _, _, j, _, hr, -, hA⟩ :=
    exists_chart_trdeg_eq_relDim M (V : Set M.X) V.isOpen hη
  have := IsLocalization.tensorRight (S := A) (FractionRing O) (nonZeroDivisors O)
  have hemb := j.isOpenEmbedding.isEmbedding.comp
      (PrimeSpectrum.localization_comap_isEmbedding (FractionRing O ⊗[O] A)
        (Algebra.algebraMapSubmonoid A (nonZeroDivisors O)))
  rw [← ringKrullDim_genericFibre_eq O (FractionRing O) hA,
    ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    ← topologicalKrullDim_eq_of_isEmbedding hemb rfl]
  refine QCoh.topologicalKrullDim_mono ?_
  rintro _ ⟨p, rfl⟩
  exact hr ⟨_, rfl⟩

end GlobalTheory.Vert.Model
