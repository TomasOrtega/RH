import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartTrdegEqRelDim
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.Vert GlobalTheory.Vert.Model GlobalTheory.VB
open TensorProduct

namespace GlobalTheory.Vert.Model

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

/- English proof (translation)
Introduce `O _ _ _ M V hV hne`. Use `le_antisymm ((QCoh.topologicalKrullDim_mono hV).trans_eq (topologicalKrullDim_gen O M)) ?_` and prove the remaining obligations. Establish `hη : genericPoint M.X ∈ (V : Set M.X)`. Take `⟨x, hx⟩` from `hne`. Conclude with `VB.genericPoint_mem hx`.

Take `⟨A, _, _, _, _, _, j, _, hr, -, hA⟩` from `exists_chart_trdeg_eq_relDim M (V : Set M.X) V.isOpen hη`. Use `IsLocalization.tensorRight (S := A) (FractionRing O) (nonZeroDivisors O)` as an intermediate fact. Establish `hemb` using `j.isOpenEmbedding.isEmbedding.comp (PrimeSpectrum.localization_comap_isEmbedding (FractionRing O ⊗[O] A) (Algebra.algebraMapSubmonoid A (nonZeroDivisors O)))`. Rewrite using `[← ringKrullDim_genericFibre_eq O (FractionRing O) hA, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ← topologicalKrullDim_eq_of_isEmbedding hemb rfl]`. Use `QCoh.topologicalKrullDim_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `hr ⟨_, rfl⟩`.
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
