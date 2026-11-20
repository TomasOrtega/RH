import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

/- English proof (translation)
Introduce `F _ Y _ p U d M hU`. Establish `hUi : IsIrreducible (U : Set Y)` using `⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩`. Use `M.iso` as an intermediate fact. Set `g : (U : Scheme) ⟶ M.X` to `inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι`. Establish `hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X)`.

Establish `hs : Function.Surjective (inv (M.σ ∣_ U)).base` using `(inv (M.σ ∣_ U)).surjective`. Simplify using `only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq, Set.image_univ]`. Conclude with `Scheme.Opens.range_ι _`. Establish `hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X)`. Rewrite using `[← hrange, ← Set.image_univ]`.

Establish `: IrreducibleSpace (U : Scheme)` using `Subtype.irreducibleSpace hUi`. Conclude with `(IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn`. Establish `hcl : IsIrreducible (Set.univ : Set M.X)`. Rewrite using `[← M.dense.closure_eq]`. Conclude with `hopn.closure`.

Establish `: IrreducibleSpace M.X` using `irreducibleSpace_def _ |>.mpr hcl`. Establish `: Smooth M.str` using `SmoothOfRelativeDimension.smooth d _`. Conclude with `isIntegral_of_smooth_field M.str`.
-/
theorem isIntegral_of_nonempty_modif : ∀ (F : Type) [Field F] (Y : Scheme.{0}) [IsIntegral Y] (p : Y ⟶ Sp F) (U : Y.Opens) (d : ℕ)
    (M : Modif p U d), (U : Set Y).Nonempty → IsIntegral M.X := by
  intro F _ Y _ p U d M hU
  have hUi : IsIrreducible (U : Set Y) :=
    ⟨hU, (IrreducibleSpace.isIrreducible_univ Y).isPreirreducible.open_subset U.isOpen (Set.subset_univ _)⟩
  have := M.iso
  let g : (U : Scheme) ⟶ M.X := inv (M.σ ∣_ U) ≫ (M.σ ⁻¹ᵁ U).ι
  have hrange : Set.range g.base = ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    have hs : Function.Surjective (inv (M.σ ∣_ U)).base := (inv (M.σ ∣_ U)).surjective
    simp only [g, Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp, Set.range_comp, hs.range_eq,
      Set.image_univ]
    exact Scheme.Opens.range_ι _
  have hopn : IsIrreducible ((M.σ ⁻¹ᵁ U : M.X.Opens) : Set M.X) := by
    rw [← hrange, ← Set.image_univ]
    have : IrreducibleSpace (U : Scheme) := Subtype.irreducibleSpace hUi
    exact (IrreducibleSpace.isIrreducible_univ (U : Scheme)).image _ g.base.hom.continuous.continuousOn
  have hcl : IsIrreducible (Set.univ : Set M.X) := by
    rw [← M.dense.closure_eq]; exact hopn.closure
  have : IrreducibleSpace M.X := irreducibleSpace_def _ |>.mpr hcl
  have : Smooth M.str := SmoothOfRelativeDimension.smooth d _
  exact isIntegral_of_smooth_field M.str

end GlobalTheory
