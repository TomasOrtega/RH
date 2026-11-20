import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCellStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula

namespace GlobalTheory.FlagZ

/- English proof (translation)
Take `⟨w, hw⟩` from `GlobalTheory.T.flag_point_in_some_cell ι κ N a l (x (IsLocalRing.closedPoint A))`. Use `GlobalTheory.T.schubert_cell_open_immersion ι κ N a l w` as an intermediate fact. Establish `hr : Set.range x ⊆ Set.range (cell a l w)`. Introduce and unpack `_ ⟨p, rfl⟩`. Conclude with `((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open (cell a l w).isOpenEmbedding.isOpen_range hw`.

Establish `e` using `IsOpenImmersion.lift_fac (cell a l w) x hr`. Use `⟨fun τ => GeneralLinearGroup.map (Spec.preimage (IsOpenImmersion.lift (cell a l w) x hr)).hom (cellGL a l w τ), ?_⟩` and prove the remaining obligations. Rewrite using `[← spMap_flagPt]`. Conclude with `e.symm.trans (congrArg (· ≫ cell a l w) (Spec.map_preimage _).symm)`.
-/
theorem exists_eq_flagPt_of_isLocalRing (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (A : Type) [CommRing A] [IsLocalRing A] (x : Sp A ⟶ Part a l) :
    ∃ g : ι → GL (Fin N) A, x = flagPt a l g := by
  obtain ⟨w, hw⟩ := GlobalTheory.T.flag_point_in_some_cell ι κ N a l (x (IsLocalRing.closedPoint A))
  have := GlobalTheory.T.schubert_cell_open_immersion ι κ N a l w
  have hr : Set.range x ⊆ Set.range (cell a l w) := by
    rintro _ ⟨p, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint p).map x.continuous).mem_open
      (cell a l w).isOpenEmbedding.isOpen_range hw
  have e := IsOpenImmersion.lift_fac (cell a l w) x hr
  refine ⟨fun τ => GeneralLinearGroup.map (Spec.preimage (IsOpenImmersion.lift (cell a l w) x hr)).hom
    (cellGL a l w τ), ?_⟩
  rw [← spMap_flagPt]
  exact e.symm.trans (congrArg (· ≫ cell a l w) (Spec.map_preimage _).symm)

end GlobalTheory.FlagZ
