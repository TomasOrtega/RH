import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_integral_clopen_cover_of_smooth_field :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Sp k) [Smooth f] [QuasiCompact f], ∃ (κ : Type) (U : κ → X.Opens), ⨆ c, U c = ⊤ ∧ (Pairwise fun a b => Disjoint (U a) (U b)) ∧ ∀ c, IsIntegral (U c).toScheme ∧ IsClosedImmersion (U c).ι := by
  intro k _ X f _ _
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hopen : ∀ c : _root_.ConnectedComponents X, IsOpen ((_root_.ConnectedComponents.mk : X → _) ⁻¹' {c}) := by
    intro c
    obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    rw [connectedComponents_preimage_singleton]
    exact GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian X inferInstance x
  let U : _root_.ConnectedComponents X → X.Opens := fun c => ⟨_, hopen c⟩
  refine ⟨_root_.ConnectedComponents X, U, ?_, ?_, fun c => ?_⟩
  · rw [eq_top_iff]
    intro x _
    exact Opens.mem_iSup.2 ⟨_root_.ConnectedComponents.mk x, rfl⟩
  · intro a b hab
    rw [disjoint_iff, ← SetLike.coe_set_eq]
    ext x
    simp only [U, Opens.coe_inf, Opens.coe_mk, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff, Opens.coe_bot, Set.mem_empty_iff_false, iff_false, not_and]
    rintro rfl rfl
    exact hab rfl
  · obtain ⟨x, rfl⟩ := _root_.ConnectedComponents.surjective_coe c
    have hU : ((U (_root_.ConnectedComponents.mk x) : X.Opens) : Set X) = connectedComponent x :=
      connectedComponents_preimage_singleton
    constructor
    · haveI : ConnectedSpace (U (_root_.ConnectedComponents.mk x)).toScheme := by
        show ConnectedSpace ((U (_root_.ConnectedComponents.mk x) : Set X))
        rw [← isConnected_iff_connectedSpace, hU]
        exact isConnected_connectedComponent
      exact isIntegral_of_smooth_field_of_connectedSpace ((U (_root_.ConnectedComponents.mk x)).ι ≫ f)
    · refine IsClosedImmersion.of_isPreimmersion _ ?_
      rw [Scheme.Opens.range_ι, hU]
      exact isClosed_connectedComponent

end GlobalTheory
