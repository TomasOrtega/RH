import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.GammaIndependence.PullRId

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace CrystallineSemistableComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

/- English proof (translation)
Substitute using the available equality. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem geomMap_eq_id {k : Type} [Field k] (Ω : Type) [Field Ω] [Algebra k Ω] {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of k)) (f : X ⟶ X) (hf : f = 𝟙 X) (h : f ≫ p = p) :
    GlobalTheory.Et.geomMap Ω p f h = 𝟙 _ := by
  subst hf
  apply pullback.hom_ext <;> simp [GlobalTheory.Et.geomMap]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pullT_id (M : Model l K) (h : 𝟙 M.X ≫ M.p = M.p) (n : ℕ) : Model.pullT (𝟙 M.X) h n = LinearMap.id := by
  unfold Model.pullT
  rw [geomMap_eq_id _ _ _ (genMap_id M h), CategoryTheory.Functor.map_id]
  exact GlobalTheory.EtC.pullHl_id l _ _ _

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem pullV_id (M : Model l K) (h : 𝟙 M.X ≫ M.p = M.p) (n : ℕ) : Model.pullV (𝟙 M.X) h n = LinearMap.id := by
  unfold Model.pullV GlobalTheory.EtC.pullHQ
  rw [geomMap_eq_id _ _ _ (genMap_id M h), CategoryTheory.Functor.map_id, GlobalTheory.EtC.pullHl_id]
  exact LinearMap.baseChange_id

end CrystallineSemistableComparison
