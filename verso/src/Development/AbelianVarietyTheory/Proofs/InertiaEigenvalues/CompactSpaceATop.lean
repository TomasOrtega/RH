import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWeakTopologyWittTiltTensor
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZlTowerGen
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology PowerSeries.WithPiTopology
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.WeakClosed

/- English proof (translation)
Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem compactSpace_oTop {l : ℕ} [Fact l.Prime] {LL : FinExt l} {e : ℕ}
    (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)) :
    @CompactSpace ↥(OL LL) (oTop bO) := by
  letI := oTop bO
  have hi : Topology.IsInducing (bO.equivFun : ↥(OL LL) → (Fin e → ℤ_[l])) := ⟨rfl⟩
  refine ⟨?_⟩
  rw [hi.isCompact_iff, Set.image_univ_of_surjective bO.equivFun.surjective]
  exact isCompact_univ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem compactSpace_aTop : ∀ {l : ℕ} [Fact l.Prime] {K LL : FinExt l} {e : ℕ} (bO : Module.Basis (Fin e) ℤ_[l] ↥(OL LL)), letI := aTop (K := K) bO; CompactSpace (AA K LL) := by
  intro l _ K LL e bO
  letI := oTop bO
  haveI := compactSpace_oTop bO
  haveI : CompactSpace (PowerSeries ↥(OL LL)) := by
    unfold PowerSeries MvPowerSeries
    exact Pi.compactSpace
  exact Pi.compactSpace

end GlobalTheory.WeakClosed
