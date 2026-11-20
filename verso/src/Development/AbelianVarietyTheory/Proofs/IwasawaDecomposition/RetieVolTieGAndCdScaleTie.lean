import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
