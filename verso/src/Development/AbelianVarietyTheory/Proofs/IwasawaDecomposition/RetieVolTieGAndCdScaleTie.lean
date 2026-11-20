import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Retie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueScaleIsScale
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VolumesAgreeAdelicOfTrueVolumeStatement

open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.Mem.Vol GlobalTheory.Mem.Per

namespace GlobalTheory.Mem

/- English proof (translation)
Introduce `D`. Use `⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩` and prove the remaining obligations. Rewrite using `[cdScaleTie_iff]`. Conclude with `GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd`.
-/
theorem retie_volTieG_and_cdScaleTie :
    ∀ D : D7, Formalism.L2.Theta.VolTieG (retie D) ∧ cdScaleTie (retie D) := by
  intro D
  refine ⟨GlobalTheory.T.volumesAgreeAdelic_of_trueVolume (retie D) (fun _ => rfl), ?_⟩
  rw [cdScaleTie_iff]
  exact GlobalTheory.Mem.Vol.ScaleExists.trueScale_isScale D.cd

end GlobalTheory.Mem
