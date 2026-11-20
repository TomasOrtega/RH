import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSectionOfIsIsoRestrict

namespace GlobalTheory.TorRef

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem blowProjSt : BlowProjSt := fun _ _ _ _ s J hs =>
  let ⟨X', π, hb, hp, _⟩ := GlobalTheory.ProjBlowup.exists_blowup s hs J
  ⟨X', π, hb, hp⟩

end GlobalTheory.TorRef
