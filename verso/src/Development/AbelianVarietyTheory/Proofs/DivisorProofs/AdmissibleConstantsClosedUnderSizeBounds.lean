import Mathlib
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleComplementTwoAlongFamilyStatement
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory

/- English proof (translation)
Introduce `𝒞 h𝒞`. Use `⟨1 / 100, by norm_num, fun eps he hle => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩`. Take `⟨K⟩` from `hK`. Use `⟨K, fun Fm _ hc _ => ?_⟩` and prove the remaining obligations.

Establish `hlt : eps < 1 / 52` using `lt_of_le_of_lt hle (by norm_num)`. Conclude with `GlobalTheory.T.admissibleComplementTwo_along_family Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2`.
-/
theorem admissibleConstants_closed_under_sizeBounds : ∀ (𝒞 : FamClass), (∀ {eps : ℝ} (Fm : FamP eps), 𝒞 Fm → TuSize Fm ∧ DGamSize Fm) →
    Closed 𝒞 (fun Fm _ => Formalism.MainNotions.WeightDegreeSizes.FamilySecondComplementInputs Fm) := by
  intro 𝒞 h𝒞
  refine ⟨1 / 100, by norm_num, fun eps he hle => ?_⟩
  have hK : Nonempty TransportedAlt := ⟨by constructor <;> exact 0⟩
  obtain ⟨K⟩ := hK
  refine ⟨K, fun Fm _ hc _ => ?_⟩
  have hlt : eps < 1 / 52 := lt_of_le_of_lt hle (by norm_num)
  exact GlobalTheory.T.admissibleComplementTwo_along_family Fm he hlt (h𝒞 Fm hc).1 (h𝒞 Fm hc).2

end GlobalTheory
