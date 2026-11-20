import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliWordSumExpansion

open Formalism.FourierDecayAlt
open Formalism.REAL Formalism.QuantumDeterminants

namespace Formalism.FourierDecayAlt.P.CutMP.En

/- English proof (translation)
The claim follows from `| [], _, x, hx, hxG => he x hx hxG | X :: w, hw, x, hx, hxG => by show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp)) (rw_congr hU he w (fun Y hY => hw Y (by simp [hY])))`.
-/
theorem rw_congr {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {U : Set (B.Mat k r)}
    (hU : IsOpen U) {f₁ f₂ : B.Mat k r → E} (he : ∀ x ∈ U, x ∈ B.GV k r → f₁ x = f₂ x) :
    ∀ w : List (B.Mat k r), (∀ X ∈ w, B.inLie k r X) → ∀ x ∈ U, x ∈ B.GV k r → B.Rw w f₁ x = B.Rw w f₂ x
  | [], _, x, hx, hxG => he x hx hxG
  | X :: w, hw, x, hx, hxG => by
    show RdV X (B.Rw w f₁) x = RdV X (B.Rw w f₂) x
    exact Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.rdV_congr hU hx hxG (hw X (by simp))
      (rw_congr hU he w (fun Y hY => hw Y (by simp [hY])))

/- English proof (translation)
Introduce `k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg`. Take `⟨L, hL, hCV⟩` from `Formalism.FourierDecayAlt.P.capelli_word_sum k r Y`. Rewrite using `[hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]`. Use `congr 1`. Use `List.map_congr_left fun cw hcw => ?_` and prove the remaining obligations.

Rewrite using `[rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]`.
-/
theorem coefficient_vector_locality : CVLocal := by
  intro k r E _ _ U f₁ f₂ Y hU h₁ h₂ he g hg
  obtain ⟨L, hL, hCV⟩ := Formalism.FourierDecayAlt.P.capelli_word_sum k r Y
  rw [hCV E (U ∩ B.GV k r) f₁ h₁ g hg hg.2, hCV E (U ∩ B.GV k r) f₂ h₂ g hg hg.2]
  congr 1
  refine List.map_congr_left fun cw hcw => ?_
  rw [rw_congr hU (fun x hx hxG => he x ⟨hx, hxG⟩) cw.2 (fun X hX => ((hL cw hcw).1 X hX).1) g hg.1 hg.2]

end Formalism.FourierDecayAlt.P.CutMP.En
