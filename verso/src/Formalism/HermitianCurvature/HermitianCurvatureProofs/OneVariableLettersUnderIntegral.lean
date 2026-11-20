import Formalism.HermitianCurvature.HermitianCurvatureProofs.EntrywiseClassWordTransfer
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2

open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.SliceIntegralLemmas

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates

/- English proof (translation)
Use `⟨h.1 e, fun K hK hK0 => ?_⟩` and prove the remaining obligations. Take `⟨C, hC, hz⟩` from `h.2 K hK hK0`. Conclude with `⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩`.
-/
theorem good_of_goodFam {E X S : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup X]
    [NormedSpace ℝ X] {Φ : X → S → V1 E} (h : CutHB.GoodFam Φ) (e : S) : Good (fun v => Φ v e) := by
  refine ⟨h.1 e, fun K hK hK0 => ?_⟩
  obtain ⟨C, hC, hz⟩ := h.2 K hK hK0
  exact ⟨C, hC, fun v hv τ hτ => hz v hv τ hτ e⟩

end Formalism.FourierDecayAlt.P.SliceIntegralLemmas

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.SliceIntegralLemmas

/- English proof (translation)
Introduce `E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e`. Conclude with `(oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht`.
-/
theorem one_variable_letters_under_integral : CutHB.OneBTInt := by
  intro E _ _ _ X _ _ _ _ _ μ _ ℓ hℓ S _ _ κ w Φ hΦ f hf t ht e
  exact (oneBT_int (μ := μ) hℓ κ w Φ f (good_of_goodFam hΦ) (fun b τ hτ => hf b τ hτ) e).2 t ht

end Formalism.FourierDecayAlt.P
