import Formalism.HermitianCurvature.StatementQ

noncomputable section

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

namespace Qx1

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hz, -, -, -, -, hGGi, -, hnabs, -⟩` from `hL`. Simplify using `only [R.LevelData.m0, M.m0A, hz, hGGi, hnabs]`.
-/
theorem model_level_multiplier (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.m0 Y = M.m0A P Y := by
  obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hGGi, -, hnabs, -⟩ := hL
  simp only [R.LevelData.m0, M.m0A, hz, hGGi, hnabs]

/- English proof (translation)
Take `⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩` from `hL`. Simplify using `only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]`.
-/
theorem model_level_lowering (P : M.Par) (L : R.LevelData (M.A P) P.r) (hL : M.IsModelLevel P L) (Y : ℂ) :
    L.l0 Y = M.l0A P Y := by
  obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hGGi, hnab, -, -⟩ := hL
  simp only [R.LevelData.l0, M.l0A, hzb, hGGi, hnab]

end Qx1

/- English proof (translation)
Introduce `P L hL Y`. Establish `hm` using `Qx1.model_level_multiplier P L hL Y`. Establish `hl` using `Qx1.model_level_lowering P L hL Y`. Take `⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩` from `hL`. Simplify using `only [NFData.QQ, hm, hl, hGG, hGGi]`.

Both sides reduce to the same expression.
-/
theorem model_is_normal_form : Formalism.FourierDecayAlt.Q.ModelIsNF := by
  intro P L hL Y
  have hm := Qx1.model_level_multiplier P L hL Y
  have hl := Qx1.model_level_lowering P L hL Y
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hGG, hGGi, -, -, -⟩ := hL
  simp only [NFData.QQ, hm, hl, hGG, hGGi]
  rfl

end Formalism.FourierDecayAlt.P
