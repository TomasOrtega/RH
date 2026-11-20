import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.PLeafIso
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalSeparation.LeafSeparation.PSepOfIso

namespace PositivityTheory.Rg.BcB.F.RS

/- English proof (translation)
Introduce `E _ _ _ N V w σ hV hσ`. Conclude with `Leaf.sepOfIso_of _ _ _ V σ (fun g x hx => hV.stable (.fin (GlobalTheory.CuspRep.locGL E N w g)) x hx) (Leaf.leafIso_of E N V w σ hV hσ)`.
-/
theorem leafMod_holds : LeafMod := by
  intro E _ _ _ N V w σ hV hσ
  exact Leaf.sepOfIso_of _ _ _ V σ (fun g x hx => hV.stable (.fin (GlobalTheory.CuspRep.locGL E N w g)) x hx) (Leaf.leafIso_of E N V w σ hV hσ)

end PositivityTheory.Rg.BcB.F.RS
