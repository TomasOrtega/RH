import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmD
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFg

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. Supply the required witnesses or components.
-/
theorem fgSl_holds : FgSl := fun _ _ _ _ _ _ _ _ _ hU hT hfg =>
  ⟨BlockFiniteGeneration.LS_fg hU hT hfg (BlockSlices.expand hU hT), BlockFiniteGeneration.RS_fg hU hT hfg (BlockSlices.expand hU hT)⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blocks_holds : Blocks := blocks_of fgSl_holds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
