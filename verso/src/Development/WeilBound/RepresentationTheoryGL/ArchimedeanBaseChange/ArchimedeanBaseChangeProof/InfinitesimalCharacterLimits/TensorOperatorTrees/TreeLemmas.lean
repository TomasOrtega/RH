import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TrStable
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TwShift
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.TensOpMaps
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TensorOperatorTrees.InfTree

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Trees

/- English proof (translation)
Assemble the required witnesses or components as `⟨trStable, twShift, graft, infTree⟩`.
-/
theorem treeLemmas : TrStable ∧ TwShift ∧ Graft ∧ InfTree := ⟨trStable, twShift, graft, infTree⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Trees
