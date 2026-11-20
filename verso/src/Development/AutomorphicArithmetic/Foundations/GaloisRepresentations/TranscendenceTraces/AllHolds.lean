import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `adic_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance`.
-/
theorem adic : Adic := adic_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance

/- English proof (translation)
Assemble the required witnesses or components as `⟨weights_holds, torsion_holds, adic⟩`.
-/
theorem all_holds : Weights ∧ Torsion ∧ Adic := ⟨weights_holds, torsion_holds, adic⟩

end UpperTheory.Gal.TranscendenceTraces
