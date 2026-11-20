import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyCoefficientRingInvarianceStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpecHolds

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adic : Adic := adic_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem all_holds : Weights ∧ Torsion ∧ Adic := ⟨weights_holds, torsion_holds, adic⟩

end UpperTheory.Gal.TranscendenceTraces
