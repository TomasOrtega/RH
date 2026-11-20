import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FKummerAlgebraFiniteProjectiveFaithfullyFlat.lean&line=203#L203)
-/
theorem _root_.GlobalTheory.T.kummerAlgebra_finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L] [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B), 0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) → Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  first | exact @GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | exact GlobalTheory.KummerAlg.finite_projective_faithfullyFlat | (intros; apply GlobalTheory.KummerAlg.finite_projective_faithfullyFlat <;> assumption)
