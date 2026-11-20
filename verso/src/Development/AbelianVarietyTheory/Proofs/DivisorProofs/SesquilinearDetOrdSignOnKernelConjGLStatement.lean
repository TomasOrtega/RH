import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SesquilinearDetOrdSignOnKernelConjGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSesquilinearDetOrdSignOnKernelConjGL.lean&line=137#L137)
-/
theorem _root_.GlobalTheory.T.sesquilinearDetOrdSignOnKernel_conj_GL : ∀ (K : Type) [Field K] [Valued K (WithZero (Multiplicative ℤ))] (σ : K →+* K), (∀ x, Valued.v (σ x) = Valued.v x) → ∀ (n : ℕ) (Q : K[X]) (a k : GL (Fin n) K), sgnOn σ 1 Q (k⁻¹ * a * k).val = sgnOn σ (cT σ (k⁻¹).val * (k⁻¹).val) Q a.val := by
  first | exact @GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | exact GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj | (intros; apply GlobalTheory.UnitaryClasses.SgnConj.sgnOn_conj <;> assumption)
