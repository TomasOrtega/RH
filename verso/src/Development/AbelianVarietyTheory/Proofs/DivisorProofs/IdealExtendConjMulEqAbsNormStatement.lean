import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealExtendConjMulEqAbsNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB

open NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIdealExtendConjMulEqAbsNorm.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.idealExtend_conj_mul_eq_absNorm : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)), (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E, D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧ (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E) {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  first | exact @GlobalTheory.VacRead.conj_mul_cE_absNorm | exact GlobalTheory.VacRead.conj_mul_cE_absNorm | (intros; apply GlobalTheory.VacRead.conj_mul_cE_absNorm <;> assumption)
