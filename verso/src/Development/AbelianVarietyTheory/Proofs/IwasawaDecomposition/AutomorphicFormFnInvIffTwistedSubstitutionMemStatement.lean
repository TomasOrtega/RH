import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphicFormFnInvIffTwistedSubstitutionMem
import Mathlib
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
open Formalism.L2.Forms GlobalTheory.IntegralityCompare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAutomorphicFormFnInvIffTwistedSubstitutionMem.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.automorphicFormFn_inv_iff_twistedSubstitution_mem : ∀ {E ι : Type} [Field E] [Fintype ι] {n : ℕ} (emb : ι → E →+* ℂ) (M : GL (Fin n) E) (s : ι → ℤ)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (P0 : MvPolynomial (ι × Fin n × Fin n) ℂ)
    (S : AddSubgroup (MvPolynomial (ι × Fin n × Fin n) ℂ)) {Yt : Type} (e : Yt ≃ Frames G) (f : Yt → ℂ),
    (∀ z, f z = fnOf G s 1 P0 (e z)) →
    ((∃ P ∈ S, ∀ z, f z = fnOf G s (atInf emb ((M⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E)) P (e z)) ↔
      twSub emb M s P0 ∈ S) := by
  first | exact @GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | exact GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem | (intros; apply GlobalTheory.IntegralityCompare.fnOf_inv_iff_twSub_mem <;> assumption)
