import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KapLat.exists_model_of_orthonormal_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsHermitianModelOfOrthonormalBasis.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)
