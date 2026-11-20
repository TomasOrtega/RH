import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAdmissibleIntegralBasisChangeOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FAffineEigenvalueEqOneOfBoxSumNeZero.lean&line=84#L84)
-/
theorem _root_.GlobalTheory.T.affine_eigenvalue_eq_one_of_boxSum_ne_zero : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  first | exact @GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | exact GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one | (intros; apply GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero.eigen_eq_one <;> assumption)
