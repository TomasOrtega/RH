import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalOrderFiniteAdeles
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsTensorFiniteAdeleEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousSymmFinite
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMaximalOrderFiniteAdeles.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.exists_maximal_order_finite_adeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    ∃ (R : Subring (Af F ⊗[F] E)) (ι : (Af F ⊗[F] E) ≃+* FiniteAdeleRing (𝓞 E) E), (∀ y, y ∈ R ↔ ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (ι y P) ≤ 1) ∧
      IsCompact (R : Set (Af F ⊗[F] E)) ∧ IsOpen (R : Set (Af F ⊗[F] E)) ∧ (∀ a ∈ R, sigR (Af F) σ a ∈ R) ∧
      ∀ a : Af F ⊗[F] E, ∃ N : ℕ, N ≠ 0 ∧ (N : Af F ⊗[F] E) * a ∈ R := by
  first | exact @GlobalTheory.AdeleBaseChange.exists_integral_subring | exact GlobalTheory.AdeleBaseChange.exists_integral_subring | (intros; apply GlobalTheory.AdeleBaseChange.exists_integral_subring <;> assumption)
