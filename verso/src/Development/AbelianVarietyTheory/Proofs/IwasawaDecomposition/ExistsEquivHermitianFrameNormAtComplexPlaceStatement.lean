import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivHermitianFrameNormAtComplexPlace
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_equiv_normAt_eq_norm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsEquivHermitianFrameNormAtComplexPlace.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.exists_equiv_hermitianFrameNorm_at_complexPlace : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (A : HLat K) (W : Type) [AddCommGroup W] [Module ℂ W] (j : A.V →ₛₗ[σ] W), (∀ v, IsUnit (A.X v).det) → LinearIndependent ℂ (fun i => j (A.b i)) → Submodule.span ℂ (Set.range fun i => j (A.b i)) = ⊤ → ∃ (n : ℕ) (g : W ≃ₗ[ℂ] EuclideanSpace ℂ (Fin n)), ∀ x, Formalism.HermitianLatticesTheory.normAt A.b A.X (InfinitePlace.mk σ) x = ‖g (j x)‖ := by
  first | exact @GlobalTheory.exists_equiv_normAt_eq_norm | exact GlobalTheory.exists_equiv_normAt_eq_norm | (intros; apply GlobalTheory.exists_equiv_normAt_eq_norm <;> assumption)
