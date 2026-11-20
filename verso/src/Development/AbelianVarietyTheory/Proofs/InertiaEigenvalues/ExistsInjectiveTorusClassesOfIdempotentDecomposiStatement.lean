import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectiveTorusClassesOfIdempotentDecomposi
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyDvdPowOfAevalEqZero
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitLemma.TorusPts.torus_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsInjectiveTorusClassesOfIdempotentDecomposi.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.exists_injective_torus_classes_of_idempotent_decomposition : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e : ι → B.A) (S : Finset ι) (a : K.O), K.Small a → IsPre B e S → ∀ k : ℕ, ∃ f : ({i // i ∉ S} → Fin (k + 1)) → B.T ⧸ (intUnits K.O B.A).subgroupOf B.T, Function.Injective f ∧ ∀ n, IsIntegral K.O ((((Quotient.out (f n) : B.T) : B.Aˣ)⁻¹ : B.Aˣ) * algebraMap K.O B.A a ^ k : B.A) := by
  first | exact @GlobalTheory.UnitLemma.TorusPts.torus_points | exact GlobalTheory.UnitLemma.TorusPts.torus_points | (intros; apply GlobalTheory.UnitLemma.TorusPts.torus_points <;> assumption)
