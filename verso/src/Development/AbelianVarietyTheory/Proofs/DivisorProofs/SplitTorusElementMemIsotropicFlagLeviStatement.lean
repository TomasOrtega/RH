import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusElementMemIsotropicFlagLevi
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSplitTorusElementMemIsotropicFlagLevi.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.splitTorusElement_mem_isotropicFlagLevi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ (t : Fin r → ℝ) (a : GAd σ J), (∀ i, t i ≠ 0) → IsTorusElt σ J X Y t a → a ∈ leviFlag σ J X Y d := by
  first | exact @GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | exact GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag | (intros; apply GlobalTheory.UAut.TorusLevi.torus_mem_leviFlag <;> assumption)
