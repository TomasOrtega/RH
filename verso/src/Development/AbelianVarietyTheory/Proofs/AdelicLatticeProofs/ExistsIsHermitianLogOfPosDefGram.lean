import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_isLog_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  intro ι _ _ x hx
  have hu : IsUnit x := (Matrix.isUnit_iff_isUnit_det x).2 hx
  have hp : (xᴴ * x).PosDef :=
    Matrix.PosDef.conjTranspose_mul_self x (Matrix.mulVec_injective_iff_isUnit.2 hu)
  have hs := hp.1.spectral_theorem
  refine ⟨_, (hp.1.eigenvectorUnitary : Matrix ι ι ℂ), fun i => Real.log (hp.1.eigenvalues i), ?_, rfl, ?_⟩
  · exact (Matrix.mem_unitaryGroup_iff).1 hp.1.eigenvectorUnitary.2
  · have he : (fun i => ((Real.exp (Real.log (hp.1.eigenvalues i)) : ℝ) : ℂ)) = RCLike.ofReal ∘ hp.1.eigenvalues := by
      funext i
      rw [Real.exp_log (hp.eigenvalues_pos i)]
      rfl
    rw [he]
    exact hs

end GlobalTheory.ClassFin
