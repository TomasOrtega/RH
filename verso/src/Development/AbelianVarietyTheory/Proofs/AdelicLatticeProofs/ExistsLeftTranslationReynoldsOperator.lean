import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LeftTranslateMatrixPolyCompletelyReducibleStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsReynoldsOfCompletelyReducibleStatement
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ReynoldsLtr

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem evC_ltr (g y : Matrix ι ι ℂ) (f : MvPolynomial (ι × ι) ℂ) :
    evC (ltr g f) y = evC f (g * y) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [evC, ltr]
  | add p q hp hq =>
    simp only [evC, map_add] at hp hq ⊢
    rw [hp, hq]
  | mul_X p i hp =>
    simp only [evC, map_mul] at hp ⊢
    rw [hp]
    simp [ltr, Matrix.mul_apply]

omit [DecidableEq ι] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem isInv_iff (Γ : Set (Matrix ι ι ℂ)) (f : MvPolynomial (ι × ι) ℂ) :
    IsInv Γ f ↔ ∀ g ∈ Γ, ltr g f = f := by
  constructor
  · intro h g hg
    apply MvPolynomial.funext
    intro x
    have h1 := evC_ltr g (Matrix.of fun i j => x (i, j)) f
    rw [h g hg] at h1
    simpa [evC] using h1
  · intro h g hg y
    rw [← evC_ltr, h g hg]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem exists_isReynolds : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → SS Γ → ∃ Rey, IsReynolds Γ Rey := by
  intro ι _ _ Γ hΓ hss
  obtain ⟨Rey, h1, h2, -, -, h5, h6⟩ := GlobalTheory.T.exists_reynolds_of_completelyReducible' (MvPolynomial (ι × ι) ℂ)
    ((fun g => (ltr g).toLinearMap) '' Γ) (by
      intro U hU
      obtain ⟨U', hU', hc⟩ := GlobalTheory.T.leftTranslateMatrixPoly_completelyReducible ι Γ hΓ hss U
        (fun g hg f hf => hU _ ⟨g, hg, rfl⟩ f hf)
      refine ⟨U', ?_, hc⟩
      rintro _ ⟨g, hg, rfl⟩ f hf
      exact hU' g hg f hf)
  refine ⟨Rey, ?_, ?_, ?_, ?_⟩
  · intro f
    rw [isInv_iff]
    intro g hg
    exact h1 f _ ⟨g, hg, rfl⟩
  · intro f hf
    rw [isInv_iff] at hf
    apply h2
    rintro _ ⟨g, hg, rfl⟩
    exact hf g hg
  · intro a f ha
    rw [isInv_iff] at ha
    refine h5 (LinearMap.mulLeft ℂ a) ?_ f
    rintro _ ⟨g, hg, rfl⟩ v
    simp only [LinearMap.mulLeft_apply, AlgHom.toLinearMap_apply, map_mul, ha g hg]
  · intro U hU
    apply h6
    rintro _ ⟨g, hg, rfl⟩ f hf
    exact hU g hg f hf

end GlobalTheory.ClassFin.ReynoldsLtr
