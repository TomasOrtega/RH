import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem FGNullstellensatz.proof : FGNullstellensatz.Statement := by
  intro F _ D _ _ _ _ r hr
  have hJ : IsJacobsonRing D := isJacobsonRing_of_finiteType (A := F)
  have hmem : r ∈ (⊥ : Ideal D).jacobson := by
    rw [Ideal.jacobson, Submodule.mem_sInf]
    rintro m ⟨-, hm⟩
    let _ : Field (D ⧸ m) := Ideal.Quotient.field m
    have : Algebra.FiniteType F (D ⧸ m) := inferInstance
    have : Module.Finite F (D ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (D ⧸ m)
    have : Algebra.IsAlgebraic F (D ⧸ m) := inferInstance
    let ψ : (D ⧸ m) →ₐ[F] AlgebraicClosure F := IsAlgClosed.lift
    have h0 : ψ (Ideal.Quotient.mkₐ F m r) = 0 := hr (ψ.comp (Ideal.Quotient.mkₐ F m))
    have h1 : Ideal.Quotient.mkₐ F m r = 0 := (map_eq_zero_iff ψ ψ.toRingHom.injective).mp h0
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1
  rw [← Ideal.radical_eq_jacobson] at hmem
  obtain ⟨k, hk⟩ := hmem
  exact IsReduced.eq_zero r ⟨k, by simpa using hk⟩

end GroundTheory.Heights₂.Heights
