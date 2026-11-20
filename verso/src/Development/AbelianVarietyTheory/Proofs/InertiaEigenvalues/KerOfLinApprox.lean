import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRepStatement
open Formalism.MainNotions.N GlobalTheory.Cong GlobalTheory.PsChar

namespace GlobalTheory.Cong

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Chain the equalities or inequalities of the calculation.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

A detailed English derivation is pending.
-/
theorem ker_of_linApprox : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (a : ℕ) (r : Γ →* GL (Fin a) (PadicAlgCl l))
    (C : Set (Γ →* GL (Fin a) (PadicAlgCl l))), IsSSRep r → LinApprox r C → ∀ s : Γ, (∀ ρ ∈ C, ρ s = 1) → r s = 1 := by
  intro l _ Γ _ a r C hss hC s hs
  have htr : ∀ g, trc r (s * g) = trc r g := by
    intro g
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨t, c, ht, hb⟩ := hC (ε / 2) (by positivity)
    have hsum : ∑ ρ ∈ t, c ρ * trc ρ (s * g) = ∑ ρ ∈ t, c ρ * trc ρ g := by
      refine Finset.sum_congr rfl fun ρ hρ => ?_
      simp [trc, map_mul, hs ρ (ht hρ)]
    rw [dist_eq_norm]
    calc ‖trc r (s * g) - trc r g‖
        = ‖(trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)) - (trc r g - ∑ ρ ∈ t, c ρ * trc ρ g)‖ := by
          rw [hsum]; congr 1; ring
      _ ≤ ‖trc r (s * g) - ∑ ρ ∈ t, c ρ * trc ρ (s * g)‖ + ‖trc r g - ∑ ρ ∈ t, c ρ * trc ρ g‖ := norm_sub_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add (hb _) (hb _)
      _ = ε := by ring
  set R : Γ → Matrix (Fin a) (Fin a) (PadicAlgCl l) := fun g => ((r g : GL (Fin a) (PadicAlgCl l)) : Matrix (Fin a) (Fin a) (PadicAlgCl l)) with hR
  have hM : R s - 1 ∈ Submodule.span (PadicAlgCl l) (Set.range R) := by
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨s, rfl⟩) ?_
    have : R 1 = 1 := by simp [hR]
    rw [← this]; exact Submodule.subset_span ⟨1, rfl⟩
  have h0 := GlobalTheory.T.eq_zero_of_trace_mul_eq_zero_semisimple_rep (PadicAlgCl l) Γ a r hss (R s - 1) hM (fun g => by
    have := htr g
    simp only [trc, map_mul, Units.val_mul] at this
    rw [sub_mul, one_mul, Matrix.trace_sub]
    simpa [hR] using sub_eq_zero.2 this)
  ext i j
  have := congrFun (congrFun (sub_eq_zero.1 h0) i) j
  simpa [hR] using this

end GlobalTheory.Cong
