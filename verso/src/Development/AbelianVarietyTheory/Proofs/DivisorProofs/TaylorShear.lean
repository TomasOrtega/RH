import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.ThetaValues.MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConstantCoeffDpolyOfAdditiveTaylorPts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCompChainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorCoordAndEvalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TaylorPolynomialEvalAlgebraFormalPropertiesStatement
open Filter Topology

namespace GlobalTheory.PeriodFamily

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Reduce the equality to equality of the corresponding arguments.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem taylor_shear : ∀ {I : Type} [Fintype I] [DecidableEq I] {D : Type} [CommRing D] [Algebra ℂ D] (N : ℕ) (t : I → D), (∀ s : Fin (N + 1) → I, ∏ a, t (s a) = 0) → ∀ {g : ℕ} (h : (I → ℂ) × (Fin g → ℂ) → ℂ) (τ : (I → ℂ) → Fin g → ℂ) (w : Fin g → ℂ), AnalyticAt ℂ τ 0 → AnalyticAt ℂ h (0, w + τ 0) → GlobalTheory.PeriodFamily.taylor N t (fun z ↦ h (z, w + τ z)) = GlobalTheory.PeriodFamily.taylor N (Sum.elim t fun a ↦ GlobalTheory.PeriodFamily.taylor N t (fun z ↦ τ z a) - algebraMap ℂ D (τ 0 a)) (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) := by
  intro I _ _ D _ _ N t ht g h τ w hτ hh
  have hτa : ∀ a, AnalyticAt ℂ (fun z ↦ τ z a) 0 := fun a ↦ analyticAt_pi_iff.1 hτ a
  have hco : ∀ {J : Type} [Fintype J] (j : J) (x : J → ℂ), AnalyticAt ℂ (fun z : J → ℂ ↦ z j) x :=
    fun j x ↦ (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ ↦ ℂ) j).analyticAt x
  have hΦ : AnalyticAt ℂ (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 := by
    refine analyticAt_pi_iff.2 ?_
    rintro (i | a)
    · exact hco i 0
    · exact (hτa a).sub analyticAt_const
  have hΦ0 : (fun z : I → ℂ ↦ (Sum.elim z (fun a ↦ τ z a - τ 0 a) : I ⊕ Fin g → ℂ)) 0 = 0 := by
    funext k
    rcases k with i | a <;> simp
  have hH : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
      h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a))) 0 := by
    have hin : AnalyticAt ℂ (fun x : I ⊕ Fin g → ℂ ↦
        ((fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)) : (I → ℂ) × (Fin g → ℂ))) 0 := by
      refine AnalyticAt.prod (analyticAt_pi_iff.2 fun i ↦ hco _ 0) ?_
      refine analyticAt_pi_iff.2 fun a ↦ ?_
      exact (analyticAt_const (v := (w + τ 0) a)).add (hco (Sum.inr a) 0)
    refine AnalyticAt.comp_of_eq hh hin ?_
    ext <;> simp
  have key := GlobalTheory.T.taylor_comp_eq_taylor_taylor_of_analyticAt N t ht _ _ hΦ hΦ0 hH
  obtain ⟨hadd, -, hconst, -⟩ := GlobalTheory.T.taylorPolynomialEvalAlgebra_formal_properties N t
  have e1 : (fun z : I → ℂ ↦ h (z, w + τ z)) = fun z : I → ℂ ↦
      (fun x : I ⊕ Fin g → ℂ ↦ h (fun i ↦ x (Sum.inl i), w + τ 0 + fun a ↦ x (Sum.inr a)))
        (Sum.elim z (fun a ↦ τ z a - τ 0 a)) := by
    funext z
    congr 1
    ext <;> simp
  rw [e1, key]
  congr 1
  funext k
  rcases k with i | a
  · exact (GlobalTheory.T.taylor_coord_and_taylor_eval_of_prod_eq_zero N t ht).1 i
  · have := hadd (fun z ↦ τ z a) (fun _ ↦ - τ 0 a) (hτa a) analyticAt_const
    rw [hconst, map_neg] at this
    simpa [sub_eq_add_neg] using this

end GlobalTheory.PeriodFamily
