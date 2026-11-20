import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.ComponentsOfD1EqZero

noncomputable section

namespace PI.UnitaryGroupMassFormula.LocJacTyp.Sd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter PI.LocJacTyp
open PI.VolStabSW.SdUniqW
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv finDim

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (AF F) ℂ)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem continuous_tr : Continuous (Algebra.trace (Fv F v) (Fv F v ⊗[F] E)) :=
  PI.VolStabSW.SdUniqW.continuous_trace_tens (F := F) (E := E) (Fv F v)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.
-/
theorem diagonal_phase_first_vector : (0 : Fv F v ⊗[F] E) ∈ D1 (E := E) v ψ := by
  intro x _; simp [psiV_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.
-/
theorem conductor_add_mem {y y' : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (hy' : y' ∈ D1 (E := E) v ψ) :
    y + y' ∈ D1 (E := E) v ψ := by
  intro x hx
  rw [mul_add, map_add, psiV_add', hy x hx, hy' x hx, mul_one]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem conductor_neg_mem {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) : -y ∈ D1 (E := E) v ψ := by
  intro x hx
  have h := psiV_neg_mul v ψ (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y))
  rw [hy x hx, mul_one] at h
  rwa [mul_neg, map_neg]

def D1sub : AddSubgroup (Fv F v ⊗[F] E) where
  carrier := D1 (E := E) v ψ
  add_mem' := conductor_add_mem v ψ
  zero_mem' := diagonal_phase_first_vector v ψ
  neg_mem' := conductor_neg_mem v ψ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem trE_mem_Aset {y : Fv F v ⊗[F] E} (hy : y ∈ D1 (E := E) v ψ) (j : Fin (Module.finrank F E)) :
    trE (E := E) v y j ∈ PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v) := by
  intro c hc
  have e : c * trE (E := E) v y j =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) ((c • bas (E := E) v j) * y) := by
    rw [trE_apply, trC_apply, smul_mul_assoc, map_smul, smul_eq_mul]
  rw [e]
  exact hy _ (smul_bas_mem v hc j)

variable (hK : OpenKer v ψ)
include hK

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conductor_isClosed : IsClosed (D1 (E := E) v ψ) := by
  have e : D1 (E := E) v ψ = ⋂ x ∈ OEv (E := E) v,
      {y | psiV F ψ v (Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (x * y)) = 1} := by
    ext y; simp [D1]
  rw [e]
  exact isClosed_biInter fun x _ => isClosed_eq ((continuous_psiV_of v ψ hK).comp
    ((continuous_tr v).comp (continuous_const.mul continuous_id))) continuous_const

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem conductor_isCompact (hnt : ∃ r, psiV F ψ v r ≠ 1) : IsCompact (D1 (E := E) v ψ) := by
  obtain ⟨y0, -, hy0⟩ := PI.OmFibreUniq.W.SdChar.Aset_bdd v (psiV F ψ v) (psiV_add' v ψ)
    (norm_psiV_of v ψ hK) hnt
  set C : Set (Fin (Module.finrank F E) → Fv F v) :=
    Set.univ.pi fun _ => (fun s => y0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v))
  have hC : IsCompact C := isCompact_univ_pi fun _ =>
    (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).image (continuous_const.mul continuous_id)
  refine (hC.image (continuous_trE_symm (E := E) v)).of_isClosed_subset (conductor_isClosed v ψ hK) ?_
  intro y hy
  refine ⟨trE (E := E) v y, fun j _ => ?_, by simp⟩
  obtain ⟨s, hs, e⟩ := hy0 _ (trE_mem_Aset v ψ hy j)
  exact ⟨s, hs, e.symm⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem conductor_mem_nhds : D1 (E := E) v ψ ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
  obtain ⟨m, w, hw, hgen⟩ := exists_gens (E := E) v
  have hA := PI.OmFibreUniq.W.SdChar.Aset_mem_nhds v (psiV F ψ v) (continuous_psiV_of v ψ hK)
    (psiV_add' v ψ) (norm_psiV_of v ψ hK)
  have hN : (⋂ k, {y : Fv F v ⊗[F] E | Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) ∈
      PI.OmFibreUniq.W.SdChar.Aset v (psiV F ψ v)}) ∈ 𝓝 (0 : Fv F v ⊗[F] E) := by
    refine Filter.iInter_mem.2 fun k => ?_
    have hc : Continuous fun y : Fv F v ⊗[F] E => Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (w k * y) :=
      (continuous_tr v).comp (continuous_const.mul continuous_id)
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hA)
  refine Filter.mem_of_superset hN fun y hy x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hy
  obtain ⟨c, hc, rfl⟩ := hgen x hx
  rw [Finset.sum_mul, map_sum, psiV_sum]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  exact hy k (c k) (hc k)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem conductor_isOpen : IsOpen (D1 (E := E) v ψ) :=
  AddSubgroup.isOpen_of_mem_nhds (D1sub (E := E) v ψ) (conductor_mem_nhds v ψ hK)

end PI.UnitaryGroupMassFormula.LocJacTyp.Sd
