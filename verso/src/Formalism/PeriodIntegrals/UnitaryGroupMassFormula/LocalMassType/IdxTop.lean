import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IdxStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.IsClosedCongruenceSubgroup

noncomputable section

namespace PI.LocMassTypW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory NumberField
  IsDedekindDomain
open scoped TensorProduct Classical

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem congruence_subgroup_measurable : CongruenceSubgroupMeasurable := by
  intro F E _ _ _ _ _ σ n J ψ v r g P Λ T μS0 hyp
  obtain ⟨-, -, hSD, -, hg, -⟩ := hyp
  exact (PI.LocMassTypM.isClosed_congruence_subgroup σ J v Λ hSD hg P).measurableSet

/- English proof (translation)
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isOpen_uog {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (r g : ℕ) : IsOpen (UOg (E := E) v g r) := by
  rw [PI.LocMassTypU.uog_eq v g r]
  exact PI.LocMassTypU.isOpen_boxS _

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem unipotent_orbit_measurable : MeasUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI := PI.LocMassTypM.borel_tensV (E := E) v
  exact (isOpen_uog (E := E) v r g).measurableSet

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem unipotent_orbit_count : CountUOg := by
  intro F E _ _ _ _ _ v r g _
  haveI := PI.LocMassTypM.sc_tensV (E := E) v
  haveI : SecondCountableTopology (UIdx r → Fv F v ⊗[F] E) := inferInstance
  have hB : IsOpen (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := isOpen_uog v r g
  rw [← Set.countable_univ_iff]
  have hd : (Set.univ : Set ((UIdx r → Fv F v ⊗[F] E) ⧸ UOgS (E := E) v g r)).PairwiseDisjoint
      (fun q => (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹' {q}) :=
    Set.pairwiseDisjoint_fiber _ _
  refine hd.countable_of_isOpen (fun q _ => ?_) (fun q _ => ?_)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    have e : (QuotientAddGroup.mk : (UIdx r → Fv F v ⊗[F] E) → _ ⧸ UOgS (E := E) v g r) ⁻¹'
        {(QuotientAddGroup.mk x : _ ⧸ UOgS (E := E) v g r)} =
        (fun w => -x + w) ⁻¹' (UOgS (E := E) v g r : Set (UIdx r → Fv F v ⊗[F] E)) := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      rw [eq_comm, QuotientAddGroup.eq]
    rw [e]
    exact hB.preimage (continuous_const.add continuous_id)
  · obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    exact ⟨x, rfl⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem index_formula_of_lift (hL : CongruenceSubgroupLift) (hU : KUnip1) : StepIdx :=
  stepIdx_of hL hU congruence_subgroup_measurable unipotent_orbit_measurable unipotent_orbit_count

end PI.LocMassTypW
