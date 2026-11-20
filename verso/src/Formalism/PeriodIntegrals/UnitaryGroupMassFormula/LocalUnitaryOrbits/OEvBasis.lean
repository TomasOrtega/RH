import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdxPiWStd

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Introduce a local definition for the expression. Simplify using the standard rewrite rules. Establish an intermediate fact. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

Prove the first alternative. Prove the second alternative. Establish an intermediate fact. Introduce a local definition for the expression. Introduce a local definition for the expression.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Treat this case separately.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
