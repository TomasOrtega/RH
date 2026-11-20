import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.IdxPiWStd

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Set `φ : (ι → v.adicCompletionIntegers F) →+ M` to `{ toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩ map_zero' := by ext1; simp map_add' := fun c d => by ext1`. Simplify using `[add_smul, Finset.sum_add_distrib] }`. Establish `hφs : Function.Surjective φ`. Introduce and unpack `⟨x, hx⟩`. Take `⟨c, rfl⟩` from `(hmem x).1 hx`.

Conclude with `⟨c, rfl⟩`. Establish `hsm : ∀ d : ι → v.adicCompletionIntegers F, ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i`. Introduce `d`. Rewrite using `[Finset.smul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => smul_smul _ _ _`.

Establish `key : ((smulSub ϖ M).addSubgroupOf M).comap φ = AddSubgroup.pi Set.univ (fun _ => unifO v ϖ)`. Use extensionality with `c`. Rewrite using `[AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`. Prove the components needed by the constructor for the conclusion. Introduce `hc i _`.

Take `⟨z, hz, hze⟩` from `(mem_smulSub ϖ M _).1 hc`. Take `⟨d, rfl⟩` from `(hmem z).1 hz`. Use `⟨d i, ?_⟩` and prove the remaining obligations. Establish `e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i`. Rewrite using `[← hsm, hze]`.

Both sides reduce to the same expression. Establish `h0` using `Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i) (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])`. Conclude with `sub_eq_zero.1 (h0 i)`. Introduce `h choose d hd using fun i => h i (Set.mem_univ i)`. Use `(mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hsm]`. Use `show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hd i]`. Rewrite using `[AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]`.

Simplify using `only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]`.
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
Establish `: FiniteDimensional F E` using `Module.Finite.of_restrictScalars_finite ℚ F E`. Use `set M := Submodule.span (v.adicCompletionIntegers F) ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM`. Establish `: Module.Finite (v.adicCompletionIntegers F) M` using `Module.Finite.iff_fg.2 (b_fg v)`. Establish `: Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)` using `Module.IsTorsionFree.of_smul_eq_zero fun r x h => by`. Establish `h' : (r : Fv F v) • x = 0` using `h`.

Break down `smul_eq_zero.1 h' with h0 | h0` into its components or cases. Conclude with `Or.inl (Subtype.ext h0)`. Conclude with `Or.inr h0`. Establish `: Module.Free (v.adicCompletionIntegers F) M` using `Module.free_of_finite_type_torsion_free'`. Set `bM` to `Module.finBasis (v.adicCompletionIntegers F) M`.

Set `b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E` to `fun i => (bM i : _)`. Establish `hli0 : LinearIndependent (v.adicCompletionIntegers F) b0` using `bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)`. Establish `hli : LinearIndependent (Fv F v) b0` using `(LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0`. Establish `hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b0 i`. Introduce `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)`. Rewrite `h` using `[Submodule.coe_sum]`.

Conclude with `h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)`. Introduce and unpack `⟨c, rfl⟩`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2`. Establish `hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0)`. Establish `hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0)`.

Introduce `x hx`. Take `⟨c, rfl⟩` from `(hmem x).1 hx`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Introduce `x _`. Proceed by induction on `x using TensorProduct.induction_on with`.

Consider the case `zero => exact Submodule.zero_mem _`. Consider the case `tmul c e`. Establish `hal : IsAlgebraic ℤ e` using `IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)`. Take `⟨m, hm0, hI⟩` from `hal.exists_integral_multiple`. Establish `hmF : (m : Fv F v) ≠ 0`.

Rewrite using `[← map_intCast (algebraMap F (Fv F v))]`. Conclude with `(map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)`. Establish `e2 : inclR (F` using `F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by`. Rewrite using `[map_zsmul, Int.cast_smul_eq_zsmul]`. Establish `e3 : c ⊗ₜ[F] e = c • inclR (F` using `F) (Fv F v) e := by`.

Simplify using `[inclR, TensorProduct.smul_tmul']`. Establish `e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F` using `F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)`. Rewrite using `[e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]`. Rewrite using `[e1]`. Conclude with `Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))`.

Consider the case `add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)`. Establish `hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E`. Establish `h1` using `Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)`. Rewrite `h1` using `[Fintype.card_fin]`. Rewrite using `[← h1, Module.finrank_baseChange]`.

Use `⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩` and prove the remaining obligations. Conclude with `hli.comp _ (Fin.cast_injective _)`. Rewrite using `[show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`.

Use `⟨fun i => c (Fin.cast hrk.symm i), ?_⟩` and prove the remaining obligations. Conclude with `(Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))`. Introduce and unpack `⟨c, rfl⟩`. Use `⟨fun i => c (Fin.cast hrk i), ?_⟩` and prove the remaining obligations. Conclude with `Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)`.
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
