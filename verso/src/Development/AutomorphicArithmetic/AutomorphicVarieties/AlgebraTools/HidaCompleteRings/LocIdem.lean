import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.HeckeModel
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocAbs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocChar
open IsLocalRing UpperTheory.V.Hi

/- English proof (translation)
A detailed English derivation is pending.
-/
private theorem coe_mem_smul_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    (Y : Submodule A M) (J : Ideal A) (y : Y) :
    (y : M) ∈ J • Y ↔ y ∈ J • (⊤ : Submodule A Y) :=
  (Submodule.mem_smul_top_iff J Y y).symm

/- English proof (translation)
Proceed by induction. Treat this case separately. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
private theorem restr_pow {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (n : ℕ) :
    Restr (t ^ n) (f ^ n) := by
  induction n with
  | zero => intro y; simp
  | succ n ih =>
    intro y
    rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the hypotheses and the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem mem_iSup_iff {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
    {Y : Submodule A M} {t : Module.End A Y} {f : Module.End A M} (h : Restr t f) (J : Ideal A) (y : Y) :
    (y : M) ∈ (⨆ n : ℕ, (J • Y).comap (f ^ n)) ↔ ∃ n : ℕ, (t ^ n) y ∈ J • (⊤ : Submodule A Y) := by
  have hf : ∀ x ∈ J • Y, f x ∈ J • Y := by
    intro x hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr z hz
      rw [map_smul]
      refine Submodule.smul_mem_smul hr ?_
      have := h ⟨z, hz⟩
      simp only at this
      rw [← this]
      exact (t ⟨z, hz⟩).2
    · intro a b ha hb
      rw [map_add]
      exact Submodule.add_mem _ ha hb
  have hmono : Monotone fun n : ℕ => (J • Y).comap (f ^ n) := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    rw [Submodule.mem_comap] at hx ⊢
    rw [pow_succ', Module.End.mul_apply]
    exact hf _ hx
  rw [Submodule.mem_iSup_of_directed _ hmono.directed_le]
  refine exists_congr fun n => ?_
  rw [Submodule.mem_comap, ← restr_pow h n y, coe_mem_smul_iff]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Supply the required witnesses or components. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locIdem :
    ∀ (A M ι : Type) [CommRing A] [IsCNL A] [AddCommGroup M] [Module A M] (Y : Submodule A M) [Module.Finite A Y] (op : ι → Module.End A M) (a : ι → A), CommOn Y op → ∃ e ∈ heckeAlg Y op, IsIdempotentElem e ∧ (∀ y : Y, (y : M) ∈ locPart Y op a ↔ e y = y) ∧ ∀ φ : Module.End A Y, (∀ i t, Restr t (op i) → φ * t = t * φ) → φ * e = e * φ := by
  intro A M ι _ _ _ _ Y _ op a h
  obtain ⟨T, _, _, j, t, -, hr, ht, htop, hfin⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.heckeModel A M ι Y op h
  haveI : Module.Finite A T := hfin inferInstance inferInstance
  obtain ⟨e, he, h1, h2, -, -⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs A T ι t a htop
  have hI : ∀ μ ∈ (maximalIdeal A).map (algebraMap A T), ∀ x,
      (j : T →+* Module.End A Y) μ x ∈ maximalIdeal A • (⊤ : Submodule A Y) := by
    intro μ hμ
    have hμ' : μ ∈ maximalIdeal A • (⊤ : Submodule A T) := by
      rw [Ideal.smul_top_eq_map]
      exact hμ
    intro x
    change j μ x ∈ _
    refine Submodule.smul_induction_on hμ' ?_ ?_
    · intro r hr z _
      rw [map_smul, LinearMap.smul_apply]
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro b c hb hc
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hb hc
  have hchar := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locChar A Y T ι (j : T →+* Module.End A Y) _
    (fun i => t i - algebraMap A T (a i)) e hI he h1 h2
  have hres : ∀ i, Restr (j (t i - algebraMap A T (a i))) (op i - algebraMap A _ (a i)) := by
    intro i y
    rw [map_sub, AlgHom.commutes, LinearMap.sub_apply, LinearMap.sub_apply, Submodule.coe_sub,
      ht i y, Module.algebraMap_end_apply, Module.algebraMap_end_apply, Submodule.coe_smul]
  have hmem : j e ∈ heckeAlg Y op := by
    rw [← hr]
    exact ⟨e, rfl⟩
  refine ⟨j e, hmem, he.map j, fun y => ?_, fun φ hφ => ?_⟩
  · refine Iff.trans ?_ (hchar y).symm
    unfold locPart
    rw [Submodule.mem_inf, and_iff_right y.2, Submodule.mem_iInf]
    refine forall_congr' fun i => ?_
    rw [Submodule.mem_iInf]
    refine forall_congr' fun k => ?_
    exact mem_iSup_iff (hres i) _ y
  · refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute hmem ?_
    rintro s ⟨i, hi⟩
    exact hφ i s hi
