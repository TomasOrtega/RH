import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.LayerGroup

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Establish `key : ∀ x : Om l, x ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l)) ↔ σ x = x`. Introduce `x`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Use `⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩` and prove the remaining obligations. Establish `hst : Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l) ≤ MulAction.stabilizer (Om l ≃ₐ[ℚ_[l]] Om l) x` using `Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)`.

Conclude with `MulAction.mem_stabilizer_iff.mp (hst hf)`. Unfold `Gj Ks`. Rewrite using `[IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf, IntermediateField.mem_fixingSubgroup_iff, ← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]`. Conclude with `and_congr Iff.rfl ⟨fun h x hx => (key x).mp (h hx), fun h x hx => (key x).mpr (h x hx)⟩`.
-/
theorem mem_layer_iff (K : FinExt l) (s : ℕ) (σ : GQ l) :
    σ ∈ Gj K s ↔ (∀ x ∈ K0 K, σ x = x) ∧ ∀ x : Om l, x ^ (l ^ s) = 1 → σ x = x := by

  have key : ∀ x : Om l,
      x ∈ IntermediateField.fixedField (Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l)) ↔ σ x = x := by
    intro x
    rw [IntermediateField.mem_fixedField_iff]
    refine ⟨fun h => h σ (Subgroup.mem_zpowers σ), fun h f hf => ?_⟩
    have hst : Subgroup.zpowers (σ : Om l ≃ₐ[ℚ_[l]] Om l) ≤
        MulAction.stabilizer (Om l ≃ₐ[ℚ_[l]] Om l) x :=
      Subgroup.zpowers_le.mpr (MulAction.mem_stabilizer_iff.mpr h)
    exact MulAction.mem_stabilizer_iff.mp (hst hf)
  unfold Gj Ks
  rw [IntermediateField.fixingSubgroup_sup, Subgroup.mem_inf,
    IntermediateField.mem_fixingSubgroup_iff, ← Subgroup.zpowers_le,
    ← IntermediateField.le_iff_le, IntermediateField.adjoin_le_iff]
  exact and_congr Iff.rfl ⟨fun h x hx => (key x).mp (h hx), fun h x hx => (key x).mpr (h x hx)⟩

/- English proof (translation)
Unfold `K0 at hx`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff K.1 τ).mp hτ x (SetLike.le_def.mp inf_le_left hx)`.
-/
private theorem absoluteGalois_apply_eq_self_of_mem_maxUnramified (K : FinExt l) {τ : GQ l} (hτ : τ ∈ GK K) {x : Om l} (hx : x ∈ K0 K) :
    τ x = x := by
  unfold K0 at hx
  exact (IntermediateField.mem_fixingSubgroup_iff K.1 τ).mp hτ x (SetLike.le_def.mp inf_le_left hx)

/- English proof (translation)
Use `⟨fun n hn g => ?_⟩` and prove the remaining obligations. Rewrite `hn`, the goal using `[Subgroup.mem_subgroupOf]`. Establish `hg : (g : GQ l) ∈ GK K` using `g.2`. Establish `hgi : ((g : GQ l))⁻¹ ∈ GK K` using `inv_mem hg`. Rewrite `hn`, the goal using `[mem_layer_iff]`.

Take `⟨h0, h1⟩` from `hn`. Use `⟨fun x hx => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x`. Rewrite using `[absoluteGalois_apply_eq_self_of_mem_maxUnramified K hgi hx, h0 x hx, absoluteGalois_apply_eq_self_of_mem_maxUnramified K hg hx]`. Express the relevant statement in the definitionally equal form `(g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x`.

Establish `hy : (((g : GQ l))⁻¹ x) ^ (l ^ s) = 1` using `by rw [← map_pow, hx, map_one]`. Rewrite using `[h1 _ hy]`. Conclude with `AlgEquiv.apply_symm_apply (g : GQ l) x`.
-/
theorem normal_layer (K : FinExt l) (s : ℕ) : ((Gj K s).subgroupOf (GK K)).Normal := by

  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hg : (g : GQ l) ∈ GK K := g.2
  have hgi : ((g : GQ l))⁻¹ ∈ GK K := inv_mem hg
  rw [mem_layer_iff] at hn ⊢
  obtain ⟨h0, h1⟩ := hn
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    rw [absoluteGalois_apply_eq_self_of_mem_maxUnramified K hgi hx, h0 x hx, absoluteGalois_apply_eq_self_of_mem_maxUnramified K hg hx]
  · change (g : GQ l) ((n : GQ l) (((g : GQ l))⁻¹ x)) = x
    have hy : (((g : GQ l))⁻¹ x) ^ (l ^ s) = 1 := by rw [← map_pow, hx, map_one]
    rw [h1 _ hy]
    exact AlgEquiv.apply_symm_apply (g : GQ l) x

/- English proof (translation)
Introduce `l _ K s h`. Establish `: IsGalois ℚ_[l] (Om l)` using `IsAlgClosure.isGalois ℚ_[l] (AlgebraicClosure ℚ_[l])`. Establish `: FiniteDimensional ℚ_[l] (Ks K s)` using `GlobalTheory.Cyc.TwistLift.finite_Ks K s`. Establish `: FiniteDimensional ℚ_[l] K.1` using `K.2`. Establish `hle : Gj K s ≤ GK K` using `IntermediateField.fixingSubgroup_le h`.

Establish `hKs : Module.finrank ℚ_[l] (Ks K s) = (Gj K s).index` using `IntermediateField.finrank_eq_fixingSubgroup_index _ (Ks K s)`. Establish `hK : Module.finrank ℚ_[l] K.1 = (GK K).index` using `IntermediateField.finrank_eq_fixingSubgroup_index _ K.1`. Establish `hmul : ((Gj K s).subgroupOf (GK K)).index * (GK K).index = (Gj K s).index` using `Subgroup.relIndex_mul_index hle`. Establish `hKpos : 0 < Module.finrank ℚ_[l] K.1` using `Module.finrank_pos`. Establish `hKspos : 0 < Module.finrank ℚ_[l] (Ks K s)` using `Module.finrank_pos`.

Establish `hidx : ((Gj K s).subgroupOf (GK K)).index ≠ 0`. Introduce `h0`. Rewrite `hmul` using `[h0, zero_mul, ← hKs]`. Use linear arithmetic over natural numbers and integers. Use `⟨normal_layer K s, ⟨hidx⟩, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(IntermediateField.fixingSubgroup_isOpen (Ks K s)).preimage continuous_subtype_val`. Rewrite using `[hKs, ← hmul, ← hK, padicValNat.mul hidx hKpos.ne']`. Use linear arithmetic over natural numbers and integers.
-/
theorem layer_group : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), K.1 ≤ Ks K s → ((Gj K s).subgroupOf (GK K)).Normal ∧ ((Gj K s).subgroupOf (GK K)).FiniteIndex ∧ IsOpen (((Gj K s).subgroupOf (GK K) : Subgroup ↥(GK K)) : Set ↥(GK K)) ∧ padicValNat l ((Gj K s).subgroupOf (GK K)).index = padicValNat l (Module.finrank ℚ_[l] ↥(Ks K s)) - padicValNat l (Module.finrank ℚ_[l] ↥K.1) := by
  intro l _ K s h
  have : IsGalois ℚ_[l] (Om l) := IsAlgClosure.isGalois ℚ_[l] (AlgebraicClosure ℚ_[l])
  have : FiniteDimensional ℚ_[l] (Ks K s) := GlobalTheory.Cyc.TwistLift.finite_Ks K s
  have : FiniteDimensional ℚ_[l] K.1 := K.2
  have hle : Gj K s ≤ GK K := IntermediateField.fixingSubgroup_le h

  have hKs : Module.finrank ℚ_[l] (Ks K s) = (Gj K s).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ (Ks K s)
  have hK : Module.finrank ℚ_[l] K.1 = (GK K).index :=
    IntermediateField.finrank_eq_fixingSubgroup_index _ K.1
  have hmul : ((Gj K s).subgroupOf (GK K)).index * (GK K).index = (Gj K s).index :=
    Subgroup.relIndex_mul_index hle
  have hKpos : 0 < Module.finrank ℚ_[l] K.1 := Module.finrank_pos
  have hKspos : 0 < Module.finrank ℚ_[l] (Ks K s) := Module.finrank_pos
  have hidx : ((Gj K s).subgroupOf (GK K)).index ≠ 0 := by
    intro h0
    rw [h0, zero_mul, ← hKs] at hmul
    omega
  refine ⟨normal_layer K s, ⟨hidx⟩, ?_, ?_⟩
  · exact (IntermediateField.fixingSubgroup_isOpen (Ks K s)).preimage continuous_subtype_val
  · rw [hKs, ← hmul, ← hK, padicValNat.mul hidx hKpos.ne']
    omega

end GlobalTheory.Cyc.LayerGroup
