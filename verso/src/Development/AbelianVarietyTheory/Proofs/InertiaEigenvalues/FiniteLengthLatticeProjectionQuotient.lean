import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthLocalizedModuleEqZeroOfNotAnnihilatorLe

open Submodule

namespace GlobalTheory

/- English proof (translation)
Establish an intermediate fact. Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Treat this case separately.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify by unfolding definitions. Substitute using the available equality. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_nonZeroDivisor_smul_mem_of_span_eq_top_finlen {O K V : Type} [CommRing O] [IsDomain O]
    [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V]
    [IsScalarTower O K V] (L : Submodule O V) (hspan : Submodule.span K (L : Set V) = ⊤) (x : V) :
    ∃ a ∈ nonZeroDivisors O, a • x ∈ L := by
  have hx : x ∈ Submodule.span K (L : Set V) := hspan ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, Submonoid.one_mem _, by simpa using hy⟩
  | zero => exact ⟨1, Submonoid.one_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨b, hb, hbz⟩ := hz
    refine ⟨a * b, Submonoid.mul_mem _ ha hb, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul a b z]
    exact L.add_mem (L.smul_mem b hay) (L.smul_mem a hbz)
  | smul c y _ hy =>
    obtain ⟨a, ha, hay⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
    dsimp only at hnd
    subst hnd
    refine ⟨a * d, Submonoid.mul_mem _ ha d.2, ?_⟩
    have key : ((d : O) : O) • (IsLocalization.mk' K n d • y) = n • y := by
      rw [← algebraMap_smul K (d : O), smul_smul, mul_comm, IsLocalization.mk'_spec,
        algebraMap_smul]
    rw [mul_smul, key, smul_comm]
    exact L.smul_mem n hay

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Consider separately whether the proposition holds or fails. Prove the second alternative. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. By extensionality, compare the relevant components.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

A detailed English derivation is pending.
-/
theorem finiteLength_projection_quotient :
    ∀ (O K V : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) (G B : Submodule K V), L.FG → Disjoint G B → Module.length O (↥(G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)) ⧸ (L ⊓ G.restrictScalars O).comap (G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O)).subtype) ≠ ⊤ ∨ ¬ (Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤) := by
  intro O K V _ _ _ _ _ _ _ _ _ _ L G B hL hdisj
  by_cases h : Submodule.span K (L : Set V) = ⊤ ∧ G ⊔ B = ⊤
  swap
  · exact Or.inr h
  left
  obtain ⟨hspan, hsup⟩ := h
  have hc : IsCompl G B := ⟨hdisj, codisjoint_iff.mpr hsup⟩
  set π : V →ₗ[O] V := (G.projection B hc).restrictScalars O
    with hπ
  set up := G.restrictScalars O ⊓ (L ⊔ B.restrictScalars O) with hup
  have hπfix : ∀ v ∈ G, π v = v := fun v hv =>
    Submodule.projection_apply_of_mem_left hc hv
  have hπzero : ∀ v ∈ B, π v = 0 := fun v hv =>
    Submodule.projection_apply_of_mem_right hc hv
  have hπG' : ∀ v : V, π v ∈ G := fun v => Submodule.projection_apply_mem hc v
  have hπB : ∀ v : V, v - π v ∈ B := by
    intro v
    have hv : v ∈ G ⊔ B := hsup ▸ Submodule.mem_top
    obtain ⟨g, hg, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hπfix g hg, hπzero b hb, add_zero, add_sub_cancel_left]
    exact hb
  have hmap : up = L.map π := by
    ext x
    constructor
    · rintro ⟨hxG, hxLB⟩
      obtain ⟨l, hl, b, hb, rfl⟩ := Submodule.mem_sup.mp hxLB
      refine ⟨l, hl, ?_⟩
      have h1 : π (l + b) = l + b := hπfix _ hxG
      have h2 : π b = 0 := hπzero b hb
      rw [map_add, h2, add_zero] at h1
      exact h1
    · rintro ⟨l, hl, rfl⟩
      refine ⟨hπG' l, ?_⟩
      have : π l = l - (l - π l) := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hl) (Submodule.mem_sup_right (hπB l))
  have hfg : up.FG := hmap ▸ hL.map π
  haveI : Module.Finite O up := Module.Finite.iff_fg.mpr hfg
  have htors : Module.IsTorsion O (↥up ⧸ (L ⊓ G.restrictScalars O).comap up.subtype) := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y =>
      obtain ⟨a, ha, hay⟩ := exists_nonZeroDivisor_smul_mem_of_span_eq_top_finlen (K := K) L hspan (y : V)
      refine ⟨⟨a, ha⟩, ?_⟩
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      refine ⟨hay, ?_⟩
      exact (G.restrictScalars O).smul_mem a y.2.1
  exact Module.length_ne_top_iff.mpr (isFiniteLength_of_isTorsion htors)

end GlobalTheory
