import Mathlib

noncomputable section

namespace Formalism.MainNotions.N.Ln34.RankInverseBounds

open Module
open scoped Classical

variable {O V : Type*} [CommRing O] [IsDomain O] [AddCommGroup V] [Module O V]

def Inv (γ : V →ₗ[O] V) (K' P : Submodule O V) : Submodule O V :=
  P ⊓ K'.comap (γ - LinearMap.id)

abbrev InvQ (γ : V →ₗ[O] V) (K' P : Submodule O V) : Type _ :=
  ↥(Inv γ K' P) ⧸ K'.comap (Inv γ K' P).subtype

abbrev Gr (P P' : Submodule O V) : Type _ := ↥P ⧸ P'.comap P.subtype

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
private theorem mem_Inv_iff_mem_and_sub_mem {γ : V →ₗ[O] V} {K' P : Submodule O V} {x : V} :
    x ∈ Inv γ K' P ↔ x ∈ P ∧ γ x - x ∈ K' := by
  first
  | exact Iff.rfl
  | simp only [Inv, Submodule.mem_inf, Submodule.mem_comap, LinearMap.sub_apply,
      LinearMap.id_apply]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem inv_mono (γ : V →ₗ[O] V) (K' : Submodule O V) {P P' : Submodule O V} (h : P' ≤ P) :
    Inv γ K' P' ≤ Inv γ K' P := by
  intro x hx
  obtain ⟨h1, h2⟩ := mem_Inv_iff_mem_and_sub_mem.mp hx
  exact mem_Inv_iff_mem_and_sub_mem.mpr ⟨h h1, h2⟩

/- English proof (translation)
Treat this case separately. Treat this case separately. A detailed English derivation is pending.
-/
theorem rank_eq_zero_of_smul {M : Type*} [AddCommGroup M] [Module O M] (a : O) (ha : a ≠ 0)
    (h : ∀ x : M, a • x = 0) : Module.rank O M = 0 := by
  first
  | exact rank_eq_zero_iff.mpr fun x => ⟨a, ha, h x⟩
  | exact (rank_eq_zero_iff (R := O) (M := M)).mpr fun x => ⟨a, ha, h x⟩

/- English proof (translation)
Establish an intermediate fact. Introduce a local definition for the expression. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Introduce a local definition for the expression.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact. Treat this case separately.

Treat this case separately. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Treat this case separately.

Treat this case separately. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Chain the equalities or inequalities of the calculation. Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Chain the equalities or inequalities of the calculation.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem step (γ : V →ₗ[O] V) (K' : Submodule O V) (hK : ∀ x ∈ K', γ x ∈ K')
    (F0 F1 : Submodule O V) (c : O) (h10 : F1 ≤ F0) (hγ : ∀ x ∈ F0, γ x - c • x ∈ F1) :
    Module.rank O (InvQ γ K' F0) ≤ Module.rank O (InvQ γ K' F1) +
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
  have hle : Inv γ K' F1 ≤ Inv γ K' F0 := inv_mono γ K' h10
  let f : InvQ γ K' F1 →ₗ[O] InvQ γ K' F0 :=
    Submodule.mapQ (K'.comap (Inv γ K' F1).subtype)
      (K'.comap (Inv γ K' F0).subtype) (Submodule.inclusion hle) (by
        intro x hx
        simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
        exact hx)
  let π : ↥(Inv γ K' F0) →ₗ[O] InvQ γ K' F0 ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ (K'.comap (Inv γ K' F0).subtype).mkQ
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ z
    exact ⟨x, rfl⟩
  have key : ∀ x : ↥(Inv γ K' F0),
      (K'.comap (Inv γ K' F0).subtype).mkQ x ∈ LinearMap.range f → π x = 0 := by
    intro x hx
    simp only [π, LinearMap.comp_apply]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx
  have hquot : Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) ≤
      (if c = 1 then Module.rank O (Gr F0 F1) else 0) := by
    split_ifs with hc1
    · let ψ : ↥(Inv γ K' F0) →ₗ[O] Gr F0 F1 :=
        (F1.comap F0.subtype).mkQ ∘ₗ Submodule.inclusion (fun y hy => (mem_Inv_iff_mem_and_sub_mem.mp hy).1)
      have hker : LinearMap.ker ψ ≤ LinearMap.ker π := by
        intro x hx
        rw [LinearMap.mem_ker] at hx ⊢
        have hxF1 : (x : V) ∈ F1 := by
          first
          | (simp only [ψ, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
              Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx
             exact hx)
          | simpa [ψ] using hx
        apply key
        have hx1 : (x : V) ∈ Inv γ K' F1 :=
          mem_Inv_iff_mem_and_sub_mem.mpr ⟨hxF1, (mem_Inv_iff_mem_and_sub_mem.mp x.2).2⟩
        refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨x, hx1⟩, ?_⟩
        first
        | rfl
        | (simp only [f, Submodule.mapQ_apply, Submodule.mkQ_apply]; rfl)
      let g : ↥(Inv γ K' F0) ⧸ LinearMap.ker ψ →ₗ[O]
          InvQ γ K' F0 ⧸ LinearMap.range f :=
        (LinearMap.ker ψ).liftQ π hker
      have hg : Function.Surjective g := by
        intro b
        obtain ⟨a, rfl⟩ := hπ b
        exact ⟨Submodule.Quotient.mk a, rfl⟩
      calc _ ≤ Module.rank O (↥(Inv γ K' F0) ⧸ LinearMap.ker ψ) :=
            LinearMap.rank_le_of_surjective g hg
        _ = Module.rank O (LinearMap.range ψ) := ψ.quotKerEquivRange.rank_eq
        _ ≤ Module.rank O (Gr F0 F1) := Submodule.rank_le _
    · apply le_of_eq
      apply rank_eq_zero_of_smul (c - 1) (sub_ne_zero.mpr hc1)
      intro y
      obtain ⟨x, rfl⟩ := hπ y
      rw [← map_smul π]
      apply key
      obtain ⟨hxF0, hxK⟩ := mem_Inv_iff_mem_and_sub_mem.mp x.2
      have hmem : c • (x : V) - γ x ∈ Inv γ K' F1 := by
        refine mem_Inv_iff_mem_and_sub_mem.mpr ⟨?_, ?_⟩
        · rw [← neg_sub]
          exact F1.neg_mem (hγ _ hxF0)
        · have e : γ (c • (x : V) - γ x) - (c • (x : V) - γ x) = c • (γ x - x) - γ (γ x - x) := by
            simp only [map_sub, map_smul, smul_sub]
            abel
          rw [e]
          exact K'.sub_mem (K'.smul_mem c hxK) (hK _ hxK)
      refine LinearMap.mem_range.mpr ⟨Submodule.Quotient.mk ⟨_, hmem⟩, ?_⟩
      have e1 : f (Submodule.Quotient.mk ⟨_, hmem⟩) =
          (Submodule.Quotient.mk (Submodule.inclusion hle ⟨_, hmem⟩) : InvQ γ K' F0) := by
        first
        | rfl
        | simp only [f, Submodule.mapQ_apply]
      rw [e1, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
      convert K'.neg_mem hxK using 1
      simp only [map_sub, map_smul, Submodule.subtype_apply, Submodule.coe_inclusion, sub_smul,
        one_smul]
      abel
  calc Module.rank O (InvQ γ K' F0)
      = Module.rank O (InvQ γ K' F0 ⧸ LinearMap.range f) +
          Module.rank O (LinearMap.range f) := by
        exact (rank_quotient_add_rank_of_isDomain _).symm
    _ ≤ (if c = 1 then Module.rank O (Gr F0 F1) else 0) +
          Module.rank O (InvQ γ K' F1) :=
        add_le_add hquot (by
          first
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict f.surjective_rangeRestrict
          | exact LinearMap.rank_le_of_surjective f.rangeRestrict (fun y => by
              obtain ⟨x, hx⟩ := LinearMap.mem_range.mp y.2
              exact ⟨x, Subtype.ext hx⟩))
    _ = _ := add_comm _ _

end Formalism.MainNotions.N.Ln34.RankInverseBounds

end
