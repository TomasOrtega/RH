import Mathlib
import GroundTheory.TateCohomology.HerbrandAbstract
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CyclicSubtraction

namespace GroundTheory.Global

open GroundTheory.GroupCoh

section Defs

variable {G M : Type*} [Group G] [AddCommGroup M]

def cycSub (ρ : Representation ℤ G M) (σ : G) : M →+ M :=
  (ρ σ - LinearMap.id).toAddMonoidHom

def normHom [Fintype G] (ρ : Representation ℤ G M) : M →+ M :=
  ρ.norm.toAddMonoidHom

noncomputable def cyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : ℚ :=
  herbrandQuotient (cycSub ρ σ) (normHom ρ)

def HasCyclicHerbrand [Fintype G] (ρ : Representation ℤ G M) (σ : G) : Prop :=
  HasHerbrandQuotient (cycSub ρ σ) (normHom ρ)

@[simp]
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cycSub_apply (ρ : Representation ℤ G M) (σ : G) (x : M) :
    cycSub ρ σ x = ρ σ x - x :=
  rfl

@[simp]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem normHom_apply [Fintype G] (ρ : Representation ℤ G M) (x : M) :
    normHom ρ x = ∑ g : G, ρ g x := by
  simp [normHom, Representation.norm, LinearMap.sum_apply]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem normHom_cycSub [Fintype G] (ρ : Representation ℤ G M) (σ : G) (x : M) :
    normHom ρ (cycSub ρ σ x) = 0 := by
  simp only [normHom, cycSub, LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply,
    LinearMap.id_apply, map_sub, Representation.norm_self_apply, sub_self]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cycSub_normHom [Fintype G] (ρ : Representation ℤ G M) (σ : G) (x : M) :
    cycSub ρ σ (normHom ρ x) = 0 := by
  simp only [normHom, cycSub, LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply,
    LinearMap.id_apply, Representation.self_norm_apply, sub_self]

end Defs

section Generator

variable {G M : Type*} [Group G] [AddCommGroup M] (ρ : Representation ℤ G M) {σ : G}

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem sub_mem_range_cycSub (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (g : G) (x : M) :
    ρ g x - x ∈ (cycSub ρ σ).range := by
  let S : Subgroup G :=
    { carrier := {g | ∀ x, ρ g x - x ∈ (cycSub ρ σ).range}
      one_mem' := fun x => by simp
      mul_mem' := fun {a b} ha hb x => by
        have : ρ (a * b) x - x = (ρ a (ρ b x) - ρ b x) + (ρ b x - x) := by
          rw [map_mul, Module.End.mul_apply]; abel
        rw [this]
        exact add_mem (ha _) (hb _)
      inv_mem' := fun {a} ha x => by
        have : ρ a⁻¹ x - x = -(ρ a (ρ a⁻¹ x) - ρ a⁻¹ x) := by
          rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
          abel
        rw [this]
        exact neg_mem (ha _) }
  have hσS : σ ∈ S := fun x => ⟨x, rfl⟩
  have : Subgroup.zpowers σ ≤ S := (Subgroup.zpowers_le).2 hσS
  exact this (hσ g) x

/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem apply_eq_of_cycSub_eq_zero (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : M}
    (hx : cycSub ρ σ x = 0) (g : G) : ρ g x = x :=
  by apply _root_.UpperTheory.Reformulated.B.CyclicSubtraction.apply_eq_of_cycSub_eq_zero <;> assumption

variable [Fintype G]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem normHom_eq_card_smul (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : M}
    (hx : cycSub ρ σ x = 0) : normHom ρ x = (Fintype.card G : ℤ) • x := by
  rw [normHom_apply, Finset.sum_congr rfl fun g _ => apply_eq_of_cycSub_eq_zero ρ hσ hx g,
    Finset.sum_const, Finset.card_univ, natCast_zsmul]

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Normalize the expressions using the abelian group laws. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_smul_sub_normHom_mem (hσ : ∀ g, g ∈ Subgroup.zpowers σ) (x : M) :
    (Fintype.card G : ℤ) • x - normHom ρ x ∈ (cycSub ρ σ).range := by
  have : (Fintype.card G : ℤ) • x - normHom ρ x = -∑ g : G, (ρ g x - x) := by
    rw [normHom_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      natCast_zsmul]
    abel
  rw [this]
  exact neg_mem (AddSubgroup.sum_mem _ fun g _ => sub_mem_range_cycSub ρ hσ g x)

end Generator

section Finiteness

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_kerModRange_of_smul_mem {A : Type*} [AddCommGroup A] [Module.Finite ℤ A]
    (f g : A →+ A) {n : ℤ} (hn : n ≠ 0) (h : ∀ x ∈ f.ker, n • x ∈ g.range) :
    Finite (KerModRange f g) := by
  have hfin : Module.Finite ℤ f.ker := by
    have : Module.Finite ℤ (LinearMap.ker f.toIntLinearMap) := inferInstance
    exact Module.Finite.equiv (R := ℤ)
      ((LinearEquiv.refl ℤ (LinearMap.ker f.toIntLinearMap)) : _ ≃ₗ[ℤ] f.ker)
  have hq : Module.Finite ℤ (KerModRange f g) :=
    Module.Finite.of_surjective
      (QuotientAddGroup.mk' (g.range.addSubgroupOf f.ker)).toIntLinearMap
      (QuotientAddGroup.mk'_surjective _)
  apply Module.finite_of_fg_torsion
  intro y
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (g.range.addSubgroupOf f.ker) y
  refine ⟨⟨n, mem_nonZeroDivisors_of_ne_zero hn⟩, ?_⟩
  show n • (QuotientAddGroup.mk' _ x : KerModRange f g) = 0
  rw [← map_zsmul, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_zsmul]
  exact h x x.2

variable {G M : Type*} [Group G] [Fintype G] [AddCommGroup M] [Module.Finite ℤ M]

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem hasCyclicHerbrand_of_finite (ρ : Representation ℤ G M) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) : HasCyclicHerbrand ρ σ := by
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_,
    finite_kerModRange_of_smul_mem _ _ hn fun x hx => ?_⟩
  · rw [← normHom_eq_card_smul ρ hσ hx]
    exact ⟨x, rfl⟩
  · have := card_smul_sub_normHom_mem ρ hσ x
    rwa [AddMonoidHom.mem_ker.1 hx, sub_zero] at this

end Finiteness

section Trivial

variable {G : Type*} [Group G] [Fintype G]

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Substitute using the available equality.

Both sides reduce to the same expression. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Proceed by induction. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cyclicHerbrand_trivial_int (σ : G) :
    cyclicHerbrand (Representation.trivial ℤ G ℤ) σ = Fintype.card G := by
  set ρ := Representation.trivial ℤ G ℤ
  have hf : cycSub ρ σ = 0 := by
    ext
    simp [ρ]
  have hg : normHom ρ = (Fintype.card G : ℤ) • AddMonoidHom.id ℤ := by
    ext
    simp [ρ, normHom_apply]
  have hn : (Fintype.card G : ℤ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1 : Nat.card (KerModRange (cycSub ρ σ) (normHom ρ)) = Fintype.card G := by
    show (normHom ρ).range.relIndex (cycSub ρ σ).ker = _
    have hr : (normHom ρ).range = AddSubgroup.zmultiples (Fintype.card G : ℤ) := by
      ext y
      simp only [hg, AddMonoidHom.mem_range, AddMonoidHom.smul_apply, AddMonoidHom.id_apply,
        AddSubgroup.mem_zmultiples_iff, smul_eq_mul]
      exact ⟨fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩,
        fun ⟨x, hx⟩ => ⟨x, by rw [← hx, mul_comm]⟩⟩
    rw [hf, AddMonoidHom.ker_zero, AddSubgroup.relIndex_top_right, hr, Int.index_zmultiples,
      Int.natAbs_natCast]
  have h2 : Nat.card (KerModRange (normHom ρ) (cycSub ρ σ)) = 1 := by
    have : Subsingleton (normHom ρ).ker := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      rw [AddMonoidHom.mem_ker, hg] at ha hb
      simp only [AddMonoidHom.smul_apply, AddMonoidHom.id_apply, smul_eq_mul,
        mul_eq_zero, hn, false_or] at ha hb
      subst ha hb
      rfl
    have : Subsingleton (KerModRange (normHom ρ) (cycSub ρ σ)) := by
      constructor
      intro a b
      induction a using QuotientAddGroup.induction_on
      induction b using QuotientAddGroup.induction_on
      congr 1
      exact Subsingleton.elim _ _
    exact Nat.card_of_subsingleton 0
  rw [cyclicHerbrand, herbrandQuotient, h1, h2, Nat.cast_one, div_one]

end Trivial

end GroundTheory.Global
