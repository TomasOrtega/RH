import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.AlgebraMapIntMemIntAd

noncomputable section

namespace PI.IwaMeasEx.MFI

open NumberField
open scoped TensorProduct nonZeroDivisors Pointwise
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

variable (I : AutInst)

def oH : AddSubgroup (AEf I) := (IntAf I.F I.E).toAddSubgroup

def uH (u : AEf I) : AddSubgroup (AEf I) := (oH I).map (AddMonoidHom.mulLeft u)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Rewrite using `[AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.inv_mul, one_mul]`. Conclude with `hy`. Introduce `hx`.

Use `⟨_, hx, ?_⟩` and prove the remaining obligations. Rewrite using `[AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem mem_uH_iff (u : (AEf I)ˣ) (x : AEf I) :
    x ∈ uH I u ↔ ((u⁻¹ : (AEf I)ˣ) : AEf I) * x ∈ IntAf I.F I.E := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.inv_mul, one_mul]
    exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, ← mul_assoc, Units.mul_inv, one_mul]

def aI (u : (AEf I)ˣ) : Ideal (𝓞 I.E) := Submodule.comap (Algebra.linearMap (𝓞 I.E) I.E) (cid I u)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `Submodule.map_comap_le _ _`. Introduce `e he`. Establish `h : iE I e ∈ IntAf I.F I.E`. Establish `e1 : iE I e = (u : AEf I) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I e)`.

Rewrite using `[← mul_assoc, Units.mul_inv, one_mul]`. Rewrite using `[e1]`. Conclude with `mul_mem hu he`. Take `⟨o, rfl⟩` from `mem_intOE _ h`. Conclude with `⟨o, he, rfl⟩`.
-/
theorem map_aI (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    Submodule.map (Algebra.linearMap (𝓞 I.E) I.E) (aI I u) = cid I u := by
  apply le_antisymm
  · exact Submodule.map_comap_le _ _
  · intro e he
    have h : iE I e ∈ IntAf I.F I.E := by
      have e1 : iE I e = (u : AEf I) * (((u⁻¹ : (AEf I)ˣ) : AEf I) * iE I e) := by
        rw [← mul_assoc, Units.mul_inv, one_mul]
      rw [e1]
      exact mul_mem hu he
    obtain ⟨o, rfl⟩ := mem_intOE _ h
    exact ⟨o, he, rfl⟩

/- English proof (translation)
Rewrite using `[FractionalIdeal.absNorm_eq' 1 (aI I u) (by`. Simplify using `only [coe_FI, map_aI I u hu]`. Conclude with `one_smul _ _)]`. Simplify using the standard rewrite rules.
-/
theorem absNorm_FI (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    FractionalIdeal.absNorm (FI I u) = (Ideal.absNorm (aI I u) : ℚ) := by
  rw [FractionalIdeal.absNorm_eq' 1 (aI I u) (by
    simp only [coe_FI, map_aI I u hu]
    exact one_smul _ _)]
  simp

/- English proof (translation)
Use `set S := (uH I (u : AEf I)).addSubgroupOf (oH I) with hS`. Set `ι : 𝓞 I.E →+ oH I` to `{ toFun := fun o => ⟨iE I (algebraMap (𝓞 I.E) I.E o), inclE_mem (RingHom.mem_range_self _ o)⟩ map_zero' := by ext; simp map_add' := fun a b => by ext; simp }`. Set `ψ : 𝓞 I.E →+ (oH I ⧸ S)` to `(QuotientAddGroup.mk' S).comp ι`. Establish `hmem : ∀ o : 𝓞 I.E, ψ o = 0 ↔ o ∈ aI I u`. Introduce `o`.

Use `show (QuotientAddGroup.mk' S) (ι o) = 0 ↔ _`. Rewrite using `[QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`. Use `show iE I (algebraMap (𝓞 I.E) I.E o) ∈ uH I (u : AEf I) ↔ _`. Rewrite using `[mem_uH_iff]`. Both sides reduce to the same expression.

Establish `hsurj : Function.Surjective ψ`. Introduce `q`. Take `⟨⟨x, hx⟩, rfl⟩` from `QuotientAddGroup.mk'_surjective S q`. Take `⟨N, hN, hNc, -⟩` from `mem_uO I u`. Take `⟨a, ⟨o, rfl⟩, z, hz, hxe⟩` from `IntAf_approx N hN x hx`.

Use `⟨o, ?_⟩` and prove the remaining obligations. Use `show (QuotientAddGroup.mk' S) (ι o) = (QuotientAddGroup.mk' S) ⟨x, hx⟩`. Rewrite using `[QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]`. Use `show -(iE I (algebraMap (𝓞 I.E) I.E o)) + x ∈ uH I (u : AEf I)`. Rewrite using `[mem_uH_iff]`.

Establish `e1 : -(iE I (algebraMap (𝓞 I.E) I.E o)) + x = iE I (N : I.E) * z`. Rewrite using `[hxe, map_natCast]`. Express the relevant statement in the definitionally equal form `-(iE I (algebraMap (𝓞 I.E) I.E o)) + (iE I (algebraMap (𝓞 I.E) I.E o) + (N : AEf I) * z) = _`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, ← mul_assoc]`.

Conclude with `mul_mem hNc hz`. Establish `hker : ψ.ker = (aI I u).toAddSubgroup`. Use extensionality with `o`. Rewrite using `[AddMonoidHom.mem_ker, hmem]`. Both sides reduce to the same expression.

Establish `h1 : (uH I (u : AEf I)).relIndex (oH I) = Nat.card (oH I ⧸ S)` using `rfl`. Establish `h2 : ψ.ker.index = Nat.card (oH I ⧸ S)`. Rewrite using `[AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]`. Establish `h3 : Ideal.absNorm (aI I u) = (aI I u).toAddSubgroup.index`. Rewrite using `[Ideal.absNorm_apply, Submodule.cardQuot_apply]`.

Both sides reduce to the same expression. Rewrite using `[h1, ← h2, hker, ← h3, nrmF_eq, absNorm_FI I u hu, inv_inv]`. Simplify using the standard rewrite rules.
-/
theorem relIndex_uH (u : (AEf I)ˣ) (hu : (u : AEf I) ∈ IntAf I.F I.E) :
    ((uH I (u : AEf I)).relIndex (oH I) : ℝ) = (nrmF I u)⁻¹ := by
  set S := (uH I (u : AEf I)).addSubgroupOf (oH I) with hS
  let ι : 𝓞 I.E →+ oH I :=
    { toFun := fun o => ⟨iE I (algebraMap (𝓞 I.E) I.E o), inclE_mem (RingHom.mem_range_self _ o)⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp }
  let ψ : 𝓞 I.E →+ (oH I ⧸ S) := (QuotientAddGroup.mk' S).comp ι
  have hmem : ∀ o : 𝓞 I.E, ψ o = 0 ↔ o ∈ aI I u := by
    intro o
    show (QuotientAddGroup.mk' S) (ι o) = 0 ↔ _
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    show iE I (algebraMap (𝓞 I.E) I.E o) ∈ uH I (u : AEf I) ↔ _
    rw [mem_uH_iff]
    rfl
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientAddGroup.mk'_surjective S q
    obtain ⟨N, hN, hNc, -⟩ := mem_uO I u
    obtain ⟨a, ⟨o, rfl⟩, z, hz, hxe⟩ := IntAf_approx N hN x hx
    refine ⟨o, ?_⟩
    show (QuotientAddGroup.mk' S) (ι o) = (QuotientAddGroup.mk' S) ⟨x, hx⟩
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq]
    show -(iE I (algebraMap (𝓞 I.E) I.E o)) + x ∈ uH I (u : AEf I)
    rw [mem_uH_iff]
    have e1 : -(iE I (algebraMap (𝓞 I.E) I.E o)) + x = iE I (N : I.E) * z := by
      rw [hxe, map_natCast]
      change -(iE I (algebraMap (𝓞 I.E) I.E o)) + (iE I (algebraMap (𝓞 I.E) I.E o) + (N : AEf I) * z) = _
      ring
    rw [e1, ← mul_assoc]
    exact mul_mem hNc hz
  have hker : ψ.ker = (aI I u).toAddSubgroup := by
    ext o
    rw [AddMonoidHom.mem_ker, hmem]
    rfl
  have h1 : (uH I (u : AEf I)).relIndex (oH I) = Nat.card (oH I ⧸ S) := rfl
  have h2 : ψ.ker.index = Nat.card (oH I ⧸ S) := by
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hsurj, AddSubgroup.card_top]
  have h3 : Ideal.absNorm (aI I u) = (aI I u).toAddSubgroup.index := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rfl
  rw [h1, ← h2, hker, ← h3, nrmF_eq, absNorm_FI I u hu, inv_inv]
  simp

end PI.IwaMeasEx.MFI

end
