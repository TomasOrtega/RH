import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral
open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

noncomputable section

namespace GlobalTheory.LieDisc.ImIndex

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def imSp (E : Type) [Field E] [NumberField E] [IsCMField E] : Submodule ℚ E where
  carrier := {a | cc a = -a}
  zero_mem' := by simp [cc]
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, cc, map_add] at ha hb ⊢; rw [ha, hb, neg_add]
  smul_mem' q a ha := by
    simp only [Set.mem_setOf_eq, cc] at ha ⊢
    rw [map_rat_smul, ha, smul_neg]

/- English proof (translation)
Unfold both sides to obtain the same proposition, which implies itself.
-/
theorem mem_imSp {a : E} : a ∈ imSp E ↔ cc a = -a := Iff.rfl

def dm (E : Type) [Field E] [NumberField E] [IsCMField E] : E →ₗ[ℚ] E where
  toFun x := x - cc x
  map_add' x y := by simp only [cc, map_add]; ring
  map_smul' q x := by simp only [cc, map_rat_smul, RingHom.id_apply, smul_sub]

/- English proof (translation)
By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions.
-/
theorem range_dm : LinearMap.range (dm E) = imSp E := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change cc (x - cc x) = -(x - cc x)
    rw [show cc (x - cc x) = cc x - cc (cc x) by simp [cc], cc_cc]; ring
  · intro hy
    refine ⟨(1 / 2 : ℚ) • y, ?_⟩
    change (1 / 2 : ℚ) • y - cc ((1 / 2 : ℚ) • y) = y
    rw [show cc ((1 / 2 : ℚ) • y) = (1 / 2 : ℚ) • cc y from map_rat_smul _ _ _, (mem_imSp).1 hy,
      smul_neg, sub_neg_eq_add, ← add_smul]
    norm_num

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem mem_ker_dm {x : E} : x ∈ LinearMap.ker (dm E) ↔ x ∈ maximalRealSubfield E := by
  rw [LinearMap.mem_ker, ← IsCMField.complexConj_eq_self_iff]
  change x - cc x = 0 ↔ _
  rw [sub_eq_zero, eq_comm]; rfl

def kerEquiv (E : Type) [Field E] [NumberField E] [IsCMField E] :
    LinearMap.ker (dm E) ≃ₗ[ℚ] maximalRealSubfield E where
  toFun x := ⟨x.1, mem_ker_dm.1 x.2⟩
  invFun y := ⟨y.1, mem_ker_dm.2 y.2⟩
  map_add' x y := rfl
  map_smul' q x := by ext; simp [Rat.smul_def]
  left_inv x := rfl
  right_inv y := rfl

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Rewrite the hypotheses and the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_imSp : Module.finrank ℚ (imSp E) = fdeg E := by
  have h := LinearMap.finrank_range_add_finrank_ker (dm E)
  rw [range_dm, (kerEquiv E).finrank_eq] at h
  have h1 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  unfold fdeg
  rw [← h1, h2] at h ⊢
  omega

instance : Module.Finite ℤ (imLat E) := by
  let f : imLat E →+ 𝓞 E :=
    { toFun := fun x => ⟨x.1, x.2.1⟩
      map_zero' := rfl
      map_add' := fun x y => rfl }
  exact Module.Finite.of_injective f.toIntLinearMap (fun x y h => Subtype.ext (congrArg Subtype.val h :))

instance : Module.Free ℤ (imLat E) := Module.free_of_finite_type_torsion_free'

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finrank_imLat : Module.finrank ℤ (imLat E) = fdeg E := by
  rw [← finrank_imSp]
  let b := Module.Free.chooseBasis ℤ (imLat E)
  let v : Module.Free.ChooseBasisIndex ℤ (imLat E) → E := fun i => (b i : E)
  have hz : LinearIndependent ℤ v :=
    b.linearIndependent.map' (imLat E).subtype.toIntLinearMap
      (LinearMap.ker_eq_bot.2 Subtype.val_injective)
  have hq : LinearIndependent ℚ v := (LinearIndependent.iff_fractionRing ℤ ℚ).1 hz
  have hspan : Submodule.span ℚ (Set.range v) = imSp E := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (b i).2.2
    · intro x hx
      have halg : IsAlgebraic ℤ x :=
        (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic x)
      obtain ⟨n, hn, hint⟩ := halg.exists_integral_multiple
      have hy : n • x ∈ imLat E := by
        refine ⟨hint, ?_⟩
        rw [mem_imSp] at hx
        simp only [cc, map_zsmul] at hx ⊢
        rw [hx, smul_neg]
      have hsum := b.sum_repr ⟨n • x, hy⟩
      have hmem : n • x ∈ Submodule.span ℚ (Set.range v) := by
        rw [show n • x = ((⟨n • x, hy⟩ : imLat E) : E) from rfl, ← hsum, AddSubgroup.val_finset_sum]
        refine Submodule.sum_mem _ fun i _ => ?_
        rw [AddSubgroup.coe_zsmul, ← Int.cast_smul_eq_zsmul ℚ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
      have hx' : x = ((n : ℚ)⁻¹) • (n • x) := by
        rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn), one_smul]
      rw [hx']
      exact Submodule.smul_mem _ _ hmem
  rw [← hspan, finrank_span_eq_card hq, Module.finrank_eq_card_chooseBasisIndex]

end GlobalTheory.LieDisc.ImIndex

open GlobalTheory.LieDisc.ImIndex in

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
-/
theorem GlobalTheory.LieDisc.relIndex_mulLeft_imLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ),
    Unr E → 1 ≤ r →
      (AddSubgroup.map (AddMonoidHom.mulLeft (r : E)) (imLat E)).relIndex (imLat E) = r ^ fdeg E := by
  intro E _ _ _ r _ _
  rw [AddSubgroup.relIndex, ← finrank_imLat, ← AddSubgroup.index_range_nsmul (imLat E) r]
  congr 1
  ext ⟨x, hx⟩
  simp only [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft,
    AddMonoidHom.mem_range, nsmulAddMonoidHom_apply]
  constructor
  · rintro ⟨y, hy, hyx⟩
    exact ⟨⟨y, hy⟩, Subtype.ext (by simp [← hyx, nsmul_eq_mul])⟩
  · rintro ⟨⟨y, hy⟩, hyx⟩
    refine ⟨y, hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa [nsmul_eq_mul] using this
