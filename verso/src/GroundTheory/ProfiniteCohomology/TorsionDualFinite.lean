import Mathlib
import GroundTheory.ProfiniteCohomology.TorsionDualDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Function

namespace QZ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_setOf_nsmul_eq_zero {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) hn

noncomputable def toReal : QZ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)).comp toAddCircle.toAddMonoidHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toReal_mk (q : ℚ) : toReal (mk q) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem toReal_injective : Injective toReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := mk_surjective x
  rw [toReal_mk, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mk_eq_zero_iff]
  refine ⟨n, ?_⟩
  have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
  exact_mod_cast this

noncomputable def toComplex (x : QZ) : ℂ :=
  (AddCircle.toCircle (toReal x) : ℂ)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem toComplex_injective : Injective toComplex := fun _ _ h =>
  toReal_injective (AddCircle.injective_toCircle one_ne_zero (Circle.ext h))

@[simp]
/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem toComplex_zero : toComplex 0 = 1 := by
  simp [toComplex]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem toComplex_add (x y : QZ) : toComplex (x + y) = toComplex x * toComplex y := by
  simp [toComplex, AddCircle.toCircle_add]

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

noncomputable def toAddChar (f : G →+ QZ) : AddChar G ℂ where
  toFun g := toComplex (f g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [toComplex_add]

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toAddChar_apply (f : G →+ QZ) (g : G) : toAddChar f g = toComplex (f g) :=
  rfl

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem toAddChar_injective : Injective (toAddChar (G := G)) := fun _ _ h =>
  AddMonoidHom.ext fun a => toComplex_injective (DFunLike.congr_fun h a)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem toAddChar_add (f f' : G →+ QZ) : toAddChar (f + f') = toAddChar f + toAddChar f' := by
  ext a
  simp [toComplex_add]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.
-/
theorem exists_comp_eq_of_injective (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    i hi (toAddCircle.toAddMonoidHom.comp f)
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp g, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hg a
  simp only [AddMonoidHom.coe_comp, comp_apply, AddEquiv.coe_toAddMonoidHom] at h1 ⊢
  rw [h1, AddEquiv.symm_apply_apply]

/- English proof (translation)
Introduce a local definition for the expression. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Simplify to obtain the desired conclusion from the available facts.
-/
theorem exists_comp_eq_of_ker_le (h : G →+ H) (χ : G →+ QZ) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : H →+ QZ, ψ.comp h = χ := by
  let χ₀ : h.range →+ QZ := (QuotientAddGroup.lift h.ker χ hχ).comp
    (QuotientAddGroup.quotientKerEquivRange h).symm.toAddMonoidHom
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective h.range.subtype h.range.subtype_injective χ₀
  refine ⟨ψ, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hψ ⟨h a, a, rfl⟩
  have h2 : (QuotientAddGroup.quotientKerEquivRange h).symm ⟨h a, a, rfl⟩ =
      (a : G ⧸ h.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [AddMonoidHom.coe_comp, comp_apply, AddSubgroup.coe_subtype, χ₀,
    AddEquiv.coe_toAddMonoidHom, h2] at h1
  simpa using h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem exists_apply_ne_zero {a : G} (ha : a ≠ 0) : ∃ f : G →+ QZ, f a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp (c : G →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  exact (AddEquiv.map_eq_zero_iff toAddCircle.symm).mp h

variable (G) in

def evalHom : G →+ ((G →+ QZ) →+ QZ) where
  toFun a :=
    { toFun := fun f => f a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext f; simp
  map_add' a b := by ext f; simp

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalHom_apply (a : G) (f : G →+ QZ) : evalHom G a f = f a :=
  rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
theorem evalHom_injective : Injective (evalHom G) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨f, hf⟩ := exists_apply_ne_zero hne
  exact hf (DFunLike.congr_fun ha f)

instance [Finite G] : Finite (G →+ QZ) :=
  Finite.of_injective _ toAddChar_injective

/- English proof (translation)
Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_hom_le [Finite G] : Nat.card (G →+ QZ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  calc Nat.card (G →+ QZ) ≤ Nat.card (AddChar G ℂ) :=
        Nat.card_le_card_of_injective _ toAddChar_injective
    _ ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact AddChar.card_addChar_le G ℂ

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem card_hom [Finite G] : Nat.card (G →+ QZ) = Nat.card G :=
  card_hom_le.antisymm <| (Nat.card_le_card_of_injective _ evalHom_injective).trans card_hom_le

variable (G) in

noncomputable def addCharEquiv [Finite G] : (G →+ QZ) ≃+ AddChar G ℂ :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' toAddChar toAddChar_add)
    (by
      have := Fintype.ofFinite G
      refine toAddChar_injective.bijective_of_nat_card_le ?_
      rw [card_hom, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq])

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem addCharEquiv_apply [Finite G] (f : G →+ QZ) (a : G) :
    addCharEquiv G f a = toComplex (f a) :=
  rfl

end QZ

namespace QZDual

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

noncomputable def addCharEquiv [Finite N] : QZDual N ≃+ AddChar N ℂ :=
  toAddMonoidHomEquiv.trans (QZ.addCharEquiv N)

@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem addCharEquiv_apply [Finite N] (χ : QZDual N) (a : N) :
    addCharEquiv χ a = QZ.toComplex (χ a) :=
  rfl

instance [Finite N] : Finite (QZDual N) :=
  Finite.of_injective _ (toAddMonoidHomEquiv (A := N)).injective

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem card_eq [Finite N] : Nat.card (QZDual N) = Nat.card N :=
  (Nat.card_congr (toAddMonoidHomEquiv (A := N)).toEquiv).trans QZ.card_hom

end QZDual

end GroundTheory.ProfCoh
