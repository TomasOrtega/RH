import Mathlib
import GroundTheory.GlobalFields.IdeleGroups.SIdeleGroups.Places

namespace GroundTheory.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AdeleBaseChange SemiLocal
open scoped NumberField.AdeleRing

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

namespace IdeleGroup

omit [NumberField K] in

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem smul_mem_standardOpenSubgroup (σ : L ≃ₐ[K] L) {x : IdeleGroup L}
    (hx : x ∈ standardOpenSubgroup L) : σ • x ∈ standardOpenSubgroup L := by
  rw [mem_standardOpenSubgroup_iff_ord] at hx ⊢
  intro w
  rw [ord_smul]
  exact hx _

variable (v : HeightOneSpectrum (𝓞 K))

def integerUnitsAboveIncl :
    ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) →*
      ((w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :=
  MonoidHom.pi fun w ↦
    (Units.map (w.1.adicCompletionIntegers L).subtype.toMonoidHom).comp (Pi.evalMonoidHom _ w)

omit [NumberField K] in
@[simp]
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_integerUnitsAboveIncl_apply
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((integerUnitsAboveIncl v z w : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L) =
      ((z w : w.1.adicCompletionIntegers L) : w.1.adicCompletion L) :=
  rfl

omit [NumberField K] in
/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem integerUnitsAboveIncl_injective :
    Function.Injective (integerUnitsAboveIncl (L := L) v) := fun _ _ h ↦
  funext fun w ↦ Units.ext (Subtype.ext (congrArg (fun y ↦ ((y w : (w.1.adicCompletion L)ˣ) :
    w.1.adicCompletion L)) h))

omit [NumberField K] in

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations.

Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem mem_range_integerUnitsAboveIncl_iff (y : (w : PlacesOver L v) → (w.1.adicCompletion L)ˣ) :
    y ∈ (integerUnitsAboveIncl v).range ↔ ∀ w : PlacesOver L v,
      (y w : w.1.adicCompletion L) ∈ w.1.adicCompletionIntegers L ∧
        ((y w)⁻¹ : (w.1.adicCompletion L)ˣ).val ∈ w.1.adicCompletionIntegers L := by
  constructor
  · rintro ⟨z, rfl⟩ w
    exact ⟨(z w : w.1.adicCompletionIntegers L).2,
      (((z w)⁻¹ : (w.1.adicCompletionIntegers L)ˣ) : w.1.adicCompletionIntegers L).2⟩
  · intro h
    refine ⟨fun w ↦ ⟨⟨y w, (h w).1⟩, ⟨((y w)⁻¹ : (w.1.adicCompletion L)ˣ), (h w).2⟩,
      Subtype.ext (y w).mul_inv, Subtype.ext (y w).inv_mul⟩, ?_⟩
    funext w
    exact Units.ext rfl

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components.
-/
theorem finiteEmbedAbove_integerUnitsAboveIncl_mem
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    finiteEmbedAbove v (integerUnitsAboveIncl v z) ∈ standardOpenSubgroup L := by
  refine (mem_standardOpenSubgroup L).2 fun w ↦ ?_
  rw [← map_inv]
  by_cases h : w.asIdeal.LiesOver v.asIdeal
  · rw [coe_finiteEmbedAbove_snd v _ ⟨w, h⟩, coe_finiteEmbedAbove_snd v _ ⟨w, h⟩]
    exact ⟨(z ⟨w, h⟩ : w.adicCompletionIntegers L).2,
      (((z ⟨w, h⟩)⁻¹ : (w.adicCompletionIntegers L)ˣ) : w.adicCompletionIntegers L).2⟩
  · rw [coe_finiteEmbedAbove_snd_of_not v _ h, coe_finiteEmbedAbove_snd_of_not v _ h]
    exact ⟨(w.adicCompletionIntegers L).one_mem, (w.adicCompletionIntegers L).one_mem⟩

def integerUnitsAboveSmul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ :=
  fun w ↦ localIntegerUnit w.1 ⟨σ • finiteEmbedAbove v (integerUnitsAboveIncl v z),
    smul_mem_standardOpenSubgroup σ (finiteEmbedAbove_integerUnitsAboveIncl_mem v z)⟩

instance : SMul (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  ⟨integerUnitsAboveSmul v⟩

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem integerUnitsAboveIncl_smul (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :
    integerUnitsAboveIncl v (σ • z) = σ • integerUnitsAboveIncl v z :=
  funext fun _ ↦ Units.ext rfl

instance integerUnitsAboveAction :
    MulDistribMulAction (L ≃ₐ[K] L) ((w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) :=
  (integerUnitsAboveIncl_injective v).mulDistribMulAction (integerUnitsAboveIncl v)
    (integerUnitsAboveIncl_smul v)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem integerUnitsAbove_smul_apply (σ : L ≃ₐ[K] L)
    (z : (w : PlacesOver L v) → (w.1.adicCompletionIntegers L)ˣ) (w : PlacesOver L v) :
    ((((σ • z) (σ • w) : ((σ • w).1.adicCompletionIntegers L)ˣ) :
      (σ • w).1.adicCompletionIntegers L) : (σ • w).1.adicCompletion L) =
      galEquiv v σ w.1 (σ • w).1 rfl ((z w : w.1.adicCompletionIntegers L) :
        w.1.adicCompletion L) := by
  rw [← coe_integerUnitsAboveIncl_apply, integerUnitsAboveIncl_smul, finiteUnitsAbove_smul_apply,
    coe_integerUnitsAboveIncl_apply]

end IdeleGroup

end

end GroundTheory.Global
