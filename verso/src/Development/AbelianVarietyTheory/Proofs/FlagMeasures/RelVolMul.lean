import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NcardImageOfLe
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.ContAut

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts.
-/
theorem relVol_mul {W : Type} [AddCommGroup W] {X Y B : AddSubgroup W}
    (hYX : Y.relIndex X ≠ 0) (hBY : B.relIndex Y ≠ 0) :
    relVol X B = relVol X Y * relVol Y B := by
  have hCY : (B ⊓ Y).relIndex Y ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have hCX : (B ⊓ Y).relIndex X ≠ 0 := AddSubgroup.relIndex_ne_zero_trans hCY hYX
  have e1 := ContModel.relVol_of_le (W0 := X) (inf_le_left : B ⊓ Y ≤ B) hCX
  have e2 := ContModel.relVol_of_le (W0 := X) (inf_le_right : B ⊓ Y ≤ Y) hCX
  have e3 := ContModel.relVol_of_le (W0 := Y) (inf_le_left : B ⊓ Y ≤ B) hCY
  have e4 : relVol Y (B ⊓ Y) = 1 / ((B ⊓ Y).relIndex Y : ℝ) := by
    unfold relVol
    rw [AddSubgroup.relIndex_eq_one.2 (inf_le_right : B ⊓ Y ≤ Y)]
    simp
  have c : ((B ⊓ Y).relIndex Y : ℝ) ≠ 0 := by exact_mod_cast hCY
  rw [e1, e2, e3, e4]
  field_simp

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem image_mk {W : Type} [AddCommGroup W] (A : AddSubgroup W) (φ : W ≃+ W) (S : Set W) :
    ∃ f : W ⧸ A → W ⧸ A.map φ.toAddMonoidHom, Function.Injective f ∧
      (QuotientAddGroup.mk : W → W ⧸ A.map φ.toAddMonoidHom) '' (φ '' S)
        = f '' ((QuotientAddGroup.mk : W → W ⧸ A) '' S) := by
  refine ⟨QuotientAddGroup.map A (A.map φ.toAddMonoidHom) φ.toAddMonoidHom
    (AddSubgroup.le_comap_map _ _), ?_, ?_⟩
  · intro u v
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective v
    intro h
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.eq] at h
    obtain ⟨a, ha, hh⟩ := h
    rw [QuotientAddGroup.eq]
    have : a = -x + y := φ.injective (by simpa using hh)
    rwa [← this]
  · rw [Set.image_image, Set.image_image]
    rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Supply the required witnesses or components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem cont_image : ∀ {W : Type} [AddCommGroup W] (W0 : AddSubgroup W) (φ : W ≃+ W), (W0.map φ.toAddMonoidHom).relIndex W0 ≠ 0 → W0.relIndex (W0.map φ.toAddMonoidHom) ≠ 0 → ∀ S, IsCO W0 S → IsCO W0 (φ '' S) ∧ cont W0 (φ '' S) = relVol W0 (W0.map φ.toAddMonoidHom) * cont W0 S := by
  intro W _ W0 φ h1 h2 S ⟨A, hA⟩
  have hi : Function.Injective φ.toAddMonoidHom := φ.injective
  have m1 := AddSubgroup.relIndex_map_map_of_injective A W0 hi
  have m2 := AddSubgroup.relIndex_map_map_of_injective W0 A hi
  obtain ⟨f, hf, him⟩ := image_mk A φ S
  have a1 : (A.map φ.toAddMonoidHom).relIndex (W0.map φ.toAddMonoidHom) ≠ 0 := m1 ▸ hA.1
  have a2 : (W0.map φ.toAddMonoidHom).relIndex (A.map φ.toAddMonoidHom) ≠ 0 := m2 ▸ hA.2.1
  have hG : GoodSub W0 (A.map φ.toAddMonoidHom) (φ '' S) := by
    refine ⟨AddSubgroup.relIndex_ne_zero_trans a1 h1, AddSubgroup.relIndex_ne_zero_trans h2 a2,
      ?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨a, ha, rfl⟩
      exact ⟨x + a, hA.2.2.1 x hx a ha, by simp⟩
    · rw [him]; exact hA.2.2.2.image f
  refine ⟨⟨_, hG⟩, ?_⟩
  rw [ContModel.cont_eq hG, ContModel.cont_eq hA, him, Set.ncard_image_of_injective _ hf,
    relVol_mul h1 a1]
  have : relVol (W0.map φ.toAddMonoidHom) (A.map φ.toAddMonoidHom) = relVol W0 A := by
    unfold relVol; rw [m1, m2]
  rw [this]; ring

end GlobalTheory.HL.ContAut
