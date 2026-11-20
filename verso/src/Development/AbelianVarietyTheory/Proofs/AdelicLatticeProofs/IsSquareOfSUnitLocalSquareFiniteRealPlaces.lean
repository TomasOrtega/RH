import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTopStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem mem_normSub_of_isSquare {F L : Type} [Field F] [CharZero F] [Field L] (φ : F →+* L)
    (δ : Fˣ) (h : IsSquare (φ (δ : F))) (x : Fˣ) : x ∈ normSub φ (δ : F) := by
  obtain ⟨c, hc⟩ := h
  have hδ : φ (δ : F) ≠ 0 := (map_ne_zero φ).mpr δ.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hc
    exact hδ hc
  have h2 : (2 : L) ≠ 0 := by
    have : φ 2 ≠ 0 := (map_ne_zero φ).mpr two_ne_zero
    rwa [map_ofNat] at this
  rw [mem_normSub]
  refine ⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩
  rw [hc]
  field_simp
  ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. A detailed English derivation is pending.
-/
theorem isSquare_of_mem_locSq : ∀ (F : Type) [Field F] [NumberField F] [DecidableEq (HeightOneSpectrum (𝓞 F))] (S T : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → sUnits F (S ∪ T) ⊔ finSq F T = ⊤ → ∀ y ∈ sUnits F (S ∪ T), y ∈ locSq F S → IsSquare (y : F) := by
  intro F _ _ _ S T hS hT y hy hloc
  by_contra hns
  apply GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F y (S ∪ T) (hS.mono Finset.subset_union_left) hy hns
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  intro x hx
  rw [finSq, Subgroup.mem_iInf] at hx
  rw [locSq, Subgroup.mem_inf, finSq, Subgroup.mem_iInf, Subgroup.mem_iInf] at hloc
  obtain ⟨hlocS, hlocR⟩ := hloc
  rw [locNorm, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_iInf]
  refine ⟨fun v => ?_, fun σ => ?_⟩
  · rw [Subgroup.mem_iInf]
    intro hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · exact mem_normSub_of_isSquare _ y
        ((mem_sqSub _ _).mp (Subgroup.mem_iInf.mp (hlocS v) hvS)) x
    · exact sqSub_le_normSub _ _ (Subgroup.mem_iInf.mp (hx v) hvT)
  · exact mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (hlocR σ)) x

end GlobalTheory.QNorm
