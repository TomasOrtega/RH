import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTopStatement

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

/- English proof (translation)
Take `⟨c, hc⟩` from `h`. Establish `hδ : φ (δ : F) ≠ 0` using `(map_ne_zero φ).mpr δ.ne_zero`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [mul_zero] at hc`.

Conclude with `hδ hc`. Establish `h2 : (2 : L) ≠ 0`. Establish `: φ 2 ≠ 0` using `(map_ne_zero φ).mpr two_ne_zero`. Rewrite `this` using `[map_ofNat]`. Then use the resulting hypothesis. Rewrite using `[mem_normSub]`.

Use `⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩` and prove the remaining obligations. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `F _ _ _ S T hS hT y hy hloc`. Assume the negation of the conclusion as `hns`. Apply `GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top F y (S ∪ T) (hS.mono Finset.subset_union_left) hy hns` to reduce the goal to its premises. Rewrite using `[eq_top_iff, ← hT]`. Use `sup_le_sup_left ?_ _` and prove the remaining obligations.

Introduce `x hx`. Rewrite `hx` using `[finSq, Subgroup.mem_iInf]`. Rewrite `hloc` using `[locSq, Subgroup.mem_inf, finSq, Subgroup.mem_iInf, Subgroup.mem_iInf]`. Take `⟨hlocS, hlocR⟩` from `hloc`. Rewrite using `[locNorm, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_iInf]`.

Use `⟨fun v => ?_, fun σ => ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.mem_iInf]`. Introduce `hv`. Break down `Finset.mem_union.mp hv with hvS | hvT` into its components or cases. Conclude with `mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (Subgroup.mem_iInf.mp (hlocS v) hvS)) x`.

Conclude with `sqSub_le_normSub _ _ (Subgroup.mem_iInf.mp (hx v) hvT)`. Conclude with `mem_normSub_of_isSquare _ y ((mem_sqSub _ _).mp (hlocR σ)) x`.
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
