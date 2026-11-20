import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianMassEqSumFrameClasses

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S P hP`. Use `⟨?_, fun h hh d C => ?_⟩` and prove the remaining obligations. Establish `e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d)`. Use function extensionality and compare the values at `fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ`. Rewrite using `[e]`.

Unfold `Frames.sumData Frames.sumCls`. Simplify using `only [← ENNReal.tsum_mul_left]`. Rewrite using `[ENNReal.tsum_comm]`. Use `tsum_congr fun c => ?_` and prove the remaining obligations. Use `split_ifs`.

Conclude with `tsum_congr fun o => mul_left_comm _ _ _`. Simplify using the standard rewrite rules. Unfold `Frames.nT`. Establish `e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) = (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C}`. Use extensionality with `Λ`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Establish `A` using `GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)`. Use `⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩` and prove the remaining obligations. Rewrite using `[A.2.2.2.2.1, h3, inv_smul_smul]`.

Introduce and unpack `⟨Λ, ⟨h1, h2, h3⟩, rfl⟩`. Establish `A` using `GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh`. Use `⟨A.1, hP _ hh d Λ h1 h2, ?_⟩` and prove the remaining obligations. Rewrite using `[A.2.2.2.2.1, h3]`. Rewrite using `[e, (MulAction.injective h).encard_image]`.
-/
theorem sumData_mass_eq_sumCls : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ P : S.Datum → Submodule L.O S.V → Prop, (∀ h ∈ S.St, ∀ d Λ, S.IsTerm d Λ → P d Λ → P d (h • Λ)) → (S.sumData fun d => S.mass d (P d)) = (S.sumCls fun C => S.sumData fun d => S.nT d C (P d)) ∧ ∀ h ∈ S.St, ∀ d C, S.nT d (h • C) (P d) = S.nT d C (P d) := by
  intro F _ _ _ _ _ E _ _ _ L r k S P hP
  refine ⟨?_, fun h hh d C => ?_⟩
  · have e : (fun d => S.mass d (P d)) = fun d => S.sumCls fun C => S.nT d C (P d) :=
      funext fun d => mass_eq_sumCls L r k S d (P d) fun h hh Λ => hP h hh d Λ
    rw [e]
    unfold Frames.sumData Frames.sumCls
    simp only [← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun c => ?_
    split_ifs
    · exact tsum_congr fun o => mul_left_comm _ _ _
    · simp
  · unfold Frames.nT
    have e : ({Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = h • C} : Set (Submodule L.O S.V)) =
        (fun Λ => h • Λ) '' {Λ | S.IsTerm d Λ ∧ P d Λ ∧ S.Fr d Λ = C} := by
      ext Λ
      constructor
      · rintro ⟨h1, h2, h3⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h⁻¹ (S.St.inv_mem hh)
        refine ⟨h⁻¹ • Λ, ⟨A.1, hP _ (S.St.inv_mem hh) d Λ h1 h2, ?_⟩, smul_inv_smul h Λ⟩
        rw [A.2.2.2.2.1, h3, inv_smul_smul]
      · rintro ⟨Λ, ⟨h1, h2, h3⟩, rfl⟩
        have A := GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ h1 h hh
        refine ⟨A.1, hP _ hh d Λ h1 h2, ?_⟩
        rw [A.2.2.2.2.1, h3]
    rw [e, (MulAction.injective h).encard_image]

end GlobalTheory.HL
