import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermLat
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetTermBasicFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeCountBoundFrames
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianLatticeMassOfTraceStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFrameClassTermsLeOverlatticeMassesStatement

open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.DefectShare

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `le_trans ?_ hN` and prove the remaining obligations. Conclude with `Set.encard_le_encard (fun a ha => hs a ha)` after adjusting the coercions.
-/
lemma tsum_subtype_le {α : Type} (P : α → Prop) (s : Set α) (hs : ∀ a, P a → a ∈ s) (f : α → ℝ≥0∞)
    (c N : ℝ≥0∞) (hf : ∀ a, P a → f a ≤ c) (hN : (s.encard : ℝ≥0∞) ≤ N) :
    ∑' a : {a // P a}, f a ≤ N * c := by
  calc ∑' a : {a // P a}, f a ≤ ∑' _ : ({a | P a} : Set α), c :=
        ENNReal.tsum_le_tsum fun a => hf a.1 a.2
    _ = (({a | P a} : Set α).encard : ℝ≥0∞) * c := ENNReal.tsum_set_const _ _
    _ ≤ N * c := by
        gcongr
        refine le_trans ?_ hN
        exact_mod_cast Set.encard_le_encard (fun a ha => hs a ha)

/- English proof (translation)
Distinguish the cases in `h : ∃ d Λ, S.IsTerm d Λ ∧ S.Fr d Λ = C`. Use `swap`. Establish `h0 : (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) = 0`. Unfold `Frames.sumData`. Use `ENNReal.tsum_eq_zero.2 fun o => ?_` and prove the remaining obligations.

Establish `: ({Λ | S.IsTerm o.out Λ ∧ S.be o.out Λ = β ∧ S.Fr o.out Λ = C} : Set (Submodule L.O S.V)) = ∅`. Use extensionality with `Λ`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨h1, -, h3⟩`. Conclude with `h ⟨_, _, h1, h3⟩`.

Simplify using `[Frames.nT, this]`. Rewrite using `[h0]`. Conclude with `zero_le`. Take `⟨d, Λ, hT, hFr⟩` from `h`. Take `⟨hSD, -, hM, -⟩` from `GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT`.

Establish `ha : 0 ≤ S.a` using `(GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).1`. Establish `hp : (S.fr d Λ, S.fr' d Λ) ∈ C`. Rewrite using `[← hFr]`. Conclude with `(GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1`. Take `⟨κ, hκ, hU⟩` from `GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ, hSD⟩`.

Take `⟨h1, h2⟩` from `GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC _ hp`. Establish `h3` using `GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC _ hp ha`. Establish `hlow : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.Mof (S.fr d Λ) (S.fr' d Λ))`. Use `(hU C hC _ hp _ le_rfl (fun x hx => (hM hx).2) (fun x hx y hy => (hSD.2 y).2 (hM hy).1 x (hM hx).1)).1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h2]`. Use `(h1 fun n => n = β).trans ?_` and prove the remaining obligations. Use `(tsum_subtype_le _ _ (fun Mh hMh => ?_) S.massSig (ENNReal.ofReal (2 * κ * ((β : ℝ) ^ (k - 1))⁻¹)) _ (fun Mh hMh => ?_) h3).trans ?_` and prove the remaining obligations. Conclude with `⟨hMh.1, hMh.2.1, hMh.2.2.1⟩`. Use `(hU C hC _ hp Mh hMh.1 hMh.2.1 hMh.2.2.1).2` as an intermediate fact.

Rewrite `this` using `[hMh.2.2.2]`. Conclude with `this`. Use `le_trans (le_of_eq ?_) (mul_le_mul_right hlow _)` and prove the remaining obligations. Establish `hz : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = (S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2))`. Rewrite using `[← zpow_natCast]`.

Use `congr 1`. Use `push_cast`. Rewrite using `[Int.toNat_of_nonneg ha]`. Establish `hq : (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) = ENNReal.ofReal ((S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2)))`. Rewrite using `[ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]`.

Rewrite using `[hz, hq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem share_le {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : LocE F E) (r k : ℕ) (S : Frames L r k) (hk : 4 * r + 7 ≤ k)
    (C : Set S.FrP) (hC : S.IsCls C) (β : ℕ) (_hβ : 1 ≤ β) :
    (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤
      ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) *
        S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  by_cases h : ∃ d Λ, S.IsTerm d Λ ∧ S.Fr d Λ = C
  swap
  · have h0 : (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) = 0 := by
      unfold Frames.sumData
      refine ENNReal.tsum_eq_zero.2 fun o => ?_
      have : ({Λ | S.IsTerm o.out Λ ∧ S.be o.out Λ = β ∧ S.Fr o.out Λ = C} :
          Set (Submodule L.O S.V)) = ∅ := by
        ext Λ
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, -, h3⟩
        exact h ⟨_, _, h1, h3⟩
      simp [Frames.nT, this]
    rw [h0]
    exact zero_le
  obtain ⟨d, Λ, hT, hFr⟩ := h
  obtain ⟨hSD, -, hM, -⟩ := GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have ha : 0 ≤ S.a := (GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).1
  have hp : (S.fr d Λ, S.fr' d Λ) ∈ C := by
    rw [← hFr]
    exact (GlobalTheory.HL.FrameClass.frame_classes L r k S (S.fr d Λ) (S.fr' d Λ)).1
  obtain ⟨κ, hκ, hU⟩ := GlobalTheory.T.selfDualHermitianLattice_mass_of_trace L r k S (by omega) ⟨Λ, hSD⟩
  obtain ⟨h1, h2⟩ := GlobalTheory.T.hermitianFrameClass_terms_le_overlattice_masses L r k S C hC _ hp
  have h3 := GlobalTheory.FrameOver.encard_overlattices_le L r k S C hC _ hp ha
  have hlow : ENNReal.ofReal (κ / 2) ≤ S.massSig (S.Mof (S.fr d Λ) (S.fr' d Λ)) := by
    have := (hU C hC _ hp _ le_rfl (fun x hx => (hM hx).2)
      (fun x hx y hy => (hSD.2 y).2 (hM hy).1 x (hM hx).1)).1
    simpa using this
  rw [h2]
  refine (h1 fun n => n = β).trans ?_
  refine (tsum_subtype_le _ _ (fun Mh hMh => ?_) S.massSig
    (ENNReal.ofReal (2 * κ * ((β : ℝ) ^ (k - 1))⁻¹)) _ (fun Mh hMh => ?_) h3).trans ?_
  · exact ⟨hMh.1, hMh.2.1, hMh.2.2.1⟩
  · have := (hU C hC _ hp Mh hMh.1 hMh.2.1 hMh.2.2.1).2
    rw [hMh.2.2.2] at this
    exact this
  · refine le_trans (le_of_eq ?_) (mul_le_mul_right hlow _)
    have hz : (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) = (S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2)) := by
      rw [← zpow_natCast]
      congr 1
      push_cast
      rw [Int.toNat_of_nonneg ha]
    have hq : (S.q : ℝ≥0∞) ^ (2 * S.a.toNat * (2 * r + 2)) =
        ENNReal.ofReal ((S.q : ℝ) ^ (2 * S.a.toNat * (2 * r + 2))) := by
      rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
    rw [hz, hq, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring

end GlobalTheory.HL.DefectShare
