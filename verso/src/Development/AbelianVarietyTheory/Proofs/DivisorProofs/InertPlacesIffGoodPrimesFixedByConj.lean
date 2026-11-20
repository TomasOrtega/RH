import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DcOpCommOfCommute
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.InertPlaces

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P`. Establish `hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg` using `by rw [h.allPl]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨Q, hQ, rfl⟩`. Take `⟨hfix, hoff⟩` from `(h.inert.tie.okI t Q).1 hQ`.

Rewrite `hfix` using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq]`. Establish `hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q` using `HeightOneSpectrum.ext hfix`. Use `⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩` and prove the remaining obligations. Break down `hPP with hm | hm` into its components or cases. Conclude with `Or.inl (by rw [hSb, ← he]; exact hm)`.

Conclude with `Or.inr (by rw [← he]; exact hm)`. Establish `e1` using `GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc`. Establish `e2 : PP = R.plI Q`. Rewrite using `[← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]`. Break down `hPP with hm | hm` into its components or cases.

Conclude with `Or.inl (by rw [hSb, ← e2]; exact hm)`. Conclude with `Or.inr (by rw [← e2]; exact hm)`. Introduce and unpack `⟨hg, hf⟩`. Establish `hnS : P ∉ (R.Sb : Set (Pl D.host.E))`. Rewrite using `[hSb]`.

Introduce `hm`. Conclude with `(hg P (Or.inl hm)).1 rfl`. Establish `hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E))`. Use `⟨?_, hnS⟩` and prove the remaining obligations. Rewrite using `[Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]`.

Take `⟨Q, hQ⟩` from `h.inert.onto P hio`. Use `⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩` and prove the remaining obligations. Rewrite using `[hQ]`. Conclude with `hio.1`. Rewrite using `[hQ]`.

Introduce and unpack `(hm | hm)`. Conclude with `hnS hm`. Conclude with `(hg P (Or.inr hm)).1 rfl`.
-/
theorem inert_places_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → ∀ (t : T) (P : Pl D.host.E), (∃ Q ∈ A3.okI t, R.plI Q = P) ↔ (Good R.toRealDat t P ∧ conjPl P = P) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h t P
  have hSb : (R.Sb : Set (Pl D.host.E)) = R.Pg := by rw [h.allPl]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨hfix, hoff⟩ := (h.inert.tie.okI t Q).1 hQ
    rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq] at hfix
    have hf : Formalism.DivisionValues.conjPl (R.plI Q) = R.plI Q := HeightOneSpectrum.ext hfix
    refine ⟨fun PP hPP => ⟨fun he => hoff ?_, fun hc => hoff ?_⟩, hf⟩
    · rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← he]; exact hm)
      · exact Or.inr (by rw [← he]; exact hm)
    · have e1 := GlobalTheory.SplitHeckeAdj.eq_conj_of_isConjPl hc
      have e2 : PP = R.plI Q := by
        rw [← Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl PP, ← e1, hf]
      rcases hPP with hm | hm
      · exact Or.inl (by rw [hSb, ← e2]; exact hm)
      · exact Or.inr (by rw [← e2]; exact hm)
  · rintro ⟨hg, hf⟩
    have hnS : P ∉ (R.Sb : Set (Pl D.host.E)) := by
      rw [hSb]; intro hm; exact (hg P (Or.inl hm)).1 rfl
    have hio : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := by
      refine ⟨?_, hnS⟩
      rw [Formalism.DivisionValues.GluingInclusion.conjIdeal_eq, hf]
    obtain ⟨Q, hQ⟩ := h.inert.onto P hio
    refine ⟨Q, (h.inert.tie.okI t Q).2 ⟨?_, ?_⟩, hQ⟩
    · rw [hQ]; exact hio.1
    · rw [hQ]
      rintro (hm | hm)
      · exact hnS hm
      · exact (hg P (Or.inr hm)).1 rfl

end GlobalTheory.InertPlaces
