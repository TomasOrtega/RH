import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNormsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsLocalKummerNormsEqTopOfPowStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupLocalKummerNormsNeTopStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMonStatement

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS`. Assume the negation of the conclusion as `hne`. Establish `hne' : ∀ r : F, r ^ p ≠ (y : F)` using `fun r hr => hne ⟨r, hr⟩`. Establish `hadm : AdmP p F (S ∪ T)` using `(GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS`. Use `GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_` and prove the remaining obligations.

Rewrite using `[eq_top_iff, ← hT]`. Use `sup_le_sup_left ?_ _` and prove the remaining obligations. Unfold `finNorm`. Use `le_iInf₂ fun v hv => ?_` and prove the remaining obligations. Break down `Finset.mem_union.1 hv with hv | hv` into its components or cases.

Establish `h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F))` using `(iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS`. Take `⟨r, hr⟩` from `h1`. Establish `: CharZero (v.adicCompletion F)` using `charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective`. Rewrite using `[GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]`. Conclude with `le_top`.

Conclude with `le_trans (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv) ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))`.
-/
theorem pow_of_mem_sUnits_union_of_mem_finPow :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
      [DecidableEq (HeightOneSpectrum (𝓞 F))] (ζ : F) (S T : Finset (HeightOneSpectrum (𝓞 F))),
      p.Prime → IsPrimitiveRoot ζ p → AdmP p F S → sUnits F (S ∪ T) ⊔ finPow p F T = ⊤ →
      ∀ y ∈ sUnits F (S ∪ T), y ∈ finPow p F S → ∃ r : F, r ^ p = (y : F) := by
  intro p F _ _ _ _ ζ S T hp hζ hS hT y hy hyS
  by_contra hne
  have hne' : ∀ r : F, r ^ p ≠ (y : F) := fun r hr => hne ⟨r, hr⟩
  have hadm : AdmP p F (S ∪ T) :=
    (GlobalTheory.T.exists_admissiblePlacesContainingPrime_superset_mono p F hp.pos).2 S (S ∪ T) Finset.subset_union_left hS
  refine GlobalTheory.T.sUnits_sup_localKummerNorms_ne_top p F ζ y (S ∪ T) hp hζ hadm hy hne' ?_
  rw [eq_top_iff, ← hT]
  refine sup_le_sup_left ?_ _
  unfold finNorm
  refine le_iInf₂ fun v hv => ?_
  rcases Finset.mem_union.1 hv with hv | hv
  · have h1 : y ∈ powSub p (algebraMap F (v.adicCompletion F)) :=
      (iInf₂_le (f := fun w (_ : w ∈ S) => powSub p (algebraMap F (w.adicCompletion F))) v hv) hyS
    obtain ⟨r, hr⟩ := h1
    have : CharZero (v.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
    rw [GlobalTheory.T.unitsLocalKummerNorms_eq_top_of_pow p F (v.adicCompletion F) _ (y : F) r hp.pos y.ne_zero hr]
    exact le_top
  · exact le_trans
      (iInf₂_le (f := fun w (_ : w ∈ T) => powSub p (algebraMap F (w.adicCompletion F))) v hv)
      ((GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1 F (v.adicCompletion F) _ (y : F))

end GlobalTheory.CNorm
