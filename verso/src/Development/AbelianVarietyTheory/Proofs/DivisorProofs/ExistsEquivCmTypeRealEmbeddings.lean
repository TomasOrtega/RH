import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealEmbeddingOrdering
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.CMVal (OF Af lattice IsCMType)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (IsDefSum IsEisValue polydisc)

namespace GlobalTheory.CMTypeEmb

/- English proof (translation)
Establish `hc : Fintype.card I = Fintype.card (InfinitePlace E)` using `Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)`. Establish `hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E))` using `Fintype.card_congr (IsCMField.equivInfinitePlace E)`. Establish `h1` using `InfinitePlace.card_add_two_mul_card_eq_rank (FR E)`. Establish `hr : InfinitePlace.nrComplexPlaces (FR E) = 0` using `IsTotallyReal.nrComplexPlaces_eq_zero (FR E)`. Establish `h3` using `InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_eq_finrank {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) : Fintype.card I = Module.finrank ℚ (FR E) := by
  have hc : Fintype.card I = Fintype.card (InfinitePlace E) :=
    Fintype.card_of_bijective (GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hφ)
  have hE : Fintype.card (InfinitePlace E) = Fintype.card (InfinitePlace (FR E)) :=
    Fintype.card_congr (IsCMField.equivInfinitePlace E)
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank (FR E)
  have hr : InfinitePlace.nrComplexPlaces (FR E) = 0 := IsTotallyReal.nrComplexPlaces_eq_zero (FR E)
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := FR E)
  omega

/- English proof (translation)
Introduce `E _ _ _ I _ φ hφ`. Establish `hcard : Fintype.card I = Module.finrank ℚ (FR E)` using `card_eq_finrank hφ`. Set `e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I` to `(Fintype.equivFinOfCardEq hcard).symm`. Take `⟨e, he⟩` from `GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀`. Use `⟨e₀.symm.trans e, fun i x ↦ ?_⟩` and prove the remaining obligations.

Use `he (e₀.symm i) x` as an intermediate fact. Simplify using `only [Equiv.apply_symm_apply] at this`. Simplify using `only [Equiv.trans_apply]`. Conclude with `this.symm`.
-/
theorem exists_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∃ e : I ≃ Emb (FR E), ∀ i (x : FR E), φ i (x : E) = ((e i x : ℝ) : ℂ) := by
  intro E _ _ _ I _ φ hφ
  have hcard : Fintype.card I = Module.finrank ℚ (FR E) := card_eq_finrank hφ
  let e₀ : Fin (Module.finrank ℚ (FR E)) ≃ I := (Fintype.equivFinOfCardEq hcard).symm
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeRestrict.exists_equiv_realEmbeddings E I φ hφ e₀
  refine ⟨e₀.symm.trans e, fun i x ↦ ?_⟩
  have := he (e₀.symm i) x
  simp only [Equiv.apply_symm_apply] at this
  simp only [Equiv.trans_apply]
  exact this.symm

end GlobalTheory.CMTypeEmb
