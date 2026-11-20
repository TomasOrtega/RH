import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsometricRealisationOfSublattice
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.RealPlaceAnalysis.Complexify
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_isometric_realisation_of_sublattice` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsIsometricRealisationOfSublattice.lean&line=69#L69)
-/
theorem _root_.GlobalTheory.T.exists_isometric_realisation_of_sublattice' : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] (n : ℕ) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (R : Submodule (𝓞 K) (Fin n → K)), (∀ w, IsUnit (X w).det) → R.FG → ∃ (j : ℕ) (i : Matrix (Fin n) (Fin j) K) (X' : InfinitePlace K → Matrix (Fin j) (Fin j) ℂ) (P : InfinitePlace K → Matrix (Fin n) (Fin j) ℂ) (B : Submodule (𝓞 K) (Fin j → K)), j = rkK R ∧ (∀ w, IsUnit (X' w).det) ∧ (∀ w, (P w)ᴴ * P w = 1) ∧ (∀ w, (X w)⁻¹ * i.map w.embedding = P w * (X' w)⁻¹) ∧ B.FG ∧ Submodule.span K (B : Set (Fin j → K)) = ⊤ ∧ (∀ y ∈ B, i *ᵥ y ∈ R) ∧ (∀ r ∈ R, ∃ y ∈ B, i *ᵥ y = r) ∧ largestSize (Pi.basisFun K (Fin j)) X' B = largestSize (Pi.basisFun K (Fin n)) X R := by
  first | exact @GlobalTheory.exists_isometric_realisation_of_sublattice | exact GlobalTheory.exists_isometric_realisation_of_sublattice | (intros; apply GlobalTheory.exists_isometric_realisation_of_sublattice <;> assumption)
