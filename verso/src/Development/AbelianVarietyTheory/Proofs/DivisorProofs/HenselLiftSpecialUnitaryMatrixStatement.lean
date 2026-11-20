import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HenselLiftSpecialUnitaryMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntLocConjIntLocConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open scoped TensorProduct
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdelicU GlobalTheory.TamOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHenselLiftSpecialUnitaryMatrix.lean&line=147#L147)
-/
theorem _root_.GlobalTheory.T.hensel_lift_special_unitary_matrix : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → ∀ (I : Ideal R), (∀ x ∈ I, c x ∈ I) → IsAdicComplete I R → ∀ w : R, w + c w = 1 → ∀ (r : ℕ) (g : Matrix (Fin r) (Fin r) R), (∀ a b, ((g.map c)ᵀ * g - 1) a b ∈ I) → g.det - 1 ∈ I → ∃ g' : Matrix (Fin r) (Fin r) R, (g'.map c)ᵀ * g' = 1 ∧ g'.det = 1 ∧ ∀ a b, g' a b - g a b ∈ I := by
  first | exact @GlobalTheory.HenselSU.hensel_special_unitary | exact GlobalTheory.HenselSU.hensel_special_unitary | (intros; apply GlobalTheory.HenselSU.hensel_special_unitary <;> assumption)
