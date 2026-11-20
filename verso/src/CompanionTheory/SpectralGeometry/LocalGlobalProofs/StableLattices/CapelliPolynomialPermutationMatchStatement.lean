import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CapelliPolynomialPermutationMatch
import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FStableLattices%2FCapelliPolynomialPermutationMatch.lean&line=42#L42)
-/
theorem _root_.GlobalTheory.T.capelli_polynomial_permutation_match : ∀ (n M : ℕ) (lev : Fin n → ℕ) (χ : Fin n → ℂ) (P : Fin M → ℂ[X]) (s : Fin M → ℂ),
    (∀ a, lev a < M) → (∀ i, (P i).Monic ∧ (P i).natDegree = (univ.filter fun a => lev a = (i : ℕ)).card) →
    (∀ Y : ℂ, ∏ i, (P i).eval (Y + s i) = Formalism.QuantumDeterminants.capP χ Y) →
    ∃ σ : Equiv.Perm (Fin n), ∀ i : Fin M,
      ∑ a ∈ univ.filter (fun a => lev a = (i : ℕ)), χ (σ a) =
        (P i).nextCoeff + ((univ.filter fun a => lev a = (i : ℕ)).card : ℂ) * s i := by
  first | exact @GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | exact GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors | (intros; apply GlobalTheory.CompanionTheory.RgCOBlock.exists_perm_of_monic_factors <;> assumption)
