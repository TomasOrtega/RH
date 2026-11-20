import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralIdempotentIrreducibleCharacterProps
open GlobalTheory.GLq Formalism.MainNotions.ArithmeticCylinders Polynomial
open scoped Classical

noncomputable section

namespace GlobalTheory.GLq.ZOrth

open GlobalTheory.BadShare GlobalTheory.BadShare.Basic

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem zOf_eq_alg {G : Type} [Group G] [Fintype G] (χ : G → ℂ) : zOf χ = alg (zc χ) := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. It suffices to derive a contradiction.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ip_simple {G : Type} [Group G] [Fintype G] (V W : FDRep ℂ G) [CategoryTheory.Simple V]
    [CategoryTheory.Simple W] :
    ip V.character W.character = if V.character = W.character then 1 else 0 := by
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by
    rw [Nat.card_eq_fintype_card]; exact_mod_cast Fintype.card_ne_zero)
  have h := FDRep.char_orthonormal V W
  rw [Nat.card_eq_fintype_card] at h
  unfold ip
  rw [h]
  by_cases hi : Nonempty (V ≅ W)
  · rw [if_pos hi, if_pos (FDRep.char_iso hi.some)]
  · rw [if_neg hi]
    by_cases hc : V.character = W.character
    · exfalso
      have h1 := FDRep.char_orthonormal V V
      rw [if_pos ⟨CategoryTheory.Iso.refl V⟩] at h1
      have h2 := FDRep.char_orthonormal V W
      rw [if_neg hi, ← hc] at h2
      rw [h1] at h2
      simp at h2
    · rw [if_neg hc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Substitute using the available equality. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities.
-/
theorem zorth : ∀ (G : Type) [Group G] [Fintype G] (χ χ' : G → ℂ), IsIrr χ → IsIrr χ' → (zOf χ * zOf χ' = if χ = χ' then zOf χ else 0) ∧ (∀ a, zOf χ * a = a * zOf χ) ∧ ip χ χ' = if χ = χ' then 1 else 0 := by
  intro G _ _ χ χ' hχ hχ'
  obtain ⟨V, hV, hVχ⟩ := hχ
  obtain ⟨W, hW, hWχ⟩ := hχ'
  have eV : V.character = χ := funext hVχ
  have eW : W.character = χ' := funext hWχ
  subst eV eW
  obtain ⟨⟨hidem, _⟩, hcen, horth, _⟩ := GlobalTheory.BadShare.ZCalc.zc_calc G V
  refine ⟨?_, ?_, ip_simple V W⟩
  · rw [zOf_eq_alg, zOf_eq_alg, ← alg_conv]
    by_cases hc : V.character = W.character
    · rw [if_pos hc, ← hc, hidem]
    · rw [if_neg hc, horth W hc]
      unfold alg; simp
  · intro a
    rw [zOf_eq_alg, ← alg_coeff a, ← alg_conv, ← alg_conv, hcen]
end GlobalTheory.GLq.ZOrth
