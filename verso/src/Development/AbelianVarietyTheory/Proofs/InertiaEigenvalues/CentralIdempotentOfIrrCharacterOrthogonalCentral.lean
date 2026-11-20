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
Use `haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (by`. Rewrite using `[Nat.card_eq_fintype_card]`. Conclude with `Fintype.card_ne_zero)` after adjusting the coercions. Establish `h` using `FDRep.char_orthonormal V W`. Rewrite `h` using `[Nat.card_eq_fintype_card]`.

Unfold `ip`. Rewrite using `[h]`. Distinguish the cases in `hi : Nonempty (V ≅ W)`. Rewrite using `[if_pos hi, if_pos (FDRep.char_iso hi.some)]`. Rewrite using `[if_neg hi]`.

Distinguish the cases in `hc : V.character = W.character`. It suffices to derive a contradiction. Establish `h1` using `FDRep.char_orthonormal V V`. Rewrite `h1` using `[if_pos ⟨CategoryTheory.Iso.refl V⟩]`. Establish `h2` using `FDRep.char_orthonormal V W`.

Rewrite `h2` using `[if_neg hi, ← hc]`. Rewrite `h2` using `[h1]`. Simplify using `at h2`. Rewrite using `[if_neg hc]`.
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
Introduce `G _ _ χ χ' hχ hχ'`. Take `⟨V, hV, hVχ⟩` from `hχ`. Take `⟨W, hW, hWχ⟩` from `hχ'`. Establish `eV : V.character = χ` using `funext hVχ`. Establish `eW : W.character = χ'` using `funext hWχ`.

Substitute `eV eW` using the available equality. Take `⟨⟨hidem, _⟩, hcen, horth, _⟩` from `GlobalTheory.BadShare.ZCalc.zc_calc G V`. Use `⟨?_, ?_, ip_simple V W⟩` and prove the remaining obligations. Rewrite using `[zOf_eq_alg, zOf_eq_alg, ← alg_conv]`. Distinguish the cases in `hc : V.character = W.character`.

Rewrite using `[if_pos hc, ← hc, hidem]`. Rewrite using `[if_neg hc, horth W hc]`. Unfold `alg`. Simplify using the standard rewrite rules. Introduce `a`.

Rewrite using `[zOf_eq_alg, ← alg_coeff a, ← alg_conv, ← alg_conv, hcen]`.
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
