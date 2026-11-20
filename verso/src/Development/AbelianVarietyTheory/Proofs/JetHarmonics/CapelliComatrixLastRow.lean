import Mathlib
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LemmaDDeterminantIdentity

open Formalism.REAL

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `Formalism.FourierDecayAlt.P.expansion_last_line A (n + 1) n E hE (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c) id u`. Establish `h1 : (Fin.snoc (α` using `fun _ => Fin (n + 1)) Fin.castSucc c : Fin (n + 1) → Fin (n + 1)) ∘ Fin.castSucc = Fin.castSucc := by`. Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Rewrite `h` using `[h1, Fin.snoc_last]`.

Simplify using `only [Function.id_comp, id] at h`. Rewrite using `[← h]`. Use `split_ifs with hc`. Substitute `hc` using the available equality. Unfold `qdet`.

Use `congr 1`. Use function extensionality and compare the values at `k`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun k => ?_) k <;> simp`. Take `⟨c', rfl⟩` from `Fin.exists_castSucc_eq.mpr hc`. Conclude with `quantumMinor_eq_zero_of_row_eq qSkewRow E _ _ u c'.castSucc (Fin.last n) hc (by simp)`.
-/
theorem capelli_comatrix_last_row (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → A) (hE : GlRel E) (u : ℂ) (c : Fin (n + 1)) :
    ∑ l : Fin (n + 1), (((-1 : ℤ) ^ (n + (l : ℕ)) : ℤ) : A) *
        (qminor E Fin.castSucc (Fin.succAbove l) (u - 1) * Tm E u c l) =
      if c = Fin.last n then qdet E u else 0 := by
  have h := Formalism.FourierDecayAlt.P.expansion_last_line A (n + 1) n E hE
    (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c) id u
  have h1 : (Fin.snoc (α := fun _ => Fin (n + 1)) Fin.castSucc c : Fin (n + 1) → Fin (n + 1)) ∘
      Fin.castSucc = Fin.castSucc := by
    funext k
    simp
  rw [h1, Fin.snoc_last] at h
  simp only [Function.id_comp, id] at h
  rw [← h]
  split_ifs with hc
  · subst hc
    unfold qdet
    congr 1
    funext k
    refine Fin.lastCases ?_ (fun k => ?_) k <;> simp
  · obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.mpr hc
    exact quantumMinor_eq_zero_of_row_eq qSkewRow E _ _ u c'.castSucc (Fin.last n) hc (by simp)

end GlobalTheory
