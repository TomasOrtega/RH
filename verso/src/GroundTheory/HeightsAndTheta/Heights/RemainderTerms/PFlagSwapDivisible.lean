import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial

noncomputable section

/- English proof (translation)
Proceed by induction on `Q using MvPolynomial.induction_on with`. Consider the case `C r => simp [MvPolynomial.algebraMap_eq]`. Consider the case `add p q hp hq`. Rewrite using `[map_add, add_sub_add_comm]`. Conclude with `dvd_add hp hq`.

Consider the case `mul_X p k hp`. Rewrite using `[map_mul, aeval_X]`. Establish `hk : (X a - X b : MvPolynomial σ R) ∣ X k - (if k = a then (X b : MvPolynomial σ R) else X k)` using `by split_ifs with h`. Substitute `h` using the available equality. Conclude with `dvd_rfl`.

Simplify using the standard rewrite rules. Establish `e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p * (if k = a then (X b : MvPolynomial σ R) else X k) = (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k + aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) …` using `by ring`. Rewrite using `[e]`. Conclude with `dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)`.
-/
theorem FlagSwapDivisible.dvd_sub_substitute {R σ : Type} [CommRing R] [DecidableEq σ] (a b : σ)
    (Q : MvPolynomial σ R) :
    (X a - X b : MvPolynomial σ R) ∣
      Q - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) Q := by
  induction Q using MvPolynomial.induction_on with
  | C r => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq =>
    rw [map_add, add_sub_add_comm]
    exact dvd_add hp hq
  | mul_X p k hp =>
    rw [map_mul, aeval_X]
    have hk : (X a - X b : MvPolynomial σ R) ∣
        X k - (if k = a then (X b : MvPolynomial σ R) else X k) := by
      split_ifs with h
      · subst h; exact dvd_rfl
      · simp
    have e : p * X k - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
          (if k = a then (X b : MvPolynomial σ R) else X k) =
        (p - aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p) * X k +
          aeval (fun v => if v = a then (X b : MvPolynomial σ R) else X v) p *
            (X k - (if k = a then (X b : MvPolynomial σ R) else X k)) := by ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left hp _) (dvd_mul_of_dvd_right hk _)

/- English proof (translation)
Introduce `σ _ P a b hab hP`. Use `set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg`. Establish `hswap : g ∘ Equiv.swap a b = g`. Use function extensionality and compare the values at `v`. Simplify using `only [Function.comp_apply, hg]`.

Break down `eq_or_ne v a with rfl | hva` into its components or cases. Simplify using `[Equiv.swap_apply_left, hab.symm]`. Break down `eq_or_ne v b with rfl | hvb` into its components or cases. Simplify using `[Equiv.swap_apply_right, hva]`. Simplify using `[Equiv.swap_apply_of_ne_of_ne hva hvb, hva]`.

Establish `hzero : aeval g P = 0`. Establish `h1 : aeval g P = -aeval g P`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : aeval g P + aeval g P = 0` using `by nth_rewrite 2 [h1]; exact add_neg_cancel _`. Establish `h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0` using `by rw [two_mul]; exact h2`.

Break down `mul_eq_zero.mp h3 with h | h` into its components or cases. Conclude with `absurd h two_ne_zero`. Conclude with `h`. Establish `hd` using `FlagSwapDivisible.dvd_sub_substitute a b P`. Rewrite `hd` using `[← hg, hzero, sub_zero]`.

Conclude with `hd`.
-/
theorem FlagSwapDivisible.proof : FlagSwapDivisible.Statement := by
  intro σ _ P a b hab hP
  set g : σ → MvPolynomial σ ℚ := fun v => if v = a then X b else X v with hg
  have hswap : g ∘ Equiv.swap a b = g := by
    funext v
    simp only [Function.comp_apply, hg]
    rcases eq_or_ne v a with rfl | hva
    · simp [Equiv.swap_apply_left, hab.symm]
    · rcases eq_or_ne v b with rfl | hvb
      · simp [Equiv.swap_apply_right, hva]
      · simp [Equiv.swap_apply_of_ne_of_ne hva hvb, hva]
  have hzero : aeval g P = 0 := by
    have h1 : aeval g P = -aeval g P := by
      calc aeval g P = aeval (g ∘ Equiv.swap a b) P := by rw [hswap]
        _ = aeval g (rename (Equiv.swap a b) P) := (aeval_rename _ _ _).symm
        _ = -aeval g P := by rw [hP, map_neg]
    have h2 : aeval g P + aeval g P = 0 := by
      nth_rewrite 2 [h1]; exact add_neg_cancel _
    have h3 : (2 : MvPolynomial σ ℚ) * aeval g P = 0 := by rw [two_mul]; exact h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h two_ne_zero
    · exact h
  have hd := FlagSwapDivisible.dvd_sub_substitute a b P
  rw [← hg, hzero, sub_zero] at hd
  exact hd

end

end RestTerms

end GroundTheory.Heights₂.Heights
