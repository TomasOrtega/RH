import Formalism.LocalToGlobal.GlobalTheory.LinkTiesTh
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory

open Formalism.BasicNotions Formalism.MainNotions NumberField

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hermitian_form_H1_eq (Λ : AddSubgroup ℂ) (z w : ℂ) : GL3Theta.hf1 Λ z w = H1 Λ z w := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem lattice_character_eq (d : ℕ) (Λ : AddSubgroup ℂ) (x : ℂ) : GL3Theta.al1 d Λ x = al1 d Λ x := rfl

/- English proof (translation)
Use function extensionality and compare the values at `z`. Simplify using `only [TaylorLogMetric.U1, U1, H1]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem taylorLogMetric_U1_eq_U1 (Λ : AddSubgroup ℂ) (x : ℂ) (G : ℂ → ℂ) : TaylorLogMetric.U1 Λ x G = U1 Λ x G := by
  funext z
  simp only [TaylorLogMetric.U1, U1, H1]
  congr 2
  ring

/- English proof (translation)
Unfold `GL3Theta.IsTheta0 IsTheta0`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨h1, fun x hx z => ?_, h3⟩` and prove the remaining obligations. Establish `hx'` using `h2 x hx z`.

Rewrite `hx'` using `[lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]`. Then use the resulting hypothesis. Introduce and unpack `⟨h1, h2, h3⟩`. Use `⟨h1, fun x hx z => ?_, h3⟩` and prove the remaining obligations. Rewrite using `[lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]`. Conclude with `h2 x hx z`.
-/
theorem is_theta_zero_iff (d : ℕ) (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.IsTheta0 d Λ G ↔ IsTheta0 d Λ G := by
  unfold GL3Theta.IsTheta0 IsTheta0
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    have hx' := h2 x hx z
    rwa [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z] at hx'
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun x hx z => ?_, h3⟩
    rw [lattice_character_eq, congrFun (taylorLogMetric_U1_eq_U1 Λ x G) z]
    exact h2 x hx z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normSq_lattice_function_eq (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : GL3Theta.normSq1 Λ G = normSq1 Λ G := rfl

/- English proof (translation)
Introduce `M _ hD N N' L L' hA hC ρ G hG`. Establish `h2` using `(h.2 M hD ρ).2 G ((is_theta_zero_iff _ _ _).2 hG) N N' L L' hA hC`. Conclude with `h2`.
-/
theorem theta_power_of_first_layer {D : D7} {δ : ℂ} {e : TaylorLogMetric.FamE D} (h : GL3Theta.thPow D D.host.ccK δ e) : ThPow D δ e := by
  intro M _ hD N N' L L' hA hC ρ G hG
  have h2 := (h.2 M hD ρ).2 G ((is_theta_zero_iff _ _ _).2 hG) N N' L L' hA hC
  exact h2

end Formalism.L2.GlobalTheoryTheory

end
