import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.EagonNorthcottIntegral.ExactSecondDegreeZero

noncomputable section

namespace PI.EagonNorthcottZ

open MvPolynomial PI.EagonNorthcott

/- English proof (translation)
Introduce `D a`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `j ω hω hy _`. Establish `h0` using `hYz D j ω hω hy`.

Use `⟨0, ⟨fun _ _ => rfl, fun J m hm => by simp at hm⟩, ?_, ?_⟩` and prove the remaining obligations. Use `(hL D ys (0 : W D) 0).1` as an intermediate fact. Simplify using `using this`. Use `(hL D xs (0 : W D) 0).1` as an intermediate fact. Rewrite using `[h0]`.

Simplify using `using this`. Consider the case `succ a ih`. Introduce `j ω hω hy hx`. Take `⟨θ, hθ, hθω⟩` from `hY D a j ω hω hy`. Establish `h1 : K ys (K xs θ) = 0` using `by rw [hA D ys xs θ, hθω, hx, neg_zero]`.

Take `⟨η', hη', hη'y, hη'x⟩` from `ih j (K xs θ) (hGX D a (j + 1) θ hθ) h1 (hS D xs θ)`. Establish `h2 : K xs (θ - η') = 0` using `by rw [(hL D xs θ η').1, hη'x, sub_self]`. Take `⟨ζ, hζ, hζx⟩` from `hX D a (j + 1) (θ - η') (hG D a (j + 2) θ η' hθ hη').1 h2`. Use `⟨-K ys ζ, (hG D (a + 1) (j + 2) _ _ (hGY D a (j + 2) ζ hζ) (hGY D a (j + 2) ζ hζ)).2, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(hL D ys (K ys ζ) 0).2, hS D ys ζ, neg_zero]`.

Rewrite using `[(hL D xs (K ys ζ) 0).2, hA D xs ys ζ, neg_neg, hζx, (hL D ys θ η').1, hθω, hη'y, sub_zero]`.
-/
theorem main_of (hA : Anti) (hS : Sq) (hL : KLin) (hG : GrLin) (hGX : GrX) (hGY : GrY) (hX : ExX) (hY : ExY) (hYz : ExYz) :
    Main := by
  intro D a
  induction a with
  | zero =>
    intro j ω hω hy _
    have h0 := hYz D j ω hω hy
    refine ⟨0, ⟨fun _ _ => rfl, fun J m hm => by simp at hm⟩, ?_, ?_⟩
    · have := (hL D ys (0 : W D) 0).1; simpa using this
    · have := (hL D xs (0 : W D) 0).1; rw [h0]; simpa using this
  | succ a ih =>
    intro j ω hω hy hx
    obtain ⟨θ, hθ, hθω⟩ := hY D a j ω hω hy
    have h1 : K ys (K xs θ) = 0 := by rw [hA D ys xs θ, hθω, hx, neg_zero]
    obtain ⟨η', hη', hη'y, hη'x⟩ := ih j (K xs θ) (hGX D a (j + 1) θ hθ) h1 (hS D xs θ)
    have h2 : K xs (θ - η') = 0 := by rw [(hL D xs θ η').1, hη'x, sub_self]
    obtain ⟨ζ, hζ, hζx⟩ := hX D a (j + 1) (θ - η') (hG D a (j + 2) θ η' hθ hη').1 h2
    refine ⟨-K ys ζ, (hG D (a + 1) (j + 2) _ _ (hGY D a (j + 2) ζ hζ) (hGY D a (j + 2) ζ hζ)).2, ?_, ?_⟩
    · rw [(hL D ys (K ys ζ) 0).2, hS D ys ζ, neg_zero]
    · rw [(hL D xs (K ys ζ) 0).2, hA D xs ys ζ, neg_neg, hζx, (hL D ys θ η').1, hθω, hη'y, sub_zero]

end PI.EagonNorthcottZ
