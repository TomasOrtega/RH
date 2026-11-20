import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.WtSubOneLe
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons x l ih => simp only [sumMvList, ptSumL, ih]`. Both sides reduce to the same expression.
-/
theorem sumMvList_eq_ptSumL {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) {τ : Type} (l : List (Fin d → MvPowerSeries τ C)) :
    sumMvList G l = ptSumL G l := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [sumMvList, ptSumL, ih]; rfl

/- English proof (translation)
The claim follows from `sumMvList_eq_ptSumL G _`.
-/
theorem basisMap_eq_ptBasisMap {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)} {d : ℕ}
    (G : LogFGL v d) (γ : Fin d → Fin d → PowerSeries C) : basisMap G γ = ptBasisMap G γ :=
  sumMvList_eq_ptSumL G _

/- English proof (translation)
Introduce `h2 C _ _ _ v p hp hvp d h hh ty G μ`. Use `⟨?_, fun γ hγ => ?_⟩` and prove the remaining obligations. Establish `key : ∀ a : Fin d, ∃ γ : Fin d → PowerSeries C, IsCurve v γ ∧ G.IsOfType p ty (ty a) γ ∧ tangent γ = Pi.single a 1`. Introduce `a`. Use `h2 C v p hp hvp d h hh ty G μ (ty a) (Pi.single a 1) (fun b => ?_) (fun b hb => ?_)` and prove the remaining obligations.

Unfold `IsIntV`. Distinguish the cases in `e : b = a`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne e]`.

Conclude with `Pi.single_eq_of_ne (fun e => hb (by rw [e])) _`. Use `choose γ h1 h2' h3 using key`. Use `⟨γ, h1, h2', ?_⟩` and prove the remaining obligations. Establish `: (Matrix.of fun a b => tangent (γ a) b) = (1 : Matrix (Fin d) (Fin d) C)`. Use extensionality with `a b`.

Simplify using `[h3, Matrix.one_apply, Pi.single_apply, eq_comm]`. Rewrite using `[this, Matrix.det_one, v.map_one]`. Rewrite using `[basisMap_eq_ptBasisMap]`. Conclude with `⟨ptBasisMap_inv G hγ.1 hγ.2.2, ptBasisMap_lg G hγ.1⟩`.
-/
theorem typicalBasis_coordinates : TypicalCurveEigenspace → TypicalCurveBasisExists := by
  intro h2 C _ _ _ v p hp hvp d h hh ty G μ
  refine ⟨?_, fun γ hγ => ?_⟩
  · have key : ∀ a : Fin d, ∃ γ : Fin d → PowerSeries C,
        IsCurve v γ ∧ G.IsOfType p ty (ty a) γ ∧ tangent γ = Pi.single a 1 := by
      intro a
      refine h2 C v p hp hvp d h hh ty G μ (ty a) (Pi.single a 1) (fun b => ?_) (fun b hb => ?_)
      · unfold IsIntV
        by_cases e : b = a
        · subst e; simp
        · simp [Pi.single_eq_of_ne e]
      · exact Pi.single_eq_of_ne (fun e => hb (by rw [e])) _
    choose γ h1 h2' h3 using key
    refine ⟨γ, h1, h2', ?_⟩
    have : (Matrix.of fun a b => tangent (γ a) b) = (1 : Matrix (Fin d) (Fin d) C) := by
      ext a b
      simp [h3, Matrix.one_apply, Pi.single_apply, eq_comm]
    rw [this, Matrix.det_one, v.map_one]
  · rw [basisMap_eq_ptBasisMap]
    exact ⟨ptBasisMap_inv G hγ.1 hγ.2.2, ptBasisMap_lg G hγ.1⟩

end GlobalTheory
