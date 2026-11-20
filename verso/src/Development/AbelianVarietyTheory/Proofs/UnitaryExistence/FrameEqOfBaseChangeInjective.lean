import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatricesStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndCompStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChangeStatement

namespace GlobalTheory.Frames

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

/- English proof (translation)
Introduce `_ E _ _ _ H Dw l Xo c S _ _ T _ _ φ z z' w hφ hx hz hz'`. Take `⟨g, a, -, hga⟩` from `(GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S z z').1 hx`. Establish `h1` using `(GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c S T φ z z' w w g (a : S) hga hz).1 hz'`. Establish `h2` using `(GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c T w w w).1`. Take `⟨hg, ha⟩` from `(GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T w w).2 _ _ _ _ h1 h2`.

Establish `ha1 : (a : S) = ((1 : Sˣ) : S)` using `hφ (by rw [ha]; simp)`. Establish `hg1 : g = fun _ => 1`. Use function extensionality and compare the values at `τ`. Establish `h` using `congrFun hg τ`. Use extensionality with `i j`.

Apply `hφ` to reduce the goal to its premises. Establish `hij` using `congrFun (congrFun h i) j`. Simplify using `only [Matrix.map_apply] at hij`. Rewrite using `[hij]`. Distinguish the cases in `e : i = j`.

Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne e]`. Rewrite `hga` using `[ha1, hg1]`. Establish `h3 : FrChg (fun _ => 1) ((1 : Sˣ) : S) z z` using `(GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S z z z).1`.

Conclude with `(GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S z (fun _ => 1) 1 (fun _ => by simp)).unique h3 hga`.
-/
theorem frPt_eq_of_frMap_injective : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (z z' : FrPt Xo c S) (w : FrPt Xo c T), Function.Injective φ → z'.x = z.x → FrMap φ z w → FrMap φ z' w → z = z' := by
  intro _ E _ _ _ H Dw l Xo c S _ _ T _ _ φ z z' w hφ hx hz hz'
  obtain ⟨g, a, -, hga⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c S z z').1 hx
  have h1 := (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c S T φ z z' w w g (a : S) hga hz).1 hz'
  have h2 := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c T w w w).1
  obtain ⟨hg, ha⟩ := (GlobalTheory.T.frameChange_exists_unique_of_same_point E H Dw l Xo c T w w).2 _ _ _ _ h1 h2
  have ha1 : (a : S) = ((1 : Sˣ) : S) := hφ (by rw [ha]; simp)
  have hg1 : g = fun _ => 1 := by
    funext τ
    have h := congrFun hg τ
    ext i j
    apply hφ
    have hij := congrFun (congrFun h i) j
    simp only [Matrix.map_apply] at hij
    rw [hij]
    by_cases e : i = j
    · subst e; simp
    · simp [Matrix.one_apply_ne e]
  rw [ha1, hg1] at hga
  have h3 : FrChg (fun _ => 1) ((1 : Sˣ) : S) z z := (GlobalTheory.T.frameChangeByMatrices_refl_and_comp E H Dw l Xo c S z z z).1
  exact (GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c S z (fun _ => 1) 1 (fun _ => by simp)).unique h3 hga

end GlobalTheory.Frames
