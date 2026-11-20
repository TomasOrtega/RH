import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CentralIdemCoeff
import Formalism.SharpRestriction.LevelLetterCocycles.IdempotentChoiceDepthZero
import Formalism.SharpRestriction.LevelLetterCocycles.TableLineDegreeTwo
import Formalism.SharpRestriction.LevelLetterCocycles.AdmissibleParameterJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleParametersOfLargeScale
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StatementJAll
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.LargeJumps

/- English proof (translation)
Introduce `eps Fm`. Take `⟨i0⟩` from `Fm.Ix_zero`. Establish `heps : 0 < eps`. Establish `h` using `(Fm.L 0 i0).sc.eps_pos`. Rewrite `h` using `[Fm.L_eps]`. Then use the resulting hypothesis.

Take `⟨x0, hx0⟩` from `GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps`. Use `⟨x0, fun x hxx hx a hF => ?_⟩` and prove the remaining obligations. Establish `hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0`. Establish `h` using `congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)`. Simplify using `only [parConsts] at h`.

Conclude with `le_of_eq (by simpa using h)`. Establish `hA` using `(hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC (by rw [Fm.L_x x a hx]; exact hxx)).1`. Conclude with `GlobalTheory.JumpStatement.holds_all _ _ (hF.admJ _ hA)`.
-/
theorem jump_bound_of_facts_large_family : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (a : Fm.Ix x),
    GlobalTheory.NFacts.Facts (Fm.D x a) (Fm.ex x hx a).nch → AdmissibleParameterJ.JumpConditions (Fm.L x a) := by
  intro eps Fm
  obtain ⟨i0⟩ := Fm.Ix_zero
  have heps : 0 < eps := by
    have h := (Fm.L 0 i0).sc.eps_pos
    rwa [Fm.L_eps] at h
  obtain ⟨x0, hx0⟩ := GlobalTheory.HTW.admissibleParameters_of_large_scale eps (Fm.PK.getD 7 0) heps
  refine ⟨x0, fun x hxx hx a hF => ?_⟩
  have hC : (Fm.params x hx a).CLw ≤ Fm.PK.getD 7 0 := by
    have h := congrArg (fun l : List ℝ => l.getD 7 0) (Fm.params_K x hx a)
    simp only [parConsts] at h
    exact le_of_eq (by simpa using h)
  have hA := (hx0 (Fm.D x a) (Fm.L x a) (Fm.params x hx a) (Fm.L_eps x a) hC
    (by rw [Fm.L_x x a hx]; exact hxx)).1
  exact GlobalTheory.JumpStatement.holds_all _ _ (hF.admJ _ hA)

end GlobalTheory.LargeJumps
