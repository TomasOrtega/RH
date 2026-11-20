import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTpCuspIntegrable
set_option maxSynthPendingDepth 1
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.Giv

/- English proof (translation)
Introduce `II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X`. Take `⟨C, C', hC⟩` from `CuspWeightIntegrable.uFn_bound X`. Use `letI : MeasurableSpace X.M.Xc := borel X.M.Xc`. Use `haveI : BorelSpace X.M.Xc := ⟨rfl⟩`. Use `⟨fun x => 2 * CuspWeightIntegrable.uFn X x, 2 * max C C', ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `((CuspWeightIntegrable.measurable_uFn X).const_mul 2).indicator X.S.R.isOpen_Yo.measurableSet`. Introduce `x hx`. Establish `h1` using `hC x hx`. Establish `hl` using `Real.log_nonneg (X.S.R.one_le_r x hx)`. Establish `h2 : C' * Real.log (X.S.R.r x) ≤ max C C' * Real.log (X.S.R.r x)` using `mul_le_mul_of_nonneg_right (le_max_right _ _) hl`.

Establish `h3 : C ≤ max C C'` using `le_max_left _ _`. Rewrite using `[abs_mul, abs_two]`. Use the polynomial consequences of the given equalities and inequalities. Introduce `z hz hy`. Establish `hzB : z ∉ D.Bd`.

Introduce `hB`. Take `⟨z0, ⟨hz0X, hz0m⟩, hp⟩` from `X.S.Yo_sub _ hy`. Take `⟨c, hc, rfl⟩` from `(X.M.fibre z hz z0 hz0m).1 hp.symm`. Conclude with `hz0X.2 (D.bd_torus z hB c hc)`. Use `CuspWeightIntegrable.cuspWeight_eq X hz hzB hy` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cuspWeight_descends :
    ∀ (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (K : Type) [Fintype K] (ι : K → Type)
      [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (E : Ψ → Type) [∀ τ, AddCommGroup (E τ)]
      [∀ τ, Module Ω (E τ)] (D : ComponentData II Ψ K ι Ω E) (O Lt : Type) [CommRing O] [AddCommGroup Lt]
      [Module O Lt] (X : ComponentSetting D O Lt),
      ∃ (G : X.M.Xc → ℝ) (C : ℝ), @Measurable X.M.Xc ℝ (borel X.M.Xc) _ (X.S.R.Yo.indicator G) ∧
        (∀ x ∈ X.S.R.Yo, |G x| ≤ C + C * Real.log (X.S.R.r x)) ∧
        ∀ z ∈ mcPts (mCoordIdeal D.y), X.M.proj z ∈ X.S.R.Yo → X.Cd.cuspWeight z = G (X.M.proj z) := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X
  obtain ⟨C, C', hC⟩ := CuspWeightIntegrable.uFn_bound X
  letI : MeasurableSpace X.M.Xc := borel X.M.Xc
  haveI : BorelSpace X.M.Xc := ⟨rfl⟩
  refine ⟨fun x => 2 * CuspWeightIntegrable.uFn X x, 2 * max C C', ?_, ?_, ?_⟩
  · exact ((CuspWeightIntegrable.measurable_uFn X).const_mul 2).indicator X.S.R.isOpen_Yo.measurableSet
  · intro x hx
    have h1 := hC x hx
    have hl := Real.log_nonneg (X.S.R.one_le_r x hx)
    have h2 : C' * Real.log (X.S.R.r x) ≤ max C C' * Real.log (X.S.R.r x) :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hl
    have h3 : C ≤ max C C' := le_max_left _ _
    rw [abs_mul, abs_two]
    nlinarith
  · intro z hz hy
    have hzB : z ∉ D.Bd := by
      intro hB
      obtain ⟨z0, ⟨hz0X, hz0m⟩, hp⟩ := X.S.Yo_sub _ hy
      obtain ⟨c, hc, rfl⟩ := (X.M.fibre z hz z0 hz0m).1 hp.symm
      exact hz0X.2 (D.bd_torus z hB c hc)
    have := CuspWeightIntegrable.cuspWeight_eq X hz hzB hy
    linarith

end GlobalTheory.CompanionTheory.Ar.Giv
