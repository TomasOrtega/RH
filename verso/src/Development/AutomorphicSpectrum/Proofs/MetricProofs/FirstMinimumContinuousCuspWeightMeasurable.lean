import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.CuspWeightInvariantUnderIsometryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FirstMinimumAndCuspWeightBoundsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallAutomorphismInverseExists
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousHermitianMatrixFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasurableCuspWeightFamilyStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsometryPreservesHermitianAndActionStatement
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas

/- English proof (translation)
Introduce `E _ _ _ Ψ _ j j' n g Λ _ _ F hj`. Establish `hO : IsOpen (ballDom F.q)` using `BallInverse.isOpen_ballDom F.q`. Set `U` to `↥(ballDom F.q)`. Set `R : U → RiemLat E g Λ` to `fun t => F.R t.1`. Establish `hP : ∀ v, Continuous fun x : U => (R x).P v` using `fun v => continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn`.

Establish `hH : Continuous fun x : U => (R x).Hm` using `GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U R F.form (fun x => F.form_eq _) hP`. Establish `hlam : Continuous fun x : U => (R x).lam1` using `GlobalTheory.T.continuous_first_minimum_family E g Λ U R hP hH`. Establish `hnz : ∀ I, Continuous fun x : U => (R x).nz F.σ I` using `fun I => GlobalTheory.T.continuous_cusp_norm_family E g Λ Ψ U R F.σ I hP hH`. Establish `hbdd : ∀ x : U, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz F.σ I)}`. Introduce `x`.

Establish `hr : (R x).HasRank F.σ j'` using `fun τ => (F.sig x.1 x.2 τ).1`. Take `⟨-, -, h3, -, -⟩` from `GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (R x) F.σ j' F.cm hr hj`. Use `⟨(R x).cuspW F.σ, ?_⟩` and prove the remaining obligations. Introduce and unpack `y ⟨I, hI, rfl⟩`. Conclude with `(h3 I hI).1`.

Establish `hcw : Measurable fun x : U => (R x).cuspW F.σ` using `GlobalTheory.T.measurable_cusp_weight_family E g Λ Ψ U R F.σ F.form (fun x => F.form_eq _) (fun I => (hnz I).measurable) hbdd`. Use `⟨continuousOn_iff_continuous_restrict.2 hlam, ?_, hO, ?_⟩` and prove the remaining obligations. Establish `e : (ballDom F.q).indicator (fun t => (F.R t).cuspW F.σ) = fun t => if h : t ∈ ballDom F.q then (R ⟨t, h⟩).cuspW F.σ else 0`. Use function extensionality and compare the values at `t`. Apply the tactic sequence `by_cases h : t ∈ ballDom F.q <;> simp [h, R]`.

Rewrite using `[e]`. Conclude with `Measurable.dite (s := ballDom F.q) hcw measurable_const hO.measurableSet`. Introduce and unpack `t ht t' ht' ⟨γ, hγ, φ, hφ⟩`. Establish `hf : ∀ x y, (F.R t').form (γ x) (γ y) = (F.R t).form x y` using `fun x y => by`. Rewrite using `[F.form_eq, F.form_eq]`.

Conclude with `hγ x y`. Take `⟨h1, h2⟩` from `GlobalTheory.T.isometry_preserves_hermitian_and_action E g Λ (F.R t) (F.R t') γ φ hf hφ`. Establish `himg : φ '' Set.range (F.R t).P = Set.range (F.R t').P`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨_, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨γ x, hφ x⟩`. Introduce and unpack `⟨y, rfl⟩`. Use `⟨_, ⟨γ.symm y, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hφ, γ.apply_symm_apply]`.

Apply the tactic sequence `obtain ⟨a, b, -⟩ := GlobalTheory.T.cusp_weight_invariant_under_isometry E g Λ Ψ (F.R t) F.σ g Λ (F.R t') φ F.cm himg h1 h2`. Conclude with `⟨b.symm, a.symm⟩`.
-/
theorem first_minimum_cusp_weight_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), 1 ≤ j' → ContinuousOn (fun t => (F.R t).lam1) (ballDom F.q) ∧ Measurable ((ballDom F.q).indicator fun t => (F.R t).cuspW F.σ) ∧ IsOpen (ballDom F.q) ∧ ∀ t ∈ ballDom F.q, ∀ t' ∈ ballDom F.q, F.Eqv (autGrp F.form) t t' → (F.R t).lam1 = (F.R t').lam1 ∧ (F.R t).cuspW F.σ = (F.R t').cuspW F.σ := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F hj
  have hO : IsOpen (ballDom F.q) := BallInverse.isOpen_ballDom F.q
  let U := ↥(ballDom F.q)
  let R : U → RiemLat E g Λ := fun t => F.R t.1
  have hP : ∀ v, Continuous fun x : U => (R x).P v := fun v =>
    continuousOn_iff_continuous_restrict.1 (F.hol.2 v).continuousOn
  have hH : Continuous fun x : U => (R x).Hm := GlobalTheory.T.continuous_hermitian_matrix_family E g Λ U R F.form (fun x => F.form_eq _) hP
  have hlam : Continuous fun x : U => (R x).lam1 := GlobalTheory.T.continuous_first_minimum_family E g Λ U R hP hH
  have hnz : ∀ I, Continuous fun x : U => (R x).nz F.σ I := fun I => GlobalTheory.T.continuous_cusp_norm_family E g Λ Ψ U R F.σ I hP hH
  have hbdd : ∀ x : U, BddAbove {y | ∃ I, (R x).IsCusp I ∧ y = -Real.log ((R x).nz F.σ I)} := by
    intro x
    have hr : (R x).HasRank F.σ j' := fun τ => (F.sig x.1 x.2 τ).1
    obtain ⟨-, -, h3, -, -⟩ := GlobalTheory.T.first_minimum_and_cusp_weight_bounds E g Λ Ψ (R x) F.σ j' F.cm hr hj
    refine ⟨(R x).cuspW F.σ, ?_⟩
    rintro y ⟨I, hI, rfl⟩
    exact (h3 I hI).1
  have hcw : Measurable fun x : U => (R x).cuspW F.σ :=
    GlobalTheory.T.measurable_cusp_weight_family E g Λ Ψ U R F.σ F.form (fun x => F.form_eq _) (fun I => (hnz I).measurable) hbdd
  refine ⟨continuousOn_iff_continuous_restrict.2 hlam, ?_, hO, ?_⟩
  · classical
    have e : (ballDom F.q).indicator (fun t => (F.R t).cuspW F.σ) =
        fun t => if h : t ∈ ballDom F.q then (R ⟨t, h⟩).cuspW F.σ else 0 := by
      funext t
      by_cases h : t ∈ ballDom F.q <;> simp [h, R]
    rw [e]
    exact Measurable.dite (s := ballDom F.q) hcw measurable_const hO.measurableSet
  · rintro t ht t' ht' ⟨γ, hγ, φ, hφ⟩
    have hf : ∀ x y, (F.R t').form (γ x) (γ y) = (F.R t).form x y := fun x y => by
      rw [F.form_eq, F.form_eq]
      exact hγ x y
    obtain ⟨h1, h2⟩ := GlobalTheory.T.isometry_preserves_hermitian_and_action E g Λ (F.R t) (F.R t') γ φ hf hφ
    have himg : φ '' Set.range (F.R t).P = Set.range (F.R t').P := by
      ext z
      constructor
      · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
        exact ⟨γ x, hφ x⟩
      · rintro ⟨y, rfl⟩
        refine ⟨_, ⟨γ.symm y, rfl⟩, ?_⟩
        rw [← hφ, γ.apply_symm_apply]
    obtain ⟨a, b, -⟩ := GlobalTheory.T.cusp_weight_invariant_under_isometry E g Λ Ψ (F.R t) F.σ g Λ (F.R t') φ F.cm himg h1 h2
    exact ⟨b.symm, a.symm⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.FamilyMeas
