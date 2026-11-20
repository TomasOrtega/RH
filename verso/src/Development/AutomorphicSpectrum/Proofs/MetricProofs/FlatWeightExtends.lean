import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.CompRightEqZero
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SingularPotentialLogGrowthPshStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PshExtensionAcrossClosedDenseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothExtensionAcrossClosedDenseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BoundedPshCorrectionLocallySmoothStatement

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder ContDiff

namespace GlobalTheory.CompanionTheory.Ar.PB.Flat

/- English proof (translation)
Introduce `e X _ _ _ A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hp' hb`. Establish `hthm : IsPotential A (th.rsmul (-1))` using `isPotentialRsmul A (-1) th hth`. Establish `hum : A.SmoothOn (bdry s)ᶜ (fun y => -u y)` using `fun j => (hu j).neg`. Establish `hpm : IsPshOn A (bdry s)ᶜ (th.rsmul (-1) + LocPot.ofFun (fun y => -u y))`. Introduce `x j y hy w`.

Establish `hf : (((th.rsmul (-1) + LocPot.ofFun (fun y => -u y)).φ x) ∘ (A.chart j).symm) = (((th + LocPot.ofFun u).rsmul (-1)).φ x) ∘ (A.chart j).symm`. Use function extensionality and compare the values at `z`. Simplify using `only [Function.comp, LocPot.rsmul]`. Use `show -1 * th.φ x _ + -u _ = -1 * (th.φ x _ + u _)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hf]`. Conclude with `hp' x j y hy w`. Take `⟨C5, h5⟩` from `GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hb`. Take `⟨C6, h6⟩` from `GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn (th.rsmul (-1)) (fun y => -u y) C₁ hthm hum hpm (fun y hy => by simpa using hb y hy)`. Establish `hM : ∀ y ∉ bdry s, |u y| ≤ max C5 C6`.

Introduce `y hy`. Establish `a` using `(h5.2.2.2 y hy).2`. Establish `b` using `(h6.2.2.2 y hy).2`. Rewrite using `[abs_le]`. Prove the components needed by the constructor for the conclusion.

Use `le_max_right C5 C6` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `a.trans (le_max_left _ _)`. Take `⟨hcl, hde⟩` from `GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc`. Take `⟨u', hu', heq⟩` from `GlobalTheory.T.smooth_extension_across_closed_dense e X A (bdry s) u hcl hde (GlobalTheory.T.bounded_psh_correction_locally_smooth e X A L s nb m W hs hsnc th u _ hth hu hp hp' hM)`.

Establish `hsm : ∀ x, A.SmoothOn ((th + LocPot.ofFun u').U x) ((th + LocPot.ofFun u').φ x)`. Introduce `x j`. Establish `h1 : ContDiffOn ℝ ∞ (th.φ x ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x))` using `(hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩`. Establish `h2 : ContDiffOn ℝ ∞ (u' ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x))` using `(hu' j).mono fun y hy => ⟨hy.1, trivial⟩`. Conclude with `h1.add h2`.

Use `⟨u', hu', heq, ?_, ?_⟩` and prove the remaining obligations. Use `GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) (th + LocPot.ofFun u) (th + LocPot.ofFun u') hcl hde (fun _ => rfl) hsm ?_ hp` and prove the remaining obligations. Introduce `x y _ hy`. Use `show th.φ x y + u' y = th.φ x y + u y`. Rewrite using `[heq y hy]`.

Use `GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) ((th + LocPot.ofFun u).rsmul (-1)) ((th + LocPot.ofFun u').rsmul (-1)) hcl hde (fun _ => rfl) ?_ ?_ hp'` and prove the remaining obligations. Introduce `x j`. Use `(hsm x j).const_smul (-1 : ℝ)` as an intermediate fact. Use `this.congr fun y _ => ?_` and prove the remaining obligations. Simplify using `[LocPot.rsmul]`.

Introduce `x y _ hy show -1 * (th.φ x y + u' y) = -1 * (th.φ x y + u y)`. Rewrite using `[heq y hy]`.
-/
theorem flat_weight_extends : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : LocPot X) (u : X → ℝ) (C₁ : ℝ), IsPotential A th → A.SmoothOn (bdry s)ᶜ u → IsPshOn A (bdry s)ᶜ (th + LocPot.ofFun u) → IsPshOn A (bdry s)ᶜ ((th + LocPot.ofFun u).rsmul (-1)) → (∀ y ∉ bdry s, |u y| ≤ C₁ * Real.log (rW L s y)) → ∃ u' : X → ℝ, A.Smooth u' ∧ (∀ y ∉ bdry s, u' y = u y) ∧ IsPsh A (th + LocPot.ofFun u') ∧ IsPsh A ((th + LocPot.ofFun u').rsmul (-1)) := by
  intro e X _ _ _ A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hp' hb
  have hthm : IsPotential A (th.rsmul (-1)) := isPotentialRsmul A (-1) th hth
  have hum : A.SmoothOn (bdry s)ᶜ (fun y => -u y) := fun j => (hu j).neg
  have hpm : IsPshOn A (bdry s)ᶜ (th.rsmul (-1) + LocPot.ofFun (fun y => -u y)) := by
    intro x j y hy w
    have hf : (((th.rsmul (-1) + LocPot.ofFun (fun y => -u y)).φ x) ∘ (A.chart j).symm) =
        (((th + LocPot.ofFun u).rsmul (-1)).φ x) ∘ (A.chart j).symm := by
      funext z
      simp only [Function.comp, LocPot.rsmul]
      show -1 * th.φ x _ + -u _ = -1 * (th.φ x _ + u _)
      ring
    rw [hf]
    exact hp' x j y hy w
  obtain ⟨C5, h5⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn th u C₁ hth hu hp hb
  obtain ⟨C6, h6⟩ := GlobalTheory.T.singular_potential_log_growth_psh e X A L s nb m W hL hs hsnc hn (th.rsmul (-1)) (fun y => -u y) C₁ hthm hum hpm
    (fun y hy => by simpa using hb y hy)
  have hM : ∀ y ∉ bdry s, |u y| ≤ max C5 C6 := by
    intro y hy
    have a := (h5.2.2.2 y hy).2
    have b := (h6.2.2.2 y hy).2
    rw [abs_le]
    constructor
    · have := le_max_right C5 C6; linarith
    · exact a.trans (le_max_left _ _)
  obtain ⟨hcl, hde⟩ := GlobalTheory.T.section_boundary_closed_and_codense e X A L s nb m W hs hsnc
  obtain ⟨u', hu', heq⟩ := GlobalTheory.T.smooth_extension_across_closed_dense e X A (bdry s) u hcl hde
    (GlobalTheory.T.bounded_psh_correction_locally_smooth e X A L s nb m W hs hsnc th u _ hth hu hp hp' hM)
  have hsm : ∀ x, A.SmoothOn ((th + LocPot.ofFun u').U x) ((th + LocPot.ofFun u').φ x) := by
    intro x j
    have h1 : ContDiffOn ℝ ∞ (th.φ x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hth.1 x j).mono fun y hy => ⟨hy.1, hy.2.1⟩
    have h2 : ContDiffOn ℝ ∞ (u' ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((th + LocPot.ofFun u').U x)) :=
      (hu' j).mono fun y hy => ⟨hy.1, trivial⟩
    exact h1.add h2
  refine ⟨u', hu', heq, ?_, ?_⟩
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) (th + LocPot.ofFun u) (th + LocPot.ofFun u') hcl hde
      (fun _ => rfl) hsm ?_ hp
    intro x y _ hy
    show th.φ x y + u' y = th.φ x y + u y
    rw [heq y hy]
  · refine GlobalTheory.T.psh_extension_across_closed_dense e X A (bdry s) ((th + LocPot.ofFun u).rsmul (-1))
      ((th + LocPot.ofFun u').rsmul (-1)) hcl hde (fun _ => rfl) ?_ ?_ hp'
    · intro x j
      have := (hsm x j).const_smul (-1 : ℝ)
      refine this.congr fun y _ => ?_
      simp [LocPot.rsmul]
    · intro x y _ hy
      show -1 * (th.φ x y + u' y) = -1 * (th.φ x y + u y)
      rw [heq y hy]

end GlobalTheory.CompanionTheory.Ar.PB.Flat
