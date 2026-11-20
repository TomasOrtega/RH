import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsCoordLattice
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.LogOmBound
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.FlatSat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieSignatureNumberField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyUniformisationStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatTheoremOfResolutionGagaStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.KroneckerCharacterPeriodFormulaStatement
import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ExistsSmulMemSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open GroundTheory.Heights₂.Heights

namespace LevelTowerAlt

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0`. Use `congrArg Complex.im H.sqrt_neg_disc_sq` as an intermediate fact. Simplify `this` using `[pow_two, Complex.mul_im]`. Establish `h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ)`.

Use `congrArg Complex.re H.sqrt_neg_disc_sq` as an intermediate fact. Simplify `this` using `[pow_two, Complex.mul_re]`. Establish `hre : H.rt0.re = 0`. Break down `mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3` into its components or cases. Conclude with `h3`.

Rewrite `h2` using `[h3]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply the tactic sequence `refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩`. Rewrite `h2` using `[h]`. Simplify using `at h2`.

Conclude with `H.d_prime.ne_zero h2`.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 ∧ H.rt0 ≠ 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    have := congrArg Complex.im H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_im] using this
  have h2 : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    have := congrArg Complex.re H.sqrt_neg_disc_sq
    simpa [pow_two, Complex.mul_re] using this
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im = 0 by linarith) with h3 | h3
    · exact h3
    · rw [h3] at h2
      nlinarith [mul_self_nonneg H.rt0.re]
  refine ⟨by apply Complex.ext <;> simp [hre], fun h => ?_⟩
  rw [h] at h2
  simp at h2
  exact H.d_prime.ne_zero h2

end LevelTowerAlt
