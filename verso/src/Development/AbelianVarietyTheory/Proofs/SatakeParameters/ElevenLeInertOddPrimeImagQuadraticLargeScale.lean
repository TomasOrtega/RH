import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtPrime
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

/- English proof (translation)
Introduce `eps heps`. Use `⟨(11 : ℝ) ^ (5 / eps), ?_⟩` and prove the remaining obligations. Introduce `D L l he hx hl hin`. Establish `hlt` using `GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2`. Rewrite `hlt` using `[he]`.

Establish `h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps)` using `Real.rpow_nonneg (by norm_num) _`. Establish `hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5)` using `Real.rpow_le_rpow h0 hx (by positivity)`. Establish `h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11`. Rewrite using `[← Real.rpow_mul (by norm_num)]`. Establish `: 5 / eps * (eps / 5) = 1` using `by field_simp`.

Rewrite using `[this, Real.rpow_one]`. Establish `: (11 : ℝ) < l` using `by linarith`. Conclude with `this.le` after adjusting the coercions.
-/
theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
