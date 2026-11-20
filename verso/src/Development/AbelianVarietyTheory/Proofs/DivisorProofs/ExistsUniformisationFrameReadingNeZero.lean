import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodCmPtFrPolyNeZero
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolyDivDet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TestPointValueEqConstMulReading
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestValueEqConstMulReadingSecZ
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c σ r U hU e F hF hF0`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Apply `hF0` to reduce the goal to its premises. Use function extensionality and compare the values at `p y`.

Use `show F p y = 0`. Use `Formalism.L2.Pj.eq_zero_of_cpts σ p _ fun ψ => ?_` and prove the remaining obligations. Take `⟨k, x, u, hk⟩` from `GlobalTheory.test_value_eq_const_mul_reading_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange U hU e p y ψ`. Establish `h` using `hk F hF`. Rewrite `h` using `[hcon k x.1 x.2, mul_zero]`.

Conclude with `h`.
-/
theorem exists_rdU_ne_zero_of_mem_secZ : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (e : Ix Dw → ℤ), ∀ F ∈ GlobalTheory.AllWt.secZ Xo c e, F ≠ 0 → ∃ k, ∃ x ∈ (U.X k).dom, rdU U F k x ≠ 0 := by
  intro E _ _ _ H Dw l Xo c σ r U hU e F hF hF0
  by_contra hcon
  push_neg at hcon
  apply hF0
  funext p y
  show F p y = 0
  refine Formalism.L2.Pj.eq_zero_of_cpts σ p _ fun ψ => ?_
  obtain ⟨k, x, u, hk⟩ :=
    GlobalTheory.test_value_eq_const_mul_reading_secZ GlobalTheory.abelianSchemeLaws_all.1.secBaseChange U hU e p y ψ
  have h := hk F hF
  rw [hcon k x.1 x.2, mul_zero] at h
  exact h

end GlobalTheory
