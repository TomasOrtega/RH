import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormFiniteFibresBirationalLinearSystem
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice GlobalTheory.HSShort
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFormFiniteFibresBirationalLinearSystem.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_form_finite_fibres_birational_linearSystem : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → S.BasePointFree → S.Birational → ∃ (d : ℕ) (g : MvPolynomial (Fin S.N) F), g.IsHomogeneous d ∧ g ∉ S.imageIdeal ∧ ∀ (K : Type) [Field K] [Algebra F K] (y : Fin S.N → K), {x : S.Pt K | aeval (S.coords x.1) g ≠ 0 ∧ ∃ c : K, S.coords x.1 = c • y}.Finite := by
  first | exact @GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | exact GlobalTheory.BirFiniteFibre.exists_form_finite_fibres | (intros; apply GlobalTheory.BirFiniteFibre.exists_form_finite_fibres <;> assumption)
