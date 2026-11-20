import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PointSeparationPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLogCanonicalLocalEquationAddSmulDivisorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCanonicalAtIffOfIsLogCanonicalLocalEquationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalEquationEffectiveQCartierDivisorStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

/- English proof (translation)
Introduce `X _ _ _ p n hp hn Δ D δ x hD hk hl hδ hδ1`. Take `⟨η, m, g, hη, hm, hg, hkl⟩` from `hk`. Take `⟨m', f, hm', -, hf⟩` from `GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x`. Take `⟨m₁, g₁, hm₁, h₁, e₁⟩` from `GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hf`. Take `⟨m₂, g₂, hm₂, h₂, e₂⟩` from `GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hf`.

Rewrite `h₁` using `[one_smul]`. Establish `hlc` using `(GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ h₁).1 hl`. Use `⟨η, m₂, g₂, hη, hm₂, h₂, fun E hE => ?_⟩` and prove the remaining obligations. Establish `a` using `hkl E hE`. Establish `b` using `hlc E hE`.

Rewrite `b` using `[e₁]`. Rewrite using `[e₂]`. Use `set t : ℚ := (E.ord f : ℚ) / m'`. Use `set d := discrep E η m g`. Establish `h1 : -δ < δ * d` using `by nlinarith`.

Establish `h2 : -(1 - δ) ≤ (1 - δ) * (d - 1 * t)` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem kltAt_add_smul_of_lcAt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n →
    ∀ (Δ D : X → ℚ) (δ : ℚ) (x : X), IsQCart D → KltAt p n Δ x → LcAt p n (Δ + D) x → 0 < δ →
      δ ≤ 1 → KltAt p n (Δ + (1 - δ) • D) x := by
  intro X _ _ _ p n hp hn Δ D δ x hD hk hl hδ hδ1
  obtain ⟨η, m, g, hη, hm, hg, hkl⟩ := hk
  obtain ⟨m', f, hm', -, hf⟩ := GlobalTheory.T.exists_localEquation_effectiveQCartierDivisor X p D hD x
  obtain ⟨m₁, g₁, hm₁, h₁, e₁⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f 1 hm hm' hg hf
  obtain ⟨m₂, g₂, hm₂, h₂, e₂⟩ := GlobalTheory.T.isLogCanonicalLocalEquation_add_smul_divisor X p n Δ D η x m m' g f (1 - δ) hm hm' hg hf
  rw [one_smul] at h₁
  have hlc := (GlobalTheory.T.logCanonicalAt_iff_of_isLogCanonicalLocalEquation X p n hp hn (Δ + D) η x m₁ g₁ hη hm₁ h₁).1 hl
  refine ⟨η, m₂, g₂, hη, hm₂, h₂, fun E hE => ?_⟩
  have a := hkl E hE
  have b := hlc E hE
  rw [e₁] at b
  rw [e₂]
  set t : ℚ := (E.ord f : ℚ) / m'
  set d := discrep E η m g
  have h1 : -δ < δ * d := by nlinarith
  have h2 : -(1 - δ) ≤ (1 - δ) * (d - 1 * t) := by nlinarith
  nlinarith

end GlobalTheory.PairStep
