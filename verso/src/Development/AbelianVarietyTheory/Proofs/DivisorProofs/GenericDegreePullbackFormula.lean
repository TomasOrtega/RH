import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartOverProperClosedEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleChartCoveringComplexPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChartStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartPreimageOfFiniteLiftedChartCoveringStatement
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GdegPullProof

/- English proof (translation)
Simplify using `[Weight.chernInt, Measure.real]`.
-/
theorem chernInt_one {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {B : LB X} (φ : Weight p σ B) (D : ℕ) :
    φ.chernInt D Set.univ (fun _ => 1) =
      (φ.chernPart D 1 Set.univ).toReal - (φ.chernPart D (-1) Set.univ).toReal := by
  simp [Weight.chernInt, Measure.real]

/- English proof (translation)
Take `⟨U, hUη, hU⟩` from `GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hX hY π hπ hη hδ`. Take `⟨hcard, hchart, hlift⟩` from `hU σ`. Establish `hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U)`. Use extensionality with `z`. Simplify using `only [Set.mem_preimage, mem_ptsIn]`.

Both sides reduce to the same expression. Establish `hcY : (ptsIn q σ (π ⁻¹ᵁ U))ᶜ = {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ}`. Use extensionality with `z`. Simplify using `[mem_ptsIn]`. Establish `hcX : (ptsIn p σ U)ᶜ = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ}`.

Use extensionality with `y`. Simplify using `[mem_ptsIn]`. Establish `h0Y` using `GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ (π ⁻¹ᵁ U).isOpen.isClosed_compl (by simp [hη, hUη]) σ ((L.φ σ).pull π hπ) ε`. Establish `h0X` using `GlobalTheory.T.chernPart_over_properClosed_eq_zero hX ((U : X.Opens) : Set X)ᶜ U.isOpen.isClosed_compl (by simp [hUη]) σ (L.φ σ) ε`. Rewrite `h0Y` using `[← hcY]`.

Rewrite `h0X` using `[← hcX]`. Establish `h3` using `GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hX hY π hπ (L.φ σ) (L.cInf σ) ε (ptsIn p σ U) (isOpen_ptsIn U) _ hcard hchart hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart π hπ (L.φ σ) (L.cInf σ) c c' hc w hw) _ (isOpen_ptsIn …`. Rewrite `h3` using `[hpre]`. Rewrite using `[← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3, ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]`.
-/
theorem mass {k : Type} [CommRing k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {D : ℕ} (hX : IsArithVar p D) (hY : IsArithVar q D)
    (π : Y ⟶ X) (hπ : π ≫ p = q) (hη : π (genericPoint Y) = genericPoint X)
    (hδ : π.residueDegree (genericPoint Y) ≠ 0) (L : HermLB p) (σ : k →+* ℂ) (ε : ℤˣ) :
    ((L.φ σ).pull π hπ).chernPart D ε Set.univ =
      (π.residueDegree (genericPoint Y) : ℝ≥0∞) * (L.φ σ).chernPart D ε Set.univ := by
  obtain ⟨U, hUη, hU⟩ := GlobalTheory.T.exists_open_etaleChart_covering_complexPoints hX hY π hπ hη hδ
  obtain ⟨hcard, hchart, hlift⟩ := hU σ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have hcY : (ptsIn q σ (π ⁻¹ᵁ U))ᶜ =
      {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ} := by
    ext z
    simp [mem_ptsIn]
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have h0Y := GlobalTheory.T.chernPart_over_properClosed_eq_zero hY ((π ⁻¹ᵁ U : Y.Opens) : Set Y)ᶜ (π ⁻¹ᵁ U).isOpen.isClosed_compl
    (by simp [hη, hUη]) σ ((L.φ σ).pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_over_properClosed_eq_zero hX ((U : X.Opens) : Set X)ᶜ U.isOpen.isClosed_compl (by simp [hUη]) σ
    (L.φ σ) ε
  rw [← hcY] at h0Y
  rw [← hcX] at h0X
  have h3 := GlobalTheory.T.chernPart_preimage_of_finite_liftedChartCovering hX hY π hπ (L.φ σ) (L.cInf σ) ε (ptsIn p σ U) (isOpen_ptsIn U) _ hcard
    hchart hlift (fun c c' hc w hw => GlobalTheory.T.chernDensity_pullbackWeight_in_liftedChart π hπ (L.φ σ) (L.cInf σ) c c' hc w hw) _
    (isOpen_ptsIn U).measurableSet subset_rfl
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.GdegPullProof

namespace GlobalTheory.CovTest

/- English proof (translation)
Introduce `k _ X Y _ _ p q D hX hY π hπ hη hδ L`. Establish `key : ∀ σ, ((L.pull π hπ).φ σ).chernInt D Set.univ (fun _ => 1) = (π.residueDegree (genericPoint Y) : ℝ) * (L.φ σ).chernInt D Set.univ (fun _ => 1)`. Introduce `σ`. Express the relevant statement in the definitionally equal form `((L.φ σ).pull π hπ).chernInt D Set.univ (fun _ => 1) = _`. Rewrite using `[GdegPullProof.chernInt_one, GdegPullProof.chernInt_one, GdegPullProof.mass hX hY π hπ hη hδ L σ 1, GdegPullProof.mass hX hY π hπ hη hδ L σ (-1), ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]`.

Simplify using `only [gdeg, chInt]`. Repeatedly rewrite using `[key]`. Rewrite using `[mul_finsum]`.
-/
theorem gdegPull : GdegPull := by
  intro k _ X Y _ _ p q D hX hY π hπ hη hδ L
  have key : ∀ σ, ((L.pull π hπ).φ σ).chernInt D Set.univ (fun _ => 1) =
      (π.residueDegree (genericPoint Y) : ℝ) * (L.φ σ).chernInt D Set.univ (fun _ => 1) := by
    intro σ
    change ((L.φ σ).pull π hπ).chernInt D Set.univ (fun _ => 1) = _
    rw [GdegPullProof.chernInt_one, GdegPullProof.chernInt_one,
      GdegPullProof.mass hX hY π hπ hη hδ L σ 1, GdegPullProof.mass hX hY π hπ hη hδ L σ (-1),
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast, mul_sub]
  simp only [gdeg, chInt]
  simp_rw [key]
  rw [mul_finsum]

end GlobalTheory.CovTest

end
