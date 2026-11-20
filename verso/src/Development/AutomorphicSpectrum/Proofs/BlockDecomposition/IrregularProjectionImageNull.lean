import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatiosEqOfSameOrbit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepMetricSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ComplexPointLiftsToMulticoneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordsBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSheetB
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section

namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

open GlobalTheory.CompanionTheory.MPDict.SmoothRep (rt mem_mchart ev_rt)

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

def ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) (p : ∀ k, Bk n k) (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) :
    (Σ k, Bk n k) → ℂ :=
  fun q => ev (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) ((i.appLE (mchart p) (i ⁻¹ᵁ mchart p) le_rfl).hom (rt p q)) y

/- English proof (translation)
The claim follows from `(mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)`.
-/
theorem mem_ptsIn_of_over {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    y ∈ ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
  (mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).2 (mem_mchart H hp)

/- English proof (translation)
The claim follows from `(CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _ (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)`.
-/
theorem ratioVec_apply {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0)
    (q : Σ k, Bk n k) : ratioVec i p y q = z q / z ⟨q.1, p q.1⟩ :=
  (CxPts.ev_appLE_of_comp (r := i) (m := PtsOver.map i rfl _) (fun _ => rfl) le_rfl _
    (mem_ptsIn_of_over i H hp)).trans (ev_rt H hp q)

/- English proof (translation)
Use `⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩` and prove the remaining obligations. Rewrite using `[ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]`.
-/
theorem sameOrbit_ratioVec {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) {p : ∀ k, Bk n k}
    {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (hp : ∀ k, z ⟨k, p k⟩ ≠ 0) :
    SameOrbit z (ratioVec i p y) := by
  refine ⟨fun k => z ⟨k, p k⟩, hp, funext fun q => ?_⟩
  rw [ratioVec_apply i H hp q, mul_div_cancel₀ _ (hp q.1)]

/- English proof (translation)
Take `⟨z, -, hz⟩` from `GlobalTheory.T.complex_point_lifts_to_multicone m n X i y`. Establish `h : ∃ z, Over i y z` using `⟨z, hz⟩`. Rewrite using `[liftOf, dif_pos h]`. Conclude with `h.choose_spec`.
-/
theorem over_liftOf {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) : Over i y (liftOf i y) := by
  obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
  have h : ∃ z, Over i y z := ⟨z, hz⟩
  rw [liftOf, dif_pos h]
  exact h.choose_spec

/- English proof (translation)
Use `choose p hp using fun k => exists_block_ne_zero_of_isUnder H k`. Establish `hyW` using `mem_ptsIn_of_over i H hp`. Establish `hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p))` using `c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)`. Establish `hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)` using `⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩`. Establish `hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y)` using `differentiableAt_pi.2 fun q => (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt`.

Establish `hs` using `ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl`. Set `L` to `LinearMap.toContinuousLinearMap Ψ`. Establish `hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y)` using `L.differentiableAt.comp _ hs`. Establish `hc (a : Fin (D + 1))` using `differentiableAt_pi.1 hL a`. Establish `hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0`.

Take `⟨l, hl0, e⟩` from `sameOrbit_ratioVec i H hp`. Introduce `h`. Apply `h0` to reduce the goal to its premises. Rewrite using `[segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]`. Establish `hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0`.

Rewrite using `[c.finChart.left_inv hy]`. Conclude with `hne`. Establish `hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)] fun v => ratios Ψ (ratioVec i p (c.finChart.symm v))` using `by filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0`. Establish `H'` using `over_liftOf i (c.finChart.symm v)`. Establish `hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0` using `fun k => (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k) ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))`.

Conclude with `ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0`. Use `DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev` and prove the remaining obligations. Simplify using `only [ratios, div_eq_mul_inv]`. Conclude with `(hc a.succ).mul ((hc 0).inv hne')`.
-/
theorem differentiableAt_projCoord {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (Ψ : LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D) {y : GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀}
    (hy : y ∈ c.e.source) {z : (Σ k, Bk n k) → ℂ} (H : Over i y z) (h0 : Ψ (segre z) 0 ≠ 0) :
    DifferentiableAt ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) := by
  choose p hp using fun k => exists_block_ne_zero_of_isUnder H k
  have hyW := mem_ptsIn_of_over i H hp
  have hOo : IsOpen (c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p)) :=
    c.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn _)
  have hv : c.finChart y ∈ c.finChart.target ∩ c.finChart.symm ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ (i ⁻¹ᵁ mchart p) :=
    ⟨c.finChart.map_source hy, by rwa [Set.mem_preimage, c.finChart.left_inv hy]⟩
  have hl : DifferentiableAt ℂ (fun v => ratioVec i p (c.finChart.symm v)) (c.finChart y) :=
    differentiableAt_pi.2 fun q =>
      (((c.analyticOnNhd_finChart_iff (isOpen_ptsIn _) _).2 (c.holo _ _)) _ hv).differentiableAt
  have hs := ReciprocityTheory.ChartRestriction.G.Geo.segre_differentiableAt hl
  let L := LinearMap.toContinuousLinearMap Ψ
  have hL : DifferentiableAt ℂ (fun v => L (segre (ratioVec i p (c.finChart.symm v)))) (c.finChart y) :=
    L.differentiableAt.comp _ hs
  have hc (a : Fin (D + 1)) := differentiableAt_pi.1 hL a
  have hne : Ψ (segre (ratioVec i p y)) 0 ≠ 0 := by
    obtain ⟨l, hl0, e⟩ := sameOrbit_ratioVec i H hp
    intro h
    apply h0
    rw [segre_orbit e, map_smul, Pi.smul_apply, h, smul_zero]
  have hne' : L (segre (ratioVec i p (c.finChart.symm (c.finChart y)))) 0 ≠ 0 := by
    rw [c.finChart.left_inv hy]
    exact hne
  have hev : (projCoord i Ψ ∘ c.finChart.symm) =ᶠ[nhds (c.finChart y)]
      fun v => ratios Ψ (ratioVec i p (c.finChart.symm v)) := by
    filter_upwards [hOo.mem_nhds hv, (hc 0).continuousAt.eventually_ne hne'] with v hvO hv0
    have H' := over_liftOf i (c.finChart.symm v)
    have hp' : ∀ k, liftOf i (c.finChart.symm v) ⟨k, p k⟩ ≠ 0 := fun k =>
      (H' k (p k)).1.1 (ptsIn_mono (mchart_le p k)
        ((mem_ptsIn_preimage (f := i) (m := PtsOver.map i rfl _) fun _ => rfl).1 hvO.2))
    exact ratios_eq_of_sameOrbit Ψ (sameOrbit_ratioVec i H' hp') hv0
  refine DifferentiableAt.congr_of_eventuallyEq (differentiableAt_pi.2 fun a => ?_) hev
  simp only [ratios, div_eq_mul_inv]
  exact (hc a.succ).mul ((hc 0).inv hne')

/- English proof (translation)
Introduce `m n X _ i _ D Ψ c`. Use `set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA`. Establish `e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A)`. Rewrite using `[Set.image_image]`. Conclude with `Set.image_congr fun y hy => by`.

Simplify using `only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]`. Rewrite using `[e]`. Use `addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩`. Conclude with `((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt`.

Introduce and unpack `_ ⟨y, ⟨-, -, hc⟩, rfl⟩`. Establish `h0` using `not_not.1 hc`. Establish `hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det = Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))` using `LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))`. Rewrite using `[hdet, h0, Algebra.norm_complex_apply, map_zero]`.
-/
theorem volume_image_crit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0}) [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ)
    (Ψ : GlobalTheory.CompanionTheory.MixZ.ArchEq.LinProj n D) (c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D),
    volume (GlobalTheory.CompanionTheory.MixZ.ArchEq.projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, GlobalTheory.CompanionTheory.MixZ.ArchEq.Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ GlobalTheory.CompanionTheory.MixZ.ArchEq.IsRegAt i Ψ c y}) = 0 := by
  intro m n X _ i _ D Ψ c
  set A := {y | y ∈ c.e.source ∧ (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y} with hA
  have e : projCoord i Ψ '' A = (projCoord i Ψ ∘ c.finChart.symm) '' (c.finChart '' A) := by
    rw [Set.image_image]
    exact Set.image_congr fun y hy => by
      simp only [Function.comp_apply, c.finChart.left_inv (show y ∈ c.finChart.source from hy.1)]
  rw [e]
  refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fun v => (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) v).restrictScalars ℝ) ?_ ?_
  · rintro _ ⟨y, ⟨hy, ⟨z, hz, h0⟩, -⟩, rfl⟩
    exact ((differentiableAt_projCoord i Ψ c hy hz h0).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  · rintro _ ⟨y, ⟨-, -, hc⟩, rfl⟩
    have h0 := not_not.1 hc
    have hdet : ((fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y)).restrictScalars ℝ).det =
        Algebra.norm ℝ (LinearMap.det (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
          (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      LinearMap.det_restrictScalars (f := (fderiv ℂ (projCoord i Ψ ∘ c.finChart.symm) (c.finChart y) :
        (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))
    rw [hdet, h0, Algebra.norm_complex_apply, map_zero]

end GlobalTheory.CompanionTheory.MixZ.ArchEq
