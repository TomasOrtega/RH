import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormConvergesEquivariantHermitianStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothVectorsDenseInvariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupRepTwistedIsUnitaryRepStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnimodularBesselModelUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselMatrixCoeffExtendsBoundedEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BoundedEquivariantMapSmoothContinuousSeminormBouStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelEqOnOfContinuousOnAeEqStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf.BesselExt

variable {k r : ℕ}

/- English proof (translation)
Use `show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r`. Simplify using the standard rewrite rules.
-/
theorem one_memG : (1 : Mat k r) ∈ GG k r := by
  show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
  simp

/- English proof (translation)
Use `show (x * y)ᴴ * Hpk k r * (x * y) = Hpk k r`. Establish `hx' : xᴴ * Hpk k r * x = Hpk k r` using `hx`. Establish `hy' : yᴴ * Hpk k r * y = Hpk k r` using `hy`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [hx', hy']`.
-/
theorem mul_memG {x y : Mat k r} (hx : x ∈ GG k r) (hy : y ∈ GG k r) : x * y ∈ GG k r := by
  show (x * y)ᴴ * Hpk k r * (x * y) = Hpk k r
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  have hy' : yᴴ * Hpk k r * y = Hpk k r := hy
  calc (x * y)ᴴ * Hpk k r * (x * y) = yᴴ * (xᴴ * Hpk k r * x) * y := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hx', hy']

section Sm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg, hF, hFe⟩` from `hu g₀ hg₀`. Take `⟨U', F', hU', hg', hF', hFe'⟩` from `hu' g₀ hg₀`. Use `⟨U ∩ U', F + F', hU.inter hU', ⟨hg, hg'⟩, (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgH => ?_⟩` and prove the remaining obligations. Establish `e1` using `hFe g hg.1 hgH`.

Establish `e2` using `hFe' g hg.2 hgH`. Simplify using `only at e1 e2`. Simplify using `only [map_add, Pi.add_apply, e1, e2]`.
-/
theorem smooth_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u u' : H} (hu : IsSmoothVec σ u) (hu' : IsSmoothVec σ u') :
    IsSmoothVec σ (u + u') := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  obtain ⟨U', F', hU', hg', hF', hFe'⟩ := hu' g₀ hg₀
  refine ⟨U ∩ U', F + F', hU.inter hU', ⟨hg, hg'⟩, (hF.mono Set.inter_subset_left).add
    (hF'.mono Set.inter_subset_right), fun g hg hgH => ?_⟩
  have e1 := hFe g hg.1 hgH
  have e2 := hFe' g hg.2 hgH
  simp only at e1 e2
  simp only [map_add, Pi.add_apply, e1, e2]

/- English proof (translation)
Introduce `g₀ hg₀`. Take `⟨U, F, hU, hg, hF, hFe⟩` from `hu g₀ hg₀`. Use `⟨U, b • F, hU, hg, hF.const_smul b, fun g hg hgH => ?_⟩` and prove the remaining obligations. Establish `e1` using `hFe g hg hgH`. Simplify using `only at e1`.

Simplify using `only [map_smul, Pi.smul_apply, e1]`.
-/
theorem smooth_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {u : H} (b : ℂ) (hu : IsSmoothVec σ u) :
    IsSmoothVec σ (b • u) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hg, hF, hFe⟩ := hu g₀ hg₀
  refine ⟨U, b • F, hU, hg, hF.const_smul b, fun g hg hgH => ?_⟩
  have e1 := hFe g hg hgH
  simp only at e1
  simp only [map_smul, Pi.smul_apply, e1]

end Sm

/- English proof (translation)
Establish `hmp : MeasurePreserving (rmulM y : Mt k r → Mt k r) μG μG` using `⟨(continuous_rmulM y).measurable, hU.1 y hy⟩`. Conclude with `hmp.quasiMeasurePreserving.ae_eq_comp h`.
-/
theorem ae_rtrans {B : Type*} {μG : Measure (Mt k r)} (hU : IsUnimod (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (Matrix.of x * y)) =ᵐ[μG] fun x => g (Matrix.of x * y) := by
  have hmp : MeasurePreserving (rmulM y : Mt k r → Mt k r) μG μG :=
    ⟨(continuous_rmulM y).measurable, hU.1 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

/- English proof (translation)
Establish `hc : Continuous (lmulM y : Mt k r → Mt k r)` using `(continuous_const (y := y)).matrix_mul (continuous_id (X := Mat k r))`. Establish `hmp : MeasurePreserving (lmulM y : Mt k r → Mt k r) μG μG` using `⟨hc.measurable, hH.2.2.2 y hy⟩`. Conclude with `hmp.quasiMeasurePreserving.ae_eq_comp h`.
-/
theorem ae_ltrans {B : Type*} {μG : Measure (Mt k r)} (hH : IsHaarOn (GG k r) μG) {y : Mat k r}
    (hy : y ∈ GG k r) {f g : Mat k r → B}
    (h : (fun x : Mt k r => f (Matrix.of x)) =ᵐ[μG] fun x => g (Matrix.of x)) :
    (fun x : Mt k r => f (y * Matrix.of x)) =ᵐ[μG] fun x => g (y * Matrix.of x) := by
  have hc : Continuous (lmulM y : Mt k r → Mt k r) :=
    (continuous_const (y := y)).matrix_mul (continuous_id (X := Mat k r))
  have hmp : MeasurePreserving (lmulM y : Mt k r → Mt k r) μG μG :=
    ⟨hc.measurable, hH.2.2.2 y hy⟩
  exact hmp.quasiMeasurePreserving.ae_eq_comp h

end GlobalTheory.SgInf.BesselExt

open GlobalTheory.SgInf.BesselExt in
/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hw v hv ξ`. Take `⟨T, hTD, hadd, hsmul, hloc, hR, hL⟩` from `GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant k r σ w a μG d z c π μS hStd hSide v hv ξ`. Establish `hrep : IsURepOn (GG k r) σ` using `hStd.2.1`. Establish `hHaar : IsHaarOn (GG k r) μG` using `hStd.2.2.2.2.1`. Establish `hUni : IsUnimod (GG k r) μG` using `GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar`.

Establish `hDDi` using `GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hrep`. Establish `hPi` using `GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1`. Take `⟨C, Ws, hWs, hreg⟩` from `GlobalTheory.T.boundedEquivariantMap_smooth_continuous_seminorm_bound k r σ μG T hrep hHaar hadd hsmul hloc hR`. Set `F : H → Mat k r → Wp` to `fun u => if h : IsSmoothVec σ u then (hreg u h).choose else 0`. Establish `hF : ∀ u, IsSmoothVec σ u → ContinuousOn (F u) (GG k r) ∧ (fun x : Mt k r => F u (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧ ‖F u 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum`.

Introduce `u hu`. Use `(hreg u hu).choose_spec` as an intermediate fact. Simplify using `only [F, dif_pos hu]`. Conclude with `this`. Establish `hDDsm : ∀ u ∈ DD σ w, IsSmoothVec σ u` using `fun u hu => (hDDi.2.2.2.2 hw).1 u (hDDi.2.2.1 hu)`.

Use `⟨fun u => F u 1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `u hu u' hu'`. Establish `hs` using `smooth_add hu hu'`. Use `GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (u + u')) (fun x => F u x + F u' x) hHaar (hF _ hs).1 ((hF u hu).1.add (hF u' hu').1) ?_ 1 one_memG` and prove the remaining obligations. Use `filter_upwards [(hF _ hs).2.1, hadd u u', (hF u hu).2.1, (hF u' hu').2.1] with x h1 h2 h3 h4`.

Rewrite using `[h1, h2, h3, h4]`. Introduce `b u hu`. Establish `hs` using `smooth_smul b hu`. Use `GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (b • u)) (fun x => b • F u x) hHaar (hF _ hs).1 ((hF u hu).1.const_smul b) ?_ 1 one_memG` and prove the remaining obligations. Use `filter_upwards [(hF _ hs).2.1, hsmul b u, (hF u hu).2.1] with x h1 h2 h3`.

Rewrite using `[h1, h2, h3]`. Introduce `h hh m hm u hu`. Establish `hhG : h ∈ GG k r` using `hh.1`. Establish `hmG : m ∈ GG k r` using `hm.1`. Establish `htG : h * m ∈ GG k r` using `mul_memG hhG hmG`.

Establish `htS : h * m ∈ Sset k r z` using `⟨h, hh, m, hm, rfl⟩`. Establish `hsu : IsSmoothVec σ (σ (h * m) u)` using `((hDDi.2.2.2.1 u hu).1 _ htG)`. Establish `h1 : ∀ x ∈ GG k r, F (σ (h * m) u) x = F u (x * (h * m))`. Use `GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG _ _ hHaar (hF _ hsu).1 ?_ ?_` and prove the remaining obligations. Conclude with `(hF u hu).1.comp ((continuous_id.mul continuous_const).continuousOn) (fun x hx => mul_memG hx htG)`.

Use `filter_upwards [(hF _ hsu).2.1, hR _ htG u, ae_rtrans hUni htG (hF u hu).2.1] with x h1 h2 h3`. Rewrite using `[h1, h2, h3]`. Establish `h2 : ∀ x ∈ GG k r, F u ((h * m) * x) = PiS (psiGen k r z c) π (h * m) (F u x)`. Use `GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (fun x => F u ((h * m) * x)) (fun x => PiS (psiGen k r z c) π (h * m) (F u x)) hHaar ?_ ?_ ?_` and prove the remaining obligations. Conclude with `(hF u hu).1.comp ((continuous_const.mul continuous_id).continuousOn) (fun x hx => mul_memG htG hx)`.

Conclude with `(PiS (psiGen k r z c) π (h * m)).continuous.comp_continuousOn (hF u hu).1`. Use `filter_upwards [ae_ltrans hHaar htG (hF u hu).2.1, hL _ htS u, (hF u hu).2.1] with x h1 h2 h3`. Rewrite using `[h1, h2, h3]`. Use `show F (σ (h * m) u) 1 = psiGen k r z c m • π h (F u 1)`. Rewrite using `[h1 1 one_memG, Matrix.one_mul, ← Matrix.mul_one (h * m), h2 1 one_memG, (hPi.1 h hh m hm).2]`.

Both sides reduce to the same expression. Use `⟨C, Ws, hWs, fun u hu => (hF u hu).2.2⟩` and prove the remaining obligations. Introduce `u hu`. Establish `hsu` using `hDDsm u hu`. Establish `hcont : ContinuousOn (Afun (psiGen k r z c) π μS σ u v ξ) (GG k r)`.

Establish `hD1` using `GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hDDi.1 hStd.2.2.2.2.2.2.2.1 u hu v hv`. Conclude with `(ContinuousLinearMap.apply ℂ Wp ξ).continuous.comp_continuousOn hD1.2.2.2`. Use `GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F u) _ hHaar (hF u hsu).1 hcont (by rw [← hTD u hu]; exact (hF u hsu).2.1) 1 one_memG` as an intermediate fact. Use `show F u 1 = _`. Rewrite using `[this]`.

Simplify using `only [Afun, hrep.1.1, ContinuousLinearMap.one_apply]`.
-/
theorem GlobalTheory.SgInf.exists_besselExt : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → IsSmoothVec σ w → ∀ v ∈ DD σ w, ∀ ξ : Wp, ∃ l : H → Wp, IsBesselMapSm z (psiGen k r z c) σ π l ∧ ∀ u ∈ DD σ w, l u = be (psiGen k r z c) π μS σ u v ξ := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide hw v hv ξ
  obtain ⟨T, hTD, hadd, hsmul, hloc, hR, hL⟩ := GlobalTheory.T.besselMatrixCoeff_extends_bounded_equivariant k r σ w a μG d z c π μS hStd hSide v hv ξ
  have hrep : IsURepOn (GG k r) σ := hStd.2.1
  have hHaar : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hUni : IsUnimod (GG k r) μG := GlobalTheory.T.isUnimodular_besselModelUnitaryGroup k r μG hHaar
  have hDDi := GlobalTheory.T.smooth_vectors_dense_invariant k r σ w hrep
  have hPi := GlobalTheory.T.besselSubgroupRepTwisted_isUnitaryRep k r z c π hSide.1 hSide.2.1 hSide.2.2.1
  obtain ⟨C, Ws, hWs, hreg⟩ := GlobalTheory.T.boundedEquivariantMap_smooth_continuous_seminorm_bound k r σ μG T hrep hHaar hadd hsmul hloc hR
  classical
  let F : H → Mat k r → Wp := fun u => if h : IsSmoothVec σ u then (hreg u h).choose else 0
  have hF : ∀ u, IsSmoothVec σ u → ContinuousOn (F u) (GG k r) ∧
      (fun x : Mt k r => F u (Matrix.of x)) =ᵐ[μG] (fun x => T u (Matrix.of x)) ∧
      ‖F u 1‖ ≤ C * (Ws.map fun ws => ‖dsigW σ ws u‖).sum := by
    intro u hu
    have := (hreg u hu).choose_spec
    simp only [F, dif_pos hu]
    exact this
  have hDDsm : ∀ u ∈ DD σ w, IsSmoothVec σ u := fun u hu => (hDDi.2.2.2.2 hw).1 u (hDDi.2.2.1 hu)
  refine ⟨fun u => F u 1, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro u hu u' hu'
    have hs := smooth_add hu hu'
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (u + u')) (fun x => F u x + F u' x) hHaar (hF _ hs).1
      ((hF u hu).1.add (hF u' hu').1) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hadd u u', (hF u hu).2.1, (hF u' hu').2.1] with x h1 h2 h3 h4
    rw [h1, h2, h3, h4]
  · intro b u hu
    have hs := smooth_smul b hu
    refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F (b • u)) (fun x => b • F u x) hHaar (hF _ hs).1
      ((hF u hu).1.const_smul b) ?_ 1 one_memG
    filter_upwards [(hF _ hs).2.1, hsmul b u, (hF u hu).2.1] with x h1 h2 h3
    rw [h1, h2, h3]
  · intro h hh m hm u hu
    have hhG : h ∈ GG k r := hh.1
    have hmG : m ∈ GG k r := hm.1
    have htG : h * m ∈ GG k r := mul_memG hhG hmG
    have htS : h * m ∈ Sset k r z := ⟨h, hh, m, hm, rfl⟩
    have hsu : IsSmoothVec σ (σ (h * m) u) := ((hDDi.2.2.2.1 u hu).1 _ htG)

    have h1 : ∀ x ∈ GG k r, F (σ (h * m) u) x = F u (x * (h * m)) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG _ _ hHaar (hF _ hsu).1 ?_ ?_
      · exact (hF u hu).1.comp ((continuous_id.mul continuous_const).continuousOn)
          (fun x hx => mul_memG hx htG)
      · filter_upwards [(hF _ hsu).2.1, hR _ htG u, ae_rtrans hUni htG (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]

    have h2 : ∀ x ∈ GG k r, F u ((h * m) * x) = PiS (psiGen k r z c) π (h * m) (F u x) := by
      refine GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (fun x => F u ((h * m) * x)) (fun x => PiS (psiGen k r z c) π (h * m) (F u x))
        hHaar ?_ ?_ ?_
      · exact (hF u hu).1.comp ((continuous_const.mul continuous_id).continuousOn)
          (fun x hx => mul_memG htG hx)
      · exact (PiS (psiGen k r z c) π (h * m)).continuous.comp_continuousOn (hF u hu).1
      · filter_upwards [ae_ltrans hHaar htG (hF u hu).2.1, hL _ htS u, (hF u hu).2.1] with x h1 h2 h3
        rw [h1, h2, h3]
    show F (σ (h * m) u) 1 = psiGen k r z c m • π h (F u 1)
    rw [h1 1 one_memG, Matrix.one_mul, ← Matrix.mul_one (h * m), h2 1 one_memG, (hPi.1 h hh m hm).2]
    rfl
  · refine ⟨C, Ws, hWs, fun u hu => (hF u hu).2.2⟩
  · intro u hu
    have hsu := hDDsm u hu
    have hcont : ContinuousOn (Afun (psiGen k r z c) π μS σ u v ξ) (GG k r) := by
      have hD1 := GlobalTheory.T.besselForm_converges_equivariant_hermitian k r σ w a μG d z c π μS hStd hSide (DD σ w) hDDi.1 hStd.2.2.2.2.2.2.2.1 u hu v hv
      exact (ContinuousLinearMap.apply ℂ Wp ξ).continuous.comp_continuousOn hD1.2.2.2
    have := GlobalTheory.T.besselModel_eqOn_of_continuousOn_ae_eq k r μG (F u) _ hHaar (hF u hsu).1 hcont
      (by rw [← hTD u hu]; exact (hF u hsu).2.1) 1 one_memG
    show F u 1 = _
    rw [this]
    simp only [Afun, hrep.1.1, ContinuousLinearMap.one_apply]
