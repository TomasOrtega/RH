import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmoothWhittakerBumpAdelicGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadNatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RsTermZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ZintZero
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.Definitions.Divisors.UnrOutside
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurDir
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Injective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBumpShintani
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWhittakerBumpExtensionSchurComplementStatement
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW Formalism.UG GlobalTheory.LFun Formalism.L2.Host
open scoped ENNReal ComplexConjugate ContDiff
open Matrix
open GlobalTheory.WhitBump

noncomputable section

namespace GlobalTheory.KappaCut

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

/- English proof (translation)
Apply the tactic sequence `refine ga_ext ?_ ?_ <;> simp`.
-/
theorem decomp (h : GA E a) :
    h = infGL E a (GeneralLinearGroup.map (pInf E) h) * finGL E a (GeneralLinearGroup.map (pFin E) h) := by
  refine ga_ext ?_ ?_ <;> simp

/- English proof (translation)
Rewrite using `[continuous_iff_continuousAt]`. Introduce `g`. Set `pI : GA E a → GL (Fin a) (Cinf E)` to `fun h => GeneralLinearGroup.map (pInf E) h`. Set `pF : GA E a → GL (Fin a) (Af E)` to `fun h => GeneralLinearGroup.map (pFin E) h`. Establish `hpI : Continuous pI` using `ContAut.continuous_map_pInf E a`.

Establish `hpF : Continuous pF` using `ContAut.continuous_map_pFin E a`. Set `F : GA E a → Lie E a` to `fun g' => toL ((pI (g⁻¹ * g') : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))`. Establish `hF : Continuous F` using `(Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (hpI.comp (continuous_const.mul continuous_id))`. Establish `hFmem : ∀ g', F g' ∈ invSet E a` using `fun g' => show IsUnit (Matrix.of (F g')) from (pI (g⁻¹ * g')).isUnit`. Establish `heq : ∀ g', pF (g⁻¹ * g') ∈ U → b g' = chart b g (F g')`.

Introduce `g' hg'`. Establish `hx : IsUnit (Matrix.of (F g'))` using `(pI (g⁻¹ * g')).isUnit`. Rewrite using `[chart, dif_pos hx]`. Establish `hu : hx.unit = pI (g⁻¹ * g')` using `Units.ext rfl`. Rewrite using `[hu]`.

Establish `e : g' = g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g'))`. Rewrite using `[mul_assoc, ← decomp, mul_inv_cancel_left]`. Rewrite using `[show b g' = b (g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g'))) from congrArg b e, hR _ hg']`. Establish `hopen : {g' | pF (g⁻¹ * g') ∈ U} ∈ nhds g`. Use `(hU.preimage (hpF.comp (continuous_const.mul continuous_id))).mem_nhds ?_` and prove the remaining obligations.

Simplify using `[pF, U.one_mem]`. Establish `hcont : ContinuousAt (fun g' => chart b g (F g')) g`. Establish `h1 : ContinuousWithinAt (chart b g) (invSet E a) (F g)` using `(hC g).continuousOn _ (hFmem g)`. Establish `h2 : ContinuousWithinAt (chart b g ∘ F) Set.univ g` using `h1.comp hF.continuousAt.continuousWithinAt (fun x _ => hFmem x)`. Rewrite `h2` using `[continuousWithinAt_univ]`. Then use the resulting hypothesis.

Conclude with `hcont.congr (Filter.eventuallyEq_of_mem hopen (fun g' hg' => (heq g' hg').symm))`.
-/
theorem continuous_of_chart (b : GA E a → ℂ) (U : Subgroup (GL (Fin a) (Af E))) (hU : IsOpen (U : Set (GL (Fin a) (Af E))))
    (hR : ∀ u ∈ U, ∀ g, b (g * finGL E a u) = b g) (hC : ∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E a)) :
    Continuous b := by
  rw [continuous_iff_continuousAt]
  intro g
  let pI : GA E a → GL (Fin a) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E a → GL (Fin a) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hpI : Continuous pI := ContAut.continuous_map_pInf E a
  have hpF : Continuous pF := ContAut.continuous_map_pFin E a
  let F : GA E a → Lie E a := fun g' => toL ((pI (g⁻¹ * g') : GL (Fin a) (Cinf E)) : Matrix (Fin a) (Fin a) (Cinf E))
  have hF : Continuous F := (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Cinf E))).comp (hpI.comp (continuous_const.mul continuous_id))
  have hFmem : ∀ g', F g' ∈ invSet E a := fun g' => show IsUnit (Matrix.of (F g')) from (pI (g⁻¹ * g')).isUnit
  have heq : ∀ g', pF (g⁻¹ * g') ∈ U → b g' = chart b g (F g') := by
    intro g' hg'
    have hx : IsUnit (Matrix.of (F g')) := (pI (g⁻¹ * g')).isUnit
    rw [chart, dif_pos hx]
    have hu : hx.unit = pI (g⁻¹ * g') := Units.ext rfl
    rw [hu]
    have e : g' = g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g')) := by
      rw [mul_assoc, ← decomp, mul_inv_cancel_left]
    rw [show b g' = b (g * infGL E a (pI (g⁻¹ * g')) * finGL E a (pF (g⁻¹ * g'))) from congrArg b e, hR _ hg']
  have hopen : {g' | pF (g⁻¹ * g') ∈ U} ∈ nhds g := by
    refine (hU.preimage (hpF.comp (continuous_const.mul continuous_id))).mem_nhds ?_
    simp [pF, U.one_mem]
  have hcont : ContinuousAt (fun g' => chart b g (F g')) g := by
    have h1 : ContinuousWithinAt (chart b g) (invSet E a) (F g) := (hC g).continuousOn _ (hFmem g)
    have h2 : ContinuousWithinAt (chart b g ∘ F) Set.univ g :=
      h1.comp hF.continuousAt.continuousWithinAt (fun x _ => hFmem x)
    rwa [continuousWithinAt_univ] at h2
  exact hcont.congr (Filter.eventuallyEq_of_mem hopen (fun g' hg' => (heq g' hg').symm))

/- English proof (translation)
Establish `h : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2)` using `contDiff_norm_sq ℝ`. Establish `e : (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) = fun z => Complex.ofRealCLM (‖z‖ ^ 2)`. Use function extensionality and compare the values at `z`. Simplify using `[Complex.normSq_eq_norm_sq]`. Rewrite using `[e]`.

Conclude with `Complex.ofRealCLM.contDiff.comp h`.
-/
theorem contDiff_normSq_ofReal : ContDiff ℝ ∞ (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) := by
  have h : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := contDiff_norm_sq ℝ
  have e : (fun z : ℂ => ((Complex.normSq z : ℝ) : ℂ)) = fun z => Complex.ofRealCLM (‖z‖ ^ 2) := by
    funext z; simp [Complex.normSq_eq_norm_sq]
  rw [e]
  exact Complex.ofRealCLM.contDiff.comp h

end GlobalTheory.KappaCut

open GlobalTheory.KappaCut in

/- English proof (translation)
Introduce `E _ _ _ m x₀`. Take `⟨b, hb1, hbN, ⟨C, hC, hCs⟩, ⟨U, hU, hUr⟩, hbc⟩` from `GlobalTheory.WhitBump.exists_bump_glob E m`. Establish `hbcont : Continuous b` using `continuous_of_chart b U hU hUr hbc`. Set `pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E)` to `fun h => GeneralLinearGroup.map (pInf E) h`. Set `pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E)` to `fun h => GeneralLinearGroup.map (pFin E) h`.

Establish `hconjF : ∀ k, x₀ * finGL E (m + 1) k * x₀⁻¹ = finGL E (m + 1) (pF x₀ * k * (pF x₀)⁻¹)`. Apply the tactic sequence `intro k; refine ga_ext ?_ ?_ <;> simp [pF]`. Establish `hconjI : ∀ y, x₀ * infGL E (m + 1) y * x₀⁻¹ = infGL E (m + 1) (pI x₀ * y * (pI x₀)⁻¹)`. Apply the tactic sequence `intro y; refine ga_ext ?_ ?_ <;> simp [pI]`. Use `⟨fun h => Complex.normSq (b (h * x₀⁻¹)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Complex.continuous_normSq.comp (hbcont.comp (continuous_id.mul continuous_const))`. Introduce `h`. Conclude with `Complex.normSq_nonneg _`. Introduce `u hu h show Complex.normSq (b (u * h * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))`. Rewrite using `[mul_assoc, hbN u hu, map_mul, GlobalTheory.JSW.psiN, Circle.normSq_coe, one_mul]`.

Use `⟨(fun c => c * x₀) '' C, hC.image (continuous_id.mul continuous_const), fun h hh => ?_⟩` and prove the remaining obligations. Establish `hb : b (h * x₀⁻¹) ≠ 0` using `fun e => hh (by simp [e])`. Take `⟨u, hu, huC⟩` from `hCs _ hb`. Conclude with `⟨u, hu, ⟨_, huC, by group⟩⟩`. Use `⟨U.comap (MulAut.conj (pF x₀)).toMonoidHom, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Subgroup.coe_comap]`. Conclude with `hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)`. Introduce `u hu h`. Establish `hu' : pF x₀ * u * (pF x₀)⁻¹ ∈ U` using `hu`. Use `show Complex.normSq (b (h * finGL E (m + 1) u * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))`.

Establish `e : h * finGL E (m + 1) u * x₀⁻¹ = h * x₀⁻¹ * finGL E (m + 1) (pF x₀ * u * (pF x₀)⁻¹)`. Rewrite using `[← hconjF]`. Use `group`. Rewrite using `[e, hUr _ hu']`. Introduce `g set A : GL (Fin (m + 1)) (Cinf E) := pI x₀ with hA`.

Set `L0 : Lie E (m + 1) →ₗ[ℝ] Lie E (m + 1)` to `{ toFun := fun x => toL ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x * ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))) map_add' := fun x y => by show toL (_ * (Matrix.of x + Matrix.of y) * _) = _`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c x => by show toL (_ * (c • Matrix.of x) * _) = _`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.

Use `rfl }`. Set `L : Lie E (m + 1) →L[ℝ] Lie E (m + 1)` to `LinearMap.toContinuousLinearMap L0`. Establish `hLx : ∀ x : Lie E (m + 1), Matrix.of (L x) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x * ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E))`. Introduce `x`. Simplify using `only [L]`.

Use `erw [LinearMap.coe_toContinuousLinearMap']`. Both sides reduce to the same expression. Establish `hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1))` using `fun x hx => by`. Establish `hx' : IsUnit (Matrix.of x)` using `hx`. Use `show IsUnit (Matrix.of (L x))`.

Rewrite using `[hLx]`. Conclude with `(A.isUnit.mul hx').mul (A⁻¹).isUnit`. Establish `h2 : ContDiffOn ℝ ∞ (fun x => chart b (g * x₀⁻¹) (L x)) (invSet E (m + 1))` using `(hbc (g * x₀⁻¹)).comp L.contDiff.contDiffOn hmaps`. Establish `h3` using `contDiff_normSq_ofReal.comp_contDiffOn h2`. Use `h3.congr fun x hx => ?_` and prove the remaining obligations.

Establish `hx' : IsUnit (Matrix.of x)` using `hx`. Establish `hL' : IsUnit (Matrix.of (L x))` using `hmaps hx`. Simplify using `only [Function.comp, chart, dif_pos hx', dif_pos hL']`. Use `congr 3`. Establish `hu : hL'.unit = A * hx'.unit * A⁻¹` using `Units.ext (by rw [IsUnit.unit_spec, hLx]; simp)`.

Rewrite using `[hu, ← hconjI]`. Use `group`. Simplify using `[hb1]`.
-/
theorem GlobalTheory.KappaCut.exists_kappa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (x₀ : GA E (m + 1)),
    ∃ κ : GA E (m + 1) → ℝ, Continuous κ ∧ (∀ h, 0 ≤ κ h) ∧ (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ h, κ (u * h) = κ h) ∧
      (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ h, κ h ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (m + 1), u⁻¹ * h ∈ C) ∧
      (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧
        ∀ u ∈ U, ∀ h, κ (h * finGL E (m + 1) u) = κ h) ∧
      (∀ g, ContDiffOn ℝ ∞ (chart (fun h => (κ h : ℂ)) g) (invSet E (m + 1))) ∧ 0 < κ x₀ := by
  intro E _ _ _ m x₀
  obtain ⟨b, hb1, hbN, ⟨C, hC, hCs⟩, ⟨U, hU, hUr⟩, hbc⟩ := GlobalTheory.WhitBump.exists_bump_glob E m
  have hbcont : Continuous b := continuous_of_chart b U hU hUr hbc
  let pI : GA E (m + 1) → GL (Fin (m + 1)) (Cinf E) := fun h => GeneralLinearGroup.map (pInf E) h
  let pF : GA E (m + 1) → GL (Fin (m + 1)) (Af E) := fun h => GeneralLinearGroup.map (pFin E) h
  have hconjF : ∀ k, x₀ * finGL E (m + 1) k * x₀⁻¹ = finGL E (m + 1) (pF x₀ * k * (pF x₀)⁻¹) := by
    intro k; refine ga_ext ?_ ?_ <;> simp [pF]
  have hconjI : ∀ y, x₀ * infGL E (m + 1) y * x₀⁻¹ = infGL E (m + 1) (pI x₀ * y * (pI x₀)⁻¹) := by
    intro y; refine ga_ext ?_ ?_ <;> simp [pI]
  refine ⟨fun h => Complex.normSq (b (h * x₀⁻¹)), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Complex.continuous_normSq.comp (hbcont.comp (continuous_id.mul continuous_const))
  · intro h; exact Complex.normSq_nonneg _
  · intro u hu h
    show Complex.normSq (b (u * h * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
    rw [mul_assoc, hbN u hu, map_mul, GlobalTheory.JSW.psiN, Circle.normSq_coe, one_mul]
  · refine ⟨(fun c => c * x₀) '' C, hC.image (continuous_id.mul continuous_const), fun h hh => ?_⟩
    have hb : b (h * x₀⁻¹) ≠ 0 := fun e => hh (by simp [e])
    obtain ⟨u, hu, huC⟩ := hCs _ hb
    exact ⟨u, hu, ⟨_, huC, by group⟩⟩
  · refine ⟨U.comap (MulAut.conj (pF x₀)).toMonoidHom, ?_, ?_⟩
    · rw [Subgroup.coe_comap]
      exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)
    · intro u hu h
      have hu' : pF x₀ * u * (pF x₀)⁻¹ ∈ U := hu
      show Complex.normSq (b (h * finGL E (m + 1) u * x₀⁻¹)) = Complex.normSq (b (h * x₀⁻¹))
      have e : h * finGL E (m + 1) u * x₀⁻¹ = h * x₀⁻¹ * finGL E (m + 1) (pF x₀ * u * (pF x₀)⁻¹) := by
        rw [← hconjF]; group
      rw [e, hUr _ hu']
  · intro g
    set A : GL (Fin (m + 1)) (Cinf E) := pI x₀ with hA
    let L0 : Lie E (m + 1) →ₗ[ℝ] Lie E (m + 1) :=
      { toFun := fun x => toL ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
          ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)))
        map_add' := fun x y => by
          show toL (_ * (Matrix.of x + Matrix.of y) * _) = _
          rw [Matrix.mul_add, Matrix.add_mul]; rfl
        map_smul' := fun c x => by
          show toL (_ * (c • Matrix.of x) * _) = _
          rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
    let L : Lie E (m + 1) →L[ℝ] Lie E (m + 1) := LinearMap.toContinuousLinearMap L0
    have hLx : ∀ x : Lie E (m + 1), Matrix.of (L x) = (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) * Matrix.of x *
        ((A⁻¹ : GL (Fin (m + 1)) (Cinf E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) := by
      intro x
      simp only [L]
      erw [LinearMap.coe_toContinuousLinearMap']
      rfl
    have hmaps : Set.MapsTo L (invSet E (m + 1)) (invSet E (m + 1)) := fun x hx => by
      have hx' : IsUnit (Matrix.of x) := hx
      show IsUnit (Matrix.of (L x))
      rw [hLx]
      exact (A.isUnit.mul hx').mul (A⁻¹).isUnit
    have h2 : ContDiffOn ℝ ∞ (fun x => chart b (g * x₀⁻¹) (L x)) (invSet E (m + 1)) :=
      (hbc (g * x₀⁻¹)).comp L.contDiff.contDiffOn hmaps
    have h3 := contDiff_normSq_ofReal.comp_contDiffOn h2
    refine h3.congr fun x hx => ?_
    have hx' : IsUnit (Matrix.of x) := hx
    have hL' : IsUnit (Matrix.of (L x)) := hmaps hx
    simp only [Function.comp, chart, dif_pos hx', dif_pos hL']
    congr 3
    have hu : hL'.unit = A * hx'.unit * A⁻¹ := Units.ext (by rw [IsUnit.unit_spec, hLx]; simp)
    rw [hu, ← hconjI]; group
  · simp [hb1]

end
