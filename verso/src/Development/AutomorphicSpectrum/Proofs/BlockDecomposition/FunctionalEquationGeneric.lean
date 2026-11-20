import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerRightTranslation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerNonvanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishingAtZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerPureTensorFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLinearity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerLocalTateIntegral

noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.SchwartzSpaceL2
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.WhitFE

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def FEat (ψ : AddChar F Circle) (μ₁ μ₂ c : Fˣ →* ℂˣ) (s : ℂ) (W : GL (Fin 2) F → ℂ) : Prop :=
  Integrable (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
    mp a (1 / 2 - s)) (multHaar F) ∧
  Integrable (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) (multHaar F) ∧
  ∫ a, W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s) ∂multHaar F =
    gam ψ (μ₁ * c) s * gam ψ (μ₂ * c) s *
      ∫ a, W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2) ∂multHaar F

/- English proof (translation)
Simplify using `[FEat, integrable_zero]`.
-/
theorem FEat.zero (ψ : AddChar F Circle) (μ₁ μ₂ c : Fˣ →* ℂˣ) (s : ℂ) :
    FEat ψ μ₁ μ₂ c s (0 : GL (Fin 2) F → ℂ) := by
  simp [FEat, integrable_zero]

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Take `⟨h1', h2', h3'⟩` from `h'`. Establish `e1 : (fun a : Fˣ => (W + W') (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) = (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) + (fun a : Fˣ => W' (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - …`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (fun a : Fˣ => (W + W') (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) = (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) + (fun a : Fˣ => W' (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2))`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.add_apply]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Conclude with `h1.add h1'`. Rewrite using `[e2]`. Conclude with `h2.add h2'`.

Rewrite using `[e1, e2, integral_add' h1 h1', integral_add' h2 h2', h3, h3']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem FEat.add {ψ : AddChar F Circle} {μ₁ μ₂ c : Fˣ →* ℂˣ} {s : ℂ} {W W' : GL (Fin 2) F → ℂ}
    (h : FEat ψ μ₁ μ₂ c s W) (h' : FEat ψ μ₁ μ₂ c s W') : FEat ψ μ₁ μ₂ c s (W + W') := by
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := h'
  have e1 : (fun a : Fˣ => (W + W') (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
      mp a (1 / 2 - s)) = (fun a : Fˣ => W (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
      mp a (1 / 2 - s)) + (fun a : Fˣ => W' (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) *
      mp a (1 / 2 - s)) := by
    funext a
    simp only [Pi.add_apply]
    ring
  have e2 : (fun a : Fˣ => (W + W') (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
      (fun a : Fˣ => W (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) +
      (fun a : Fˣ => W' (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) := by
    funext a
    simp only [Pi.add_apply]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact h1.add h1'
  · rw [e2]; exact h2.add h2'
  · rw [e1, e2, integral_add' h1 h1', integral_add' h2 h2', h3, h3']
    ring

/- English proof (translation)
Use `⟨hα.1.mul hβ.1, fun x => ?_⟩` and prove the remaining obligations. Simplify using `[hα.2 x, hβ.2 x]`.
-/
theorem isUnit1_mul {α β : Fˣ →* ℂˣ} (hα : IsUnit1 α) (hβ : IsUnit1 β) : IsUnit1 (α * β) := by
  refine ⟨hα.1.mul hβ.1, fun x => ?_⟩
  simp [hα.2 x, hβ.2 x]

/- English proof (translation)
Use `⟨continuous_quasiChar_inv hα.1, fun x => ?_⟩` and prove the remaining obligations. Simplify using `[hα.2 x]`.
-/
theorem isUnit1_inv {α : Fˣ →* ℂˣ} (hα : IsUnit1 α) : IsUnit1 α⁻¹ := by
  refine ⟨continuous_quasiChar_inv hα.1, fun x => ?_⟩
  simp [hα.2 x]

/- English proof (translation)
Establish `hm : ((modulus (a : F) : ℝ) : ℂ) ≠ 0`. Use `modulus_ne_zero a.ne_zero` as an intermediate fact. Conclude with `this` after adjusting the coercions. Conclude with `Complex.cpow_add _ _ hm`.
-/
theorem mp_add (a : Fˣ) (s t : ℂ) : mp a (s + t) = mp a s * mp a t := by
  have hm : ((modulus (a : F) : ℝ) : ℂ) ≠ 0 := by
    have := modulus_ne_zero a.ne_zero
    exact_mod_cast this
  exact Complex.cpow_add _ _ hm

/- English proof (translation)
Assemble the required witnesses or components as `⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg F)⟩`.
-/
theorem comp_neg_mem {f : F → ℂ} (hf : f ∈ schwartzBruhat F) :
    (fun x => f (-x)) ∈ schwartzBruhat F :=
  ⟨hf.1.comp_continuous continuous_neg, hf.2.comp_homeomorph (Homeomorph.neg F)⟩

/- English proof (translation)
Unfold `localFourier`. Use `integral_neg_eq_self (fun x => f x * (ψ (x * (-y)) : ℂ)) (selfDualMeasure ψ)` as an intermediate fact. Rewrite using `[← this]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem localFourier_comp_neg (ψ : AddChar F Circle) (f : F → ℂ) (y : F) :
    localFourier (selfDualMeasure ψ) ψ (fun x => f (-x)) y =
      localFourier (selfDualMeasure ψ) ψ f (-y) := by
  unfold localFourier
  have := integral_neg_eq_self (fun x => f x * (ψ (x * (-y)) : ℂ)) (selfDualMeasure ψ)
  rw [← this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[rt, pt, w0, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]`.
-/
theorem rightTranslate_pureTensor_weyl (f g : F → ℂ) : rt (pt f g) (w0 : GL (Fin 2) F) = pt g (fun x => f (-x)) := by
  funext x
  simp [rt, pt, w0, Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]

/- English proof (translation)
Use `ext`. Simplify using `[w0, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]`.
-/
theorem det_weyl_GL2 : GeneralLinearGroup.det (w0 : GL (Fin 2) F) = 1 := by
  ext
  simp [w0, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]

/- English proof (translation)
Simplify using `[mp]`.
-/
theorem mp_one_left (s : ℂ) : mp (1 : Fˣ) s = 1 := by
  simp [mp]

/- English proof (translation)
Use `set T := localFourier (selfDualMeasure ψ) ψ with hT`. Establish `hTf : T f ∈ schwartzBruhat F` using `localFourier_mem_schwartzBruhat _ hψ.1 hψ.2.1 hf`. Establish `hTg : T g ∈ schwartzBruhat F` using `localFourier_mem_schwartzBruhat _ hψ.1 hψ.2.1 hg`. Establish `hβ : IsUnit1 (μ₁⁻¹ * μ₂)` using `isUnit1_mul (isUnit1_inv h₁) h₂`. Establish `h1c : IsUnit1 (μ₁ * c)` using `isUnit1_mul h₁ hc`.

Establish `h2c : IsUnit1 (μ₂ * c)` using `isUnit1_mul h₂ hc`. Establish `s0' : 0 < (1 - s).re` using `by simpa using s1`. Take `⟨pI, pE⟩` from `GlobalTheory.CompanionTheory.DoubleTate.sdz F f hf (fun x => T g (-x)) (comp_neg_mem hTg) (μ₂ * c) (μ₁⁻¹ * μ₂) h2c hβ s s0`. Take `⟨dI, dE⟩` from `GlobalTheory.CompanionTheory.DoubleTate.sdz F g hg (T f) hTf (μ₁ * c)⁻¹ (μ₁⁻¹ * μ₂) (isUnit1_inv h1c) hβ (1 - s) s0'`. Establish `ch1 : (μ₂ * c) * (μ₁⁻¹ * μ₂)⁻¹ = μ₁ * c`.

Use extensionality with `a`. Establish `n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0` using `(μ₂ a).ne_zero`. Establish `n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0` using `(μ₁ a).ne_zero`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]`. Clear the denominators using the available nonvanishing facts.

Establish `ch2 : (μ₁ * c)⁻¹ * (μ₁⁻¹ * μ₂)⁻¹ = (μ₂ * c)⁻¹`. Use extensionality with `a`. Establish `n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0` using `(μ₂ a).ne_zero`. Establish `n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0` using `(μ₁ a).ne_zero`. Establish `n3 : ((c a : ℂˣ) : ℂ) ≠ 0` using `(c a).ne_zero`.

Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, mul_inv, inv_inv]`. Clear the denominators using the available nonvanishing facts. Rewrite `pE` using `[ch1, localZeta_comp_neg]`. Rewrite `dE` using `[ch2]`. Establish `ePrimal : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) = fun a : Fˣ => (((μ₂ * c) a : ℂˣ) : ℂ) * mp a s * ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * f ((h : F) * a) * T g (-((h⁻¹ : Fˣ) : F)) ∂multHaar F`.

Use function extensionality and compare the values at `a`. Rewrite using `[GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ μ₁ μ₂ h₁ h₂ f hf g hg a]`. Establish `: mp a s = mp a (1 / 2) * mp a (s - 1 / 2)`. Rewrite using `[← mp_add]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `eDual : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) * (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) = fun a : Fˣ => (((μ₁ * c)⁻¹ a : ℂˣ) : ℂ) * mp a (1 - s) * ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * g ((h : F) * a) * T f ((h⁻¹ : Fˣ) : F) ∂multHaar F` using `by clear pI pE dI dE ch1 ch2 ePrimal`.

Use function extensionality and compare the values at `a`. Establish `hS` using `(GlobalTheory.CompanionTheory.WhittakerTrans.sTrans F ψ hψ μ₁ μ₂ h₁ h₂ (pt f g) (GlobalTheory.CompanionTheory.WhNe.pt_mem_plane hf hg) w0).2 (dg2 a 1)`. Rewrite using `[hS, det_weyl_GL2, rightTranslate_pureTensor_weyl, GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ μ₁ μ₂ h₁ h₂ g hg _ (comp_neg_mem hf) a]`. Establish `hin : ∀ h : Fˣ, localFourier (selfDualMeasure ψ) ψ (fun x => f (-x)) (-((h⁻¹ : Fˣ) : F)) = T f ((h⁻¹ : Fˣ) : F)` using `fun h => by`. Rewrite using `[localFourier_comp_neg, neg_neg]`.

Simplify using `only [hin]`. Establish `: mp a (1 - s) = mp a (1 / 2) * mp a (1 / 2 - s)`. Rewrite using `[← mp_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, mp_one_left]`. Establish `n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0` using `(μ₁ a).ne_zero`. Establish `n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0` using `(μ₂ a).ne_zero`. Establish `n3 : ((c a : ℂˣ) : ℂ) ≠ 0` using `(c a).ne_zero`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val, map_one, Units.val_one]`.

Generalize the expression as in `(∫ h : Fˣ, ((μ₁ h : ℂˣ) : ℂ)⁻¹ * ((μ₂ h : ℂˣ) : ℂ) * g ((h : F) * a) * T f ((h : F)⁻¹) ∂multHaar F) = I`. Clear the denominators using the available nonvanishing facts. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[eDual]`. Conclude with `dI`.

Rewrite using `[ePrimal]`. Conclude with `pI`. Establish `t1` using `(GlobalTheory.CompanionTheory.TateFE.sTate F ψ hψ (μ₂ * c) h2c f hf s s0 s1).1`. Establish `t2` using `(GlobalTheory.CompanionTheory.TateFE.sTate F ψ hψ (μ₁ * c) h1c g hg s s0 s1).2`. Rewrite using `[eDual, ePrimal, dE, pE, t1, t2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fe_pt {ψ : AddChar F Circle} (hψ : IsStd ψ) {μ₁ μ₂ : Fˣ →* ℂˣ} (h₁ : IsUnit1 μ₁)
    (h₂ : IsUnit1 μ₂) {c : Fˣ →* ℂˣ} (hc : IsUnit1 c) {s : ℂ} (s0 : 0 < s.re) (s1 : s.re < 1)
    {f g : F → ℂ} (hf : f ∈ schwartzBruhat F) (hg : g ∈ schwartzBruhat F) :
    FEat ψ μ₁ μ₂ c s (W2 ψ μ₁ μ₂ (pt f g)) := by
  set T := localFourier (selfDualMeasure ψ) ψ with hT
  have hTf : T f ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat _ hψ.1 hψ.2.1 hf
  have hTg : T g ∈ schwartzBruhat F := localFourier_mem_schwartzBruhat _ hψ.1 hψ.2.1 hg
  have hβ : IsUnit1 (μ₁⁻¹ * μ₂) := isUnit1_mul (isUnit1_inv h₁) h₂
  have h1c : IsUnit1 (μ₁ * c) := isUnit1_mul h₁ hc
  have h2c : IsUnit1 (μ₂ * c) := isUnit1_mul h₂ hc
  have s0' : 0 < (1 - s).re := by simpa using s1
  obtain ⟨pI, pE⟩ := GlobalTheory.CompanionTheory.DoubleTate.sdz F f hf (fun x => T g (-x)) (comp_neg_mem hTg)
    (μ₂ * c) (μ₁⁻¹ * μ₂) h2c hβ s s0
  obtain ⟨dI, dE⟩ := GlobalTheory.CompanionTheory.DoubleTate.sdz F g hg (T f) hTf
    (μ₁ * c)⁻¹ (μ₁⁻¹ * μ₂) (isUnit1_inv h1c) hβ (1 - s) s0'
  have ch1 : (μ₂ * c) * (μ₁⁻¹ * μ₂)⁻¹ = μ₁ * c := by
    ext a
    have n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0 := (μ₂ a).ne_zero
    have n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := (μ₁ a).ne_zero
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv, inv_inv]
    field_simp
  have ch2 : (μ₁ * c)⁻¹ * (μ₁⁻¹ * μ₂)⁻¹ = (μ₂ * c)⁻¹ := by
    ext a
    have n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0 := (μ₂ a).ne_zero
    have n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := (μ₁ a).ne_zero
    have n3 : ((c a : ℂˣ) : ℂ) ≠ 0 := (c a).ne_zero
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      mul_inv, inv_inv]
    field_simp
  rw [ch1, localZeta_comp_neg] at pE
  rw [ch2] at dE
  have ePrimal : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1) * ((c a : ℂˣ) : ℂ) * mp a (s - 1 / 2)) =
      fun a : Fˣ => (((μ₂ * c) a : ℂˣ) : ℂ) * mp a s *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * f ((h : F) * a) * T g (-((h⁻¹ : Fˣ) : F)) ∂multHaar F := by
    funext a
    rw [GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ μ₁ μ₂ h₁ h₂ f hf g hg a]
    have : mp a s = mp a (1 / 2) * mp a (s - 1 / 2) := by
      rw [← mp_add]; congr 1; ring
    rw [this]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    ring
  have eDual : (fun a : Fˣ => W2 ψ μ₁ μ₂ (pt f g) (dg2 a 1 * w0) *
      (((μ₁ a * μ₂ a * c a)⁻¹ : ℂˣ) : ℂ) * mp a (1 / 2 - s)) =
      fun a : Fˣ => (((μ₁ * c)⁻¹ a : ℂˣ) : ℂ) * mp a (1 - s) *
        ∫ h : Fˣ, (((μ₁⁻¹ * μ₂) h : ℂˣ) : ℂ) * g ((h : F) * a) * T f ((h⁻¹ : Fˣ) : F) ∂multHaar F := by
    clear pI pE dI dE ch1 ch2 ePrimal
    funext a
    have hS := (GlobalTheory.CompanionTheory.WhittakerTrans.sTrans F ψ hψ μ₁ μ₂ h₁ h₂ (pt f g)
      (GlobalTheory.CompanionTheory.WhNe.pt_mem_plane hf hg) w0).2 (dg2 a 1)
    rw [hS, det_weyl_GL2, rightTranslate_pureTensor_weyl, GlobalTheory.CompanionTheory.WhittakerTorus.swd F ψ hψ μ₁ μ₂ h₁ h₂ g hg _ (comp_neg_mem hf) a]
    have hin : ∀ h : Fˣ, localFourier (selfDualMeasure ψ) ψ (fun x => f (-x)) (-((h⁻¹ : Fˣ) : F)) =
        T f ((h⁻¹ : Fˣ) : F) := fun h => by
      rw [localFourier_comp_neg, neg_neg]
    simp only [hin]
    have : mp a (1 - s) = mp a (1 / 2) * mp a (1 / 2 - s) := by
      rw [← mp_add]; congr 1; ring
    rw [this, mp_one_left]
    have n1 : ((μ₁ a : ℂˣ) : ℂ) ≠ 0 := (μ₁ a).ne_zero
    have n2 : ((μ₂ a : ℂˣ) : ℂ) ≠ 0 := (μ₂ a).ne_zero
    have n3 : ((c a : ℂˣ) : ℂ) ≠ 0 := (c a).ne_zero
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, Units.val_inv_eq_inv_val,
      map_one, Units.val_one]
    generalize (∫ h : Fˣ, ((μ₁ h : ℂˣ) : ℂ)⁻¹ * ((μ₂ h : ℂˣ) : ℂ) * g ((h : F) * a) * T f ((h : F)⁻¹)
      ∂multHaar F) = I
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [eDual]; exact dI
  · rw [ePrimal]; exact pI
  · have t1 := (GlobalTheory.CompanionTheory.TateFE.sTate F ψ hψ (μ₂ * c) h2c f hf s s0 s1).1
    have t2 := (GlobalTheory.CompanionTheory.TateFE.sTate F ψ hψ (μ₁ * c) h1c g hg s s0 s1).2
    rw [eDual, ePrimal, dE, pE, t1, t2]
    ring

/- English proof (translation)
Introduce `F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s s0 s1`. Take `⟨n, f, g, hfg, rfl⟩` from `GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt F φ hφ`. Establish `key : ∀ t : Finset (Fin n), (∑ i ∈ t, pt (f i) (g i)) ∈ GodementSectionLocal.schwartzBruhat2 F ∧ FEat ψ μ₁ μ₂ c s (W2 ψ μ₁ μ₂ (∑ i ∈ t, pt (f i) (g i)))`. Introduce `t`. Proceed by induction on `t using Finset.induction_on with`.

Consider the case `empty`. Use `⟨by simpa using Submodule.zero_mem _, ?_⟩` and prove the remaining obligations. Establish `hz` using `(GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _)).2 0`. Simplify using `only [zero_smul] at hz`. Simplify `FEat.zero ψ μ₁ μ₂ c s` using `[hz]`.

Consider the case `insert i t hi ih`. Establish `hp` using `GlobalTheory.CompanionTheory.WhNe.pt_mem_plane (hfg i).1 (hfg i).2`. Rewrite using `[Finset.sum_insert hi]`. Use `⟨Submodule.add_mem _ hp ih.1, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ hp _ ih.1).1]`.

Conclude with `(fe_pt hψ h₁ h₂ hc s0 s1 (hfg i).1 (hfg i).2).add ih.2`. Conclude with `(key Finset.univ).2`.
-/
theorem feGen : FeGen := by
  intro F _ _ _ _ _ _ ψ hψ μ₁ μ₂ h₁ h₂ φ hφ c hc s s0 s1
  obtain ⟨n, f, g, hfg, rfl⟩ := GlobalTheory.CompanionTheory.PlanePure.schwartzBruhat2_eq_sum_pt F φ hφ
  have key : ∀ t : Finset (Fin n), (∑ i ∈ t, pt (f i) (g i)) ∈ GodementSectionLocal.schwartzBruhat2 F ∧
      FEat ψ μ₁ μ₂ c s (W2 ψ μ₁ μ₂ (∑ i ∈ t, pt (f i) (g i))) := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      refine ⟨by simpa using Submodule.zero_mem _, ?_⟩
      have hz := (GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ 0 (Submodule.zero_mem _) 0
        (Submodule.zero_mem _)).2 0
      simp only [zero_smul] at hz
      simpa [hz] using FEat.zero ψ μ₁ μ₂ c s
    | insert i t hi ih =>
      have hp := GlobalTheory.CompanionTheory.WhNe.pt_mem_plane (hfg i).1 (hfg i).2
      rw [Finset.sum_insert hi]
      refine ⟨Submodule.add_mem _ hp ih.1, ?_⟩
      rw [(GlobalTheory.CompanionTheory.WhitLin.whittaker_linear_in_schwartz_bruhat F ψ hψ μ₁ μ₂ h₁ h₂ _ hp _ ih.1).1]
      exact (fe_pt hψ h₁ h₂ hc s0 s1 (hfg i).1 (hfg i).2).add ih.2
  exact (key Finset.univ).2

end GlobalTheory.CompanionTheory.WhitFE
