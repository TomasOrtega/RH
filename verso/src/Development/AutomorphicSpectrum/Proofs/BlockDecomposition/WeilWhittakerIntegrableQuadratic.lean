import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.SquareIntegrable.SSmooth
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TemperedBoundGL2
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSmoothCharCompNorm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WcEqZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerBoundQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilCharacterTwistNontrivialGaloisStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisConjugateStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNontrivialGaloisIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactTranslateEntriesBoundedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenNormImageUnitsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormImageNeighbourhoodEventuallyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuityQuadraticExtensionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasureIndependenceStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WcB.CaseZero

/- English proof (translation)
Establish `hδ0 : 0 < δ` using `hδ ▸ mul_pos ha hb`. Establish `hXY : 0 < X / Y` using `div_pos hX hY`. Establish `e1 : (X * Y * δ) ^ (1 / 2 : ℝ) = (X / Y) ^ (1 / 2 : ℝ) * Y * δ ^ (1 / 2 : ℝ)`. Establish `: X * Y * δ = (X / Y) * Y ^ 2 * δ` using `by field_simp`. Rewrite using `[this, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_mul hXY.le, Real.sqrt_sq hY.le]`.

Establish `e2 : a⁻¹ = b * δ⁻¹` using `by rw [hδ]; field_simp`. Establish `e3 : (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * a)⁻¹ * P = δ ^ (1 / 2 : ℝ) * δ⁻¹ * b * P * (X / Y) ^ (1 / 2 : ℝ)`. Rewrite using `[e1, mul_inv, e2]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[e3]`.

Establish `h1 : 0 ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹` using `by positivity`. Establish `h2 : 0 ≤ (X / Y) ^ (1 / 2 : ℝ)` using `by positivity`. Establish `h3 : b * P ≤ M * S` using `mul_le_mul hbM hPS hP0 (hb.le.trans hbM)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem real_bound {X Y a b δ M S P : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hb : 0 < b)
    (hδ : δ = a * b) (hbM : b ≤ M) (hP0 : 0 ≤ P) (hPS : P ≤ S) :
    (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * a)⁻¹ * P ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ * M * S * (X / Y) ^ (1 / 2 : ℝ) := by
  have hδ0 : 0 < δ := hδ ▸ mul_pos ha hb
  have hXY : 0 < X / Y := div_pos hX hY
  have e1 : (X * Y * δ) ^ (1 / 2 : ℝ) = (X / Y) ^ (1 / 2 : ℝ) * Y * δ ^ (1 / 2 : ℝ) := by
    have : X * Y * δ = (X / Y) * Y ^ 2 * δ := by field_simp
    rw [this, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
      Real.sqrt_mul (by positivity), Real.sqrt_mul hXY.le, Real.sqrt_sq hY.le]
  have e2 : a⁻¹ = b * δ⁻¹ := by rw [hδ]; field_simp
  have e3 : (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * a)⁻¹ * P
      = δ ^ (1 / 2 : ℝ) * δ⁻¹ * b * P * (X / Y) ^ (1 / 2 : ℝ) := by
    rw [e1, mul_inv, e2]
    field_simp
  rw [e3]
  have h1 : 0 ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ := by positivity
  have h2 : 0 ≤ (X / Y) ^ (1 / 2 : ℝ) := by positivity
  have h3 : b * P ≤ M * S := mul_le_mul hbM hPS hP0 (hb.le.trans hbM)
  calc δ ^ (1 / 2 : ℝ) * δ⁻¹ * b * P * (X / Y) ^ (1 / 2 : ℝ)
      = δ ^ (1 / 2 : ℝ) * δ⁻¹ * (b * P) * (X / Y) ^ (1 / 2 : ℝ) := by ring
    _ ≤ δ ^ (1 / 2 : ℝ) * δ⁻¹ * (M * S) * (X / Y) ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by ring

/- English proof (translation)
Establish `e : X / Y = T * a ^ 2 / δ` using `by rw [hT]; field_simp`. Rewrite using `[e]`. Establish `hT0 : 0 ≤ T` using `by rw [hT]; positivity`. Use `gcongr`. Conclude with `hT0.trans hTR`.
-/
theorem real_support {X Y a δ M T R : ℝ} (hX : 0 < X) (hY : 0 < Y) (ha : 0 < a) (hδ0 : 0 < δ)
    (haM : a ≤ M) (hT : T = ((Y * a) ^ 2)⁻¹ * (X * Y * δ)) (hTR : T ≤ R) :
    X / Y ≤ R * M ^ 2 / δ := by
  have e : X / Y = T * a ^ 2 / δ := by rw [hT]; field_simp
  rw [e]
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  gcongr
  exact hT0.trans hTR

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hc hΦ hcs h₀`. Take `⟨M, hM, hMat⟩` from `GlobalTheory.T.compact_translate_entries_bounded F h₀`. Establish `hcont : Continuous Φ` using `hΦ.continuous`. Take `⟨S, hS⟩` from `hcs.exists_bound_of_continuous hcont`. Establish `hS0 : 0 ≤ S` using `(norm_nonneg _).trans (hS 0)`.

Establish `hmodc : Continuous fun e : E => (modulus e : ℝ)` using `NNReal.continuous_coe.comp continuous_modulus`. Take `⟨R, hR⟩` from `hcs.isCompact.bddAbove_image hmodc.continuousOn`. Establish `hRΦ : ∀ e, Φ e ≠ 0 → (modulus e : ℝ) ≤ R` using `fun e he => hR (Set.mem_image_of_mem _ (subset_tsupport _ he))`. Use `set δ : ℝ := (modulus (h₀.val).det : ℝ) with hδdef`. Establish `hdet0 : (h₀.val).det ≠ 0`.

Use `(Matrix.isUnit_iff_isUnit_det _).1 h₀.isUnit` as an intermediate fact. Conclude with `this.ne_zero`. Establish `hδ0 : 0 < δ`. Simplify `modulus_pos hdet0` using `[hδdef]`. Use `⟨δ ^ (1 / 2 : ℝ) * δ⁻¹ * M * S, max 1 (R * M ^ 2 / δ), by positivity, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩` and prove the remaining obligations.

Introduce `x y k hk h10`. Take `⟨hent, hdetm⟩` from `hMat k hk`. Use `set m : GL (Fin 2) F := k * h₀ with hm`. Establish `hg : dg2 x y * k * h₀ = dg2 x y * m` using `by rw [hm, mul_assoc]`. Rewrite using `[hg]`.

Use `set g : GL (Fin 2) F := dg2 x y * m with hgdef`. Establish `hg10 : g.val 1 0 = 0`. Simplify using `[hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two, h10]`. Establish `hg11 : g.val 1 1 = (y : F) * m.val 1 1`. Simplify using `[hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `hgdet : (g.val).det = (x : F) * y * (m.val).det`. Rewrite using `[hgdef, Units.val_mul, Matrix.det_mul]`. Simplify using `[dg2, Matrix.det_fin_two]`. Establish `hmdet : (m.val).det = m.val 0 0 * m.val 1 1`. Simplify using `[Matrix.det_fin_two, h10]`.

Establish `hmdet0 : (m.val).det ≠ 0`. Use `(Matrix.isUnit_iff_isUnit_det _).1 m.isUnit` as an intermediate fact. Conclude with `this.ne_zero`. Establish `h00 : m.val 0 0 ≠ 0` using `fun h => hmdet0 (by rw [hmdet, h, zero_mul])`. Establish `h11 : m.val 1 1 ≠ 0` using `fun h => hmdet0 (by rw [hmdet, h, mul_zero])`.

Use `set X : ℝ := (modulus (x : F) : ℝ) with hXdef`. Use `set Y : ℝ := (modulus (y : F) : ℝ) with hYdef`. Use `set a : ℝ := (modulus (m.val 1 1) : ℝ) with hadef`. Use `set b : ℝ := (modulus (m.val 0 0) : ℝ) with hbdef`. Establish `hX : 0 < X` using `by simpa [hXdef] using modulus_pos x.ne_zero`.

Establish `hY : 0 < Y` using `by simpa [hYdef] using modulus_pos y.ne_zero`. Establish `ha : 0 < a` using `by simpa [hadef] using modulus_pos h11`. Establish `hb : 0 < b` using `by simpa [hbdef] using modulus_pos h00`. Establish `hδab : δ = a * b`. Rewrite using `[hδdef, ← hdetm, hmdet, modulus_mul, hadef, hbdef]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hxy : (modulus (((x / y : Fˣ)) : F) : ℝ) = X / Y`. Rewrite using `[Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]`. Use `push_cast`.

Rewrite using `[hXdef, hYdef, div_eq_mul_inv]`. Establish `hmg : (modulus (g.val).det : ℝ) = X * Y * δ`. Rewrite using `[hgdet, modulus_mul, modulus_mul, hdetm]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `hm11 : (modulus (g.val 1 1) : ℝ) = Y * a`. Rewrite using `[hg11, modulus_mul]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[hxy]`.

Distinguish the cases in `hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0`. Use `⟨?_, fun h => absurd hW h⟩` and prove the remaining obligations. Rewrite using `[hW, norm_zero]`. Check the signs of the components of the expression. Take `⟨t, htN, hval⟩` from `GlobalTheory.T.weil_whittaker_galois_conjugate F E χ σ μ lam c Φ hc g hg10 hW`.

Use `⟨?_, fun _ => ?_⟩` and prove the remaining obligations. Rewrite using `[hval, hmg, hm11]`. Conclude with `real_bound hX hY ha hb hδab (hent 0 0) (norm_nonneg _) (hS _)`. Establish `hΦτ : Φ (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) ≠ 0`. Introduce `h0`.

Apply `hW` to reduce the goal to its premises. Establish `: ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = 0` using `by rw [hval, h0]; simp`. Conclude with `norm_eq_zero.1 this`. Establish `hT` using `hRΦ _ hΦτ`. Establish `hmodτ : (modulus (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) : ℝ) = ((Y * a) ^ 2)⁻¹ * (X * Y * δ)`.

Rewrite using `[modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F) (E := E), ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E) (t : E), htN, modulus_inv]`. Use `push_cast`. Rewrite using `[hm11, hmg]`. Clear the denominators using the available nonvanishing facts. Conclude with `(real_support hX hY ha hδ0 (hent 1 1) hmodτ hT).trans (le_max_right _ _)`.
-/
theorem borel_bound : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle) (σ : E ≃ₐ[F] E) (μ : Measure E) (lam : ℂ) (c : Eˣ →* ℂˣ) (Φ : E → ℂ), IsUnit1 c → IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 = 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ σ μ lam c Φ hc hΦ hcs h₀
  obtain ⟨M, hM, hMat⟩ := GlobalTheory.T.compact_translate_entries_bounded F h₀
  have hcont : Continuous Φ := hΦ.continuous
  obtain ⟨S, hS⟩ := hcs.exists_bound_of_continuous hcont
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  have hmodc : Continuous fun e : E => (modulus e : ℝ) :=
    NNReal.continuous_coe.comp continuous_modulus
  obtain ⟨R, hR⟩ := hcs.isCompact.bddAbove_image hmodc.continuousOn
  have hRΦ : ∀ e, Φ e ≠ 0 → (modulus e : ℝ) ≤ R := fun e he =>
    hR (Set.mem_image_of_mem _ (subset_tsupport _ he))
  set δ : ℝ := (modulus (h₀.val).det : ℝ) with hδdef
  have hdet0 : (h₀.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 h₀.isUnit
    exact this.ne_zero
  have hδ0 : 0 < δ := by
    simpa [hδdef] using modulus_pos hdet0
  refine ⟨δ ^ (1 / 2 : ℝ) * δ⁻¹ * M * S, max 1 (R * M ^ 2 / δ), by positivity,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x y k hk h10
  obtain ⟨hent, hdetm⟩ := hMat k hk
  set m : GL (Fin 2) F := k * h₀ with hm
  have hg : dg2 x y * k * h₀ = dg2 x y * m := by rw [hm, mul_assoc]
  rw [hg]
  set g : GL (Fin 2) F := dg2 x y * m with hgdef
  have hg10 : g.val 1 0 = 0 := by
    simp [hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two, h10]
  have hg11 : g.val 1 1 = (y : F) * m.val 1 1 := by
    simp [hgdef, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have hgdet : (g.val).det = (x : F) * y * (m.val).det := by
    rw [hgdef, Units.val_mul, Matrix.det_mul]
    simp [dg2, Matrix.det_fin_two]
  have hmdet : (m.val).det = m.val 0 0 * m.val 1 1 := by
    simp [Matrix.det_fin_two, h10]
  have hmdet0 : (m.val).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det _).1 m.isUnit
    exact this.ne_zero
  have h00 : m.val 0 0 ≠ 0 := fun h => hmdet0 (by rw [hmdet, h, zero_mul])
  have h11 : m.val 1 1 ≠ 0 := fun h => hmdet0 (by rw [hmdet, h, mul_zero])
  set X : ℝ := (modulus (x : F) : ℝ) with hXdef
  set Y : ℝ := (modulus (y : F) : ℝ) with hYdef
  set a : ℝ := (modulus (m.val 1 1) : ℝ) with hadef
  set b : ℝ := (modulus (m.val 0 0) : ℝ) with hbdef
  have hX : 0 < X := by simpa [hXdef] using modulus_pos x.ne_zero
  have hY : 0 < Y := by simpa [hYdef] using modulus_pos y.ne_zero
  have ha : 0 < a := by simpa [hadef] using modulus_pos h11
  have hb : 0 < b := by simpa [hbdef] using modulus_pos h00
  have hδab : δ = a * b := by
    rw [hδdef, ← hdetm, hmdet, modulus_mul, hadef, hbdef]
    push_cast
    ring
  have hxy : (modulus (((x / y : Fˣ)) : F) : ℝ) = X / Y := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    rw [hXdef, hYdef, div_eq_mul_inv]
  have hmg : (modulus (g.val).det : ℝ) = X * Y * δ := by
    rw [hgdet, modulus_mul, modulus_mul, hdetm]
    push_cast
    rfl
  have hm11 : (modulus (g.val 1 1) : ℝ) = Y * a := by
    rw [hg11, modulus_mul]
    push_cast
    rfl
  rw [hxy]
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0
  · refine ⟨?_, fun h => absurd hW h⟩
    rw [hW, norm_zero]
    positivity
  obtain ⟨t, htN, hval⟩ := GlobalTheory.T.weil_whittaker_galois_conjugate F E χ σ μ lam c Φ hc g hg10 hW
  refine ⟨?_, fun _ => ?_⟩
  · rw [hval, hmg, hm11]
    exact real_bound hX hY ha hb hδab (hent 0 0) (norm_nonneg _) (hS _)
  · have hΦτ : Φ (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) ≠ 0 := by
      intro h0
      apply hW
      have : ‖GL2LocalData.Wc χ σ μ lam c Φ g‖ = 0 := by rw [hval, h0]; simp
      exact norm_eq_zero.1 this
    have hT := hRΦ _ hΦτ
    have hmodτ : (modulus (algebraMap F E (g.val 1 1)⁻¹ * (t : E)) : ℝ)
        = ((Y * a) ^ 2)⁻¹ * (X * Y * δ) := by
      rw [modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F) (E := E),
        ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (E := E) (t : E), htN, modulus_inv]
      push_cast
      rw [hm11, hmg]
      field_simp
    exact (real_support hX hY ha hδ0 (hent 1 1) hmodτ hT).trans (le_max_right _ _)

end GlobalTheory.CompanionTheory.WcB.CaseZero
