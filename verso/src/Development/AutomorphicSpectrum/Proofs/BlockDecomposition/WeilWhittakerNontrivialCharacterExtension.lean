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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerNonvanishingCharacterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerMeasurabilityStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerGaloisInvarianceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerIntegrableQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerContinuousQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerSupportBoundQuadraticStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilWhittakerCentralTwistStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.DualHol
open GlobalTheory.CompanionTheory.WcB
open scoped Topology

namespace GlobalTheory.CompanionTheory.WhitOffBorel

/- English proof (translation)
Establish `hXY : 0 < X / Y` using `div_pos hX hY`. Take `⟨s, hs⟩ : ∃ s, s = Real.sqrt (X / Y)` from `⟨_, rfl⟩`. Take `⟨d, hd⟩ : ∃ d, d = Real.sqrt δ` from `⟨_, rfl⟩`. Establish `hs0 : 0 < s` using `hs ▸ Real.sqrt_pos.2 hXY`. Establish `hd0 : 0 < d` using `hd ▸ Real.sqrt_pos.2 hδ`.

Establish `hss : s * s = X / Y` using `by rw [hs]; exact Real.mul_self_sqrt hXY.le`. Establish `hdd : d * d = δ` using `by rw [hd]; exact Real.mul_self_sqrt hδ.le`. Establish `e : (X * Y * δ) ^ (1 / 2 : ℝ) = s * d * Y`. Rewrite using `[← Real.sqrt_eq_rpow]`. Establish `: X * Y * δ = (s * d * Y) ^ 2`.

Establish `: (s * d * Y) ^ 2 = (s * s) * (d * d) * Y ^ 2` using `by ring`. Rewrite using `[this, hss, hdd]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[this, Real.sqrt_sq (by positivity)]`. Rewrite using `[e, ← Real.sqrt_eq_rpow (X / Y), ← hs, ← hd]`.

Establish `hmax : p * max 1 (q / p) = max p q`. Rewrite using `[mul_max_of_nonneg _ _ hp.le, mul_one, mul_div_cancel₀ _ hp.ne']`. Establish `key : I * max p q ≤ |C₀| * p`. Rewrite using `[← hmax]`. Combine the equalities or inequalities in the displayed calculation.

Establish `key2 : d * d * I ≤ |C₀| * M * p`. Rewrite using `[hdd]`. Combine the equalities or inequalities in the displayed calculation. Establish `key3 : d * I / p ≤ |C₀| * M / d`. Rewrite using `[div_le_div_iff₀ hp hd0]`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Clear the denominators using the available nonvanishing facts. Use `_ ≤ (L * s) * (|C₀| * M / d) := mul_le_mul_of_nonneg_left key3 (by positivity)`. Use `_ = L * d⁻¹ * |C₀| * M * s := by field_simp`.
-/
theorem real_bound {X Y δ p q M I C₀ L : ℝ} (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ) (hp : 0 < p)
    (hM : 0 < M) (hI : 0 ≤ I) (hL : 0 ≤ L)
    (h1 : I * max 1 (q / p) ≤ C₀) (h2 : δ ≤ M * max p q) :
    L * (X * Y * δ) ^ (1 / 2 : ℝ) * (Y * p)⁻¹ * I ≤
      (L * (Real.sqrt δ)⁻¹ * |C₀| * M) * (X / Y) ^ (1 / 2 : ℝ) := by
  have hXY : 0 < X / Y := div_pos hX hY
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (X / Y) := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Real.sqrt δ := ⟨_, rfl⟩
  have hs0 : 0 < s := hs ▸ Real.sqrt_pos.2 hXY
  have hd0 : 0 < d := hd ▸ Real.sqrt_pos.2 hδ
  have hss : s * s = X / Y := by rw [hs]; exact Real.mul_self_sqrt hXY.le
  have hdd : d * d = δ := by rw [hd]; exact Real.mul_self_sqrt hδ.le
  have e : (X * Y * δ) ^ (1 / 2 : ℝ) = s * d * Y := by
    rw [← Real.sqrt_eq_rpow]
    have : X * Y * δ = (s * d * Y) ^ 2 := by
      have : (s * d * Y) ^ 2 = (s * s) * (d * d) * Y ^ 2 := by ring
      rw [this, hss, hdd]; field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  rw [e, ← Real.sqrt_eq_rpow (X / Y), ← hs, ← hd]
  have hmax : p * max 1 (q / p) = max p q := by
    rw [mul_max_of_nonneg _ _ hp.le, mul_one, mul_div_cancel₀ _ hp.ne']
  have key : I * max p q ≤ |C₀| * p := by
    rw [← hmax]
    calc I * (p * max 1 (q / p)) = (I * max 1 (q / p)) * p := by ring
      _ ≤ |C₀| * p := mul_le_mul_of_nonneg_right (h1.trans (le_abs_self _)) hp.le
  have key2 : d * d * I ≤ |C₀| * M * p := by
    rw [hdd]
    calc δ * I ≤ (M * max p q) * I := mul_le_mul_of_nonneg_right h2 hI
      _ = M * (I * max p q) := by ring
      _ ≤ M * (|C₀| * p) := mul_le_mul_of_nonneg_left key hM.le
      _ = |C₀| * M * p := by ring
  have key3 : d * I / p ≤ |C₀| * M / d := by
    rw [div_le_div_iff₀ hp hd0]
    calc d * I * d = d * d * I := by ring
      _ ≤ |C₀| * M * p := key2
  calc L * (s * d * Y) * (Y * p)⁻¹ * I = (L * s) * (d * I / p) := by
        field_simp
    _ ≤ (L * s) * (|C₀| * M / d) := mul_le_mul_of_nonneg_left key3 (by positivity)
    _ = L * d⁻¹ * |C₀| * M * s := by field_simp

/- English proof (translation)
Establish `e : (X * Y * δ / (Y * p)) ^ 2 * (X * Y * δ)⁻¹ = (X / Y) * δ / p ^ 2`. Clear the denominators using the available nonvanishing facts. Rewrite `h` using `[e]`. Establish `hM : 0 < M` using `hp.trans_le hpM`. Establish `hm : max 1 ((q / p) ^ 2) ≤ M ^ 2 / p ^ 2`.

Use `max_le ?_ ?_` and prove the remaining obligations. Rewrite using `[le_div_iff₀ (by positivity), one_mul]`. Conclude with `pow_le_pow_left₀ hp.le hpM 2`. Rewrite using `[div_pow]`. Conclude with `div_le_div_of_nonneg_right (pow_le_pow_left₀ hq hqM 2) (by positivity)`.

Establish `h3 : (X / Y) * δ / p ^ 2 ≤ |R| * (M ^ 2 / p ^ 2)` using `h.trans ((mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)).trans (mul_le_mul_of_nonneg_left hm (abs_nonneg R)))`. Establish `h4 : (X / Y) * δ ≤ |R| * M ^ 2`. Establish `hp2 : 0 < p ^ 2` using `by positivity`. Use `mul_le_mul_of_nonneg_right h3 hp2.le` as an intermediate fact. Establish `e1 : (X / Y) * δ / p ^ 2 * p ^ 2 = (X / Y) * δ` using `by field_simp`.

Establish `e2 : |R| * (M ^ 2 / p ^ 2) * p ^ 2 = |R| * M ^ 2` using `by field_simp`. Rewrite `this` using `[e1, e2]`. Then use the resulting hypothesis. Conclude with `le_max_of_le_right ((le_div_iff₀ hδ).2 h4)`.
-/
theorem real_supp {X Y δ p q M R : ℝ} (hX : 0 < X) (hY : 0 < Y) (hδ : 0 < δ) (hp : 0 < p)
    (hq : 0 ≤ q) (hpM : p ≤ M) (hqM : q ≤ M)
    (h : (X * Y * δ / (Y * p)) ^ 2 * (X * Y * δ)⁻¹ ≤ R * max 1 ((q / p) ^ 2)) :
    X / Y ≤ max 1 (|R| * M ^ 2 / δ) := by
  have e : (X * Y * δ / (Y * p)) ^ 2 * (X * Y * δ)⁻¹ = (X / Y) * δ / p ^ 2 := by
    field_simp
  rw [e] at h
  have hM : 0 < M := hp.trans_le hpM
  have hm : max 1 ((q / p) ^ 2) ≤ M ^ 2 / p ^ 2 := by
    refine max_le ?_ ?_
    · rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hp.le hpM 2
    · rw [div_pow]
      exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hq hqM 2) (by positivity)
  have h3 : (X / Y) * δ / p ^ 2 ≤ |R| * (M ^ 2 / p ^ 2) :=
    h.trans ((mul_le_mul_of_nonneg_right (le_abs_self R) (by positivity)).trans
      (mul_le_mul_of_nonneg_left hm (abs_nonneg R)))
  have h4 : (X / Y) * δ ≤ |R| * M ^ 2 := by
    have hp2 : 0 < p ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right h3 hp2.le
    have e1 : (X / Y) * δ / p ^ 2 * p ^ 2 = (X / Y) * δ := by field_simp
    have e2 : |R| * (M ^ 2 / p ^ 2) * p ^ 2 = |R| * M ^ 2 := by field_simp
    rwa [e1, e2] at this
  exact le_max_of_le_right ((le_div_iff₀ hδ).2 h4)

/- English proof (translation)
Introduce `F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχc hχ1 σ hσ μ _ lam c hc Φ hΦl hΦc h₀`. Take `⟨C₀, hC₀⟩` from `GlobalTheory.T.weil_whittaker_nonvanishing_character F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc`. Take `⟨R, hR⟩` from `GlobalTheory.T.weil_whittaker_measurability F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc`. Take `⟨M, hM0, hM⟩` from `GlobalTheory.T.compact_translate_entries_bounded F h₀`. Establish `hδ₀ : (0 : ℝ) < (modulus (h₀.val).det : ℝ)`.

Establish `hne : (h₀.val).det ≠ 0`. Use `(Matrix.isUnits_det_units h₀)` as an intermediate fact. Conclude with `this.ne_zero`. Conclude with `modulus_pos hne` after adjusting the coercions. Use `⟨‖lam‖ * (Real.sqrt (modulus (h₀.val).det : ℝ))⁻¹ * |C₀| * M, max 1 (|R| * M ^ 2 / (modulus (h₀.val).det : ℝ)), by positivity, lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩` and prove the remaining obligations.

Introduce `x y k hk hne`. Take `⟨hent, hdet⟩` from `hM k hk`. Rewrite using `[mul_assoc (dg2 x y) k h₀]`. Take `⟨m, hm⟩ : ∃ m, m = k * h₀` from `⟨_, rfl⟩`. Rewrite `hne`, `hent`, `hdet`, the goal using `[← hm]`.

Take `⟨g, hg⟩ : ∃ g, g = dg2 x y * m` from `⟨_, rfl⟩`. Rewrite using `[← hg]`. Establish `g10 : g.val 1 0 = y * m.val 1 0`. Simplify using `[hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `g11 : g.val 1 1 = y * m.val 1 1`.

Simplify using `[hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]`. Establish `gdet : (g.val).det = x * y * (m.val).det`. Rewrite using `[hg, Units.val_mul, Matrix.det_mul]`. Simplify using `[dg2, Matrix.det_fin_two_of]`. Establish `hXp : (0 : ℝ) < (modulus (x : F) : ℝ)` using `by exact_mod_cast modulus_pos x.ne_zero`.

Establish `hYp : (0 : ℝ) < (modulus (y : F) : ℝ)` using `by exact_mod_cast modulus_pos y.ne_zero`. Establish `hpp : (0 : ℝ) < (modulus (m.val 1 0) : ℝ)` using `by exact_mod_cast modulus_pos hne`. Establish `hxy : (modulus ((x / y : Fˣ) : F) : ℝ) = (modulus (x : F) : ℝ) / (modulus (y : F) : ℝ)`. Rewrite using `[Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]`. Use `push_cast`.

Rewrite using `[div_eq_mul_inv]`. Establish `mg10 : (modulus (g.val 1 0) : ℝ) = (modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ)`. Rewrite using `[g10, modulus_mul]`. Use `push_cast`. Both sides reduce to the same expression.

Establish `mgdet : (modulus (g.val).det : ℝ) = (modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ)`. Rewrite using `[gdet, modulus_mul, modulus_mul, hdet]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hg10 : g.val 1 0 ≠ 0`.

Rewrite using `[g10]`. Conclude with `mul_ne_zero y.ne_zero hne`. Establish `mκ : (modulus (g.val 1 1 / g.val 1 0) : ℝ) = (modulus (m.val 1 1) : ℝ) / (modulus (m.val 1 0) : ℝ)`. Rewrite using `[g10, g11, div_eq_mul_inv, modulus_mul, modulus_inv, modulus_mul, modulus_mul]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Distinguish the cases in `hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0`. Rewrite using `[hW, norm_zero]`. Use `⟨by positivity, fun h => absurd rfl h⟩` and prove the remaining obligations. Take `⟨t, htN, hval⟩` from `GlobalTheory.T.weil_whittaker_galois_invariance F E χ σ hσ μ lam c hc Φ g hg10 hW`.

Establish `hI0 : gaussI χ μ Φ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) ≠ 0`. Introduce `h0`. Rewrite `hval` using `[h0, norm_zero, mul_zero]`. Conclude with `hW (norm_eq_zero.1 hval)`. Use `⟨?_, fun _ => ?_⟩` and prove the remaining obligations.

Rewrite using `[hval, mgdet, mg10, hxy]`. Use `GlobalTheory.CompanionTheory.WhitOffBorel.real_bound (q := (modulus (m.val 1 1) : ℝ)) hXp hYp hδ₀ hpp hM0 (norm_nonneg _) (norm_nonneg _) ?_ ?_` and prove the remaining obligations. Use `hC₀ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹)` as an intermediate fact. Rewrite `this` using `[mκ]`. Then use the resulting hypothesis. Establish `hpm : (modulus (m.val 1 0) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ)` using `le_max_left _ _`.

Establish `hqm : (modulus (m.val 1 1) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ)` using `le_max_right _ _`. Establish `hn1 : (modulus (-1 : F) : ℝ) ≤ 1`. Conclude with `(modulus_le_one_iff (K := F)).2 (neg_mem (one_mem _))` after adjusting the coercions. Establish `t1 : (modulus (m.val 0 0 * m.val 1 1) : ℝ) ≤ M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ)`. Rewrite using `[modulus_mul]`.

Use `push_cast`. Conclude with `mul_le_mul (hent 0 0) hqm (NNReal.coe_nonneg _) hM0.le`. Establish `t2 : (modulus (-(m.val 0 1 * m.val 1 0)) : ℝ) ≤ M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ)`. Establish `e : -(m.val 0 1 * m.val 1 0) = (-1) * (m.val 0 1 * m.val 1 0)` using `by ring`. Rewrite using `[e, modulus_mul, modulus_mul]`.

Use `push_cast`. Combine the equalities or inequalities in the displayed calculation. Establish `hd : (m.val).det = m.val 0 0 * m.val 1 1 + -(m.val 0 1 * m.val 1 0)`. Rewrite using `[Matrix.det_fin_two]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hdd : (modulus (h₀.val).det : ℝ) = (modulus (m.val).det : ℝ)` using `by rw [hdet]`. Rewrite using `[hdd, hd]`. Conclude with `(GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le t1 t2)`. Rewrite using `[hxy]`. Establish `hs` using `hR _ _ hI0`.

Establish `mξ : (modulus (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) : ℝ) = ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ) / ((modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ))) ^ 2 * ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val). …`. Rewrite using `[modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F), modulus_inv, ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (t : E), htN, div_eq_mul_inv, modulus_mul, modulus_inv]`. Use `push_cast`. Rewrite using `[mgdet, mg10, div_eq_mul_inv]`. Rewrite `hs` using `[mξ, mκ]`.

Conclude with `GlobalTheory.CompanionTheory.WhitOffBorel.real_supp hXp hYp hδ₀ hpp (NNReal.coe_nonneg _) (hent 1 0) (hent 1 1) hs`.
-/
theorem whittaker_off_borel : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)] (χ : AddChar F Circle), Continuous χ → χ ≠ 1 → ∀ σ : E ≃ₐ[F] E, σ ≠ AlgEquiv.refl → ∀ (μ : Measure E) [μ.IsAddHaarMeasure] (lam : ℂ) (c : Eˣ →* ℂˣ), IsUnit1 c → ∀ Φ : E → ℂ, IsLocallyConstant Φ → HasCompactSupport Φ → ∀ h₀ : GL (Fin 2) F, ∃ C B : ℝ, 0 ≤ C ∧ 0 < B ∧ ∀ (x y : Fˣ), ∀ k ∈ GLnLocal.integralGL F 2, (k * h₀).val 1 0 ≠ 0 → ‖GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀)‖ ≤ C * (modulus ((x / y : Fˣ) : F) : ℝ) ^ (1 / 2 : ℝ) ∧ (GL2LocalData.Wc χ σ μ lam c Φ (dg2 x y * k * h₀) ≠ 0 → (modulus ((x / y : Fˣ) : F) : ℝ) ≤ B) := by
  intro F _ _ _ _ _ _ E _ _ _ _ _ _ _ _ _ _ _ χ hχc hχ1 σ hσ μ _ lam c hc Φ hΦl hΦc h₀
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.weil_whittaker_nonvanishing_character F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc
  obtain ⟨R, hR⟩ := GlobalTheory.T.weil_whittaker_measurability F E χ hχc hχ1 σ hσ μ Φ hΦl hΦc
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.compact_translate_entries_bounded F h₀
  have hδ₀ : (0 : ℝ) < (modulus (h₀.val).det : ℝ) := by
    have hne : (h₀.val).det ≠ 0 := by
      have := (Matrix.isUnits_det_units h₀)
      exact this.ne_zero
    exact_mod_cast modulus_pos hne
  refine ⟨‖lam‖ * (Real.sqrt (modulus (h₀.val).det : ℝ))⁻¹ * |C₀| * M,
    max 1 (|R| * M ^ 2 / (modulus (h₀.val).det : ℝ)), by positivity,
    lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro x y k hk hne
  obtain ⟨hent, hdet⟩ := hM k hk
  rw [mul_assoc (dg2 x y) k h₀]
  obtain ⟨m, hm⟩ : ∃ m, m = k * h₀ := ⟨_, rfl⟩
  rw [← hm] at hne hent hdet ⊢
  obtain ⟨g, hg⟩ : ∃ g, g = dg2 x y * m := ⟨_, rfl⟩
  rw [← hg]
  have g10 : g.val 1 0 = y * m.val 1 0 := by
    simp [hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have g11 : g.val 1 1 = y * m.val 1 1 := by
    simp [hg, dg2, Matrix.mul_apply, Fin.sum_univ_two]
  have gdet : (g.val).det = x * y * (m.val).det := by
    rw [hg, Units.val_mul, Matrix.det_mul]
    simp [dg2, Matrix.det_fin_two_of]
  have hXp : (0 : ℝ) < (modulus (x : F) : ℝ) := by exact_mod_cast modulus_pos x.ne_zero
  have hYp : (0 : ℝ) < (modulus (y : F) : ℝ) := by exact_mod_cast modulus_pos y.ne_zero
  have hpp : (0 : ℝ) < (modulus (m.val 1 0) : ℝ) := by exact_mod_cast modulus_pos hne
  have hxy : (modulus ((x / y : Fˣ) : F) : ℝ) = (modulus (x : F) : ℝ) / (modulus (y : F) : ℝ) := by
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, modulus_mul, modulus_inv]
    push_cast
    rw [div_eq_mul_inv]
  have mg10 : (modulus (g.val 1 0) : ℝ) = (modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ) := by
    rw [g10, modulus_mul]; push_cast; rfl
  have mgdet : (modulus (g.val).det : ℝ) =
      (modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ) := by
    rw [gdet, modulus_mul, modulus_mul, hdet]; push_cast; rfl
  have hg10 : g.val 1 0 ≠ 0 := by
    rw [g10]; exact mul_ne_zero y.ne_zero hne
  have mκ : (modulus (g.val 1 1 / g.val 1 0) : ℝ) =
      (modulus (m.val 1 1) : ℝ) / (modulus (m.val 1 0) : ℝ) := by
    rw [g10, g11, div_eq_mul_inv, modulus_mul, modulus_inv, modulus_mul, modulus_mul]
    push_cast
    field_simp
  by_cases hW : GL2LocalData.Wc χ σ μ lam c Φ g = 0
  · rw [hW, norm_zero]
    refine ⟨by positivity, fun h => absurd rfl h⟩
  obtain ⟨t, htN, hval⟩ := GlobalTheory.T.weil_whittaker_galois_invariance F E χ σ hσ μ lam c hc Φ g hg10 hW
  have hI0 : gaussI χ μ Φ (g.val 1 1 / g.val 1 0)
      (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, norm_zero, mul_zero] at hval
    exact hW (norm_eq_zero.1 hval)
  refine ⟨?_, fun _ => ?_⟩
  · rw [hval, mgdet, mg10, hxy]
    refine GlobalTheory.CompanionTheory.WhitOffBorel.real_bound (q := (modulus (m.val 1 1) : ℝ)) hXp hYp hδ₀ hpp hM0 (norm_nonneg _) (norm_nonneg _) ?_ ?_
    · have := hC₀ (g.val 1 1 / g.val 1 0) (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹)
      rwa [mκ] at this
    · have hpm : (modulus (m.val 1 0) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) :=
        le_max_left _ _
      have hqm : (modulus (m.val 1 1) : ℝ) ≤ max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) :=
        le_max_right _ _
      have hn1 : (modulus (-1 : F) : ℝ) ≤ 1 := by
        exact_mod_cast (modulus_le_one_iff (K := F)).2 (neg_mem (one_mem _))
      have t1 : (modulus (m.val 0 0 * m.val 1 1) : ℝ) ≤
          M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) := by
        rw [modulus_mul]; push_cast
        exact mul_le_mul (hent 0 0) hqm (NNReal.coe_nonneg _) hM0.le
      have t2 : (modulus (-(m.val 0 1 * m.val 1 0)) : ℝ) ≤
          M * max (modulus (m.val 1 0) : ℝ) (modulus (m.val 1 1) : ℝ) := by
        have e : -(m.val 0 1 * m.val 1 0) = (-1) * (m.val 0 1 * m.val 1 0) := by ring
        rw [e, modulus_mul, modulus_mul]; push_cast
        calc (modulus (-1 : F) : ℝ) * ((modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ))
            ≤ 1 * ((modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ)) :=
              mul_le_mul_of_nonneg_right hn1 (by positivity)
          _ = (modulus (m.val 0 1) : ℝ) * (modulus (m.val 1 0) : ℝ) := one_mul _
          _ ≤ _ := mul_le_mul (hent 0 1) hpm (NNReal.coe_nonneg _) hM0.le
      have hd : (m.val).det = m.val 0 0 * m.val 1 1 + -(m.val 0 1 * m.val 1 0) := by
        rw [Matrix.det_fin_two]; ring
      have hdd : (modulus (h₀.val).det : ℝ) = (modulus (m.val).det : ℝ) := by rw [hdet]
      rw [hdd, hd]
      exact (GlobalTheory.CompanionTheory.LFCoords.modulus_add_le_max _ _).trans (max_le t1 t2)
  · rw [hxy]
    have hs := hR _ _ hI0
    have mξ : (modulus (algebraMap F E ((g.val).det / g.val 1 0) * (t : E)⁻¹) : ℝ) =
        ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ) /
          ((modulus (y : F) : ℝ) * (modulus (m.val 1 0) : ℝ))) ^ 2 *
        ((modulus (x : F) : ℝ) * (modulus (y : F) : ℝ) * (modulus (h₀.val).det : ℝ))⁻¹ := by
      rw [modulus_mul, GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_algebraMap (K := F), modulus_inv,
        ← GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep.modulus_norm (K := F) (t : E), htN, div_eq_mul_inv,
        modulus_mul, modulus_inv]
      push_cast
      rw [mgdet, mg10, div_eq_mul_inv]
    rw [mξ, mκ] at hs
    exact GlobalTheory.CompanionTheory.WhitOffBorel.real_supp hXp hYp hδ₀ hpp (NNReal.coe_nonneg _) (hent 1 0) (hent 1 1) hs

end GlobalTheory.CompanionTheory.WhitOffBorel
