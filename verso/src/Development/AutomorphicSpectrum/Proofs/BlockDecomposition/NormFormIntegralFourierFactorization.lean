import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnstatedLocalWeilLemma

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSquare

open GlobalTheory.CompanionTheory.WeilSB

section Main

variable {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]
  [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E]
  [ValuativeExtension F E] [FiniteDimensional F E] [Algebra.IsSeparable F E]
  [Fact (Module.finrank F E = 2)]

/- English proof (translation)
Establish `ha : (a : F) ≠ 0` using `a.ne_zero`. Establish `h1 : Algebra.trace F E (conj F E u * z) = Algebra.trace F E (u * conj F E z)`. Rewrite using `[← trace_conj (K := F) (conj F E u * z), map_mul, conj_conj]`. Establish `h2 : u * conj F E (algebraMap F E ((a : F)⁻¹) * z) = algebraMap F E ((a : F)⁻¹) * (u * conj F E z)`. Rewrite using `[map_mul, conj_algebraMap]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[norm_add (K := F) u, h2, trace_algebraMap_mul, h1, map_mul (Algebra.norm F), norm_algebraMap_eq_sq]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem square_identity (a : Fˣ) (u z : E) :
    (a : F) * Algebra.norm F u + Algebra.trace F E (conj F E u * z) =
      (a : F) * Algebra.norm F (u + algebraMap F E ((a : F)⁻¹) * z) + -(Algebra.norm F z) / a := by
  have ha : (a : F) ≠ 0 := a.ne_zero
  have h1 : Algebra.trace F E (conj F E u * z) = Algebra.trace F E (u * conj F E z) := by
    rw [← trace_conj (K := F) (conj F E u * z), map_mul, conj_conj]
  have h2 : u * conj F E (algebraMap F E ((a : F)⁻¹) * z) =
      algebraMap F E ((a : F)⁻¹) * (u * conj F E z) := by
    rw [map_mul, conj_algebraMap]
    ring
  rw [norm_add (K := F) u, h2, trace_algebraMap_mul, h1, map_mul (Algebra.norm F), norm_algebraMap_eq_sq]
  field_simp
  ring

/- English proof (translation)
Establish `e : (valBall E n : Set E).indicator (fun u => G (u + w)) = fun u => (valBall E n : Set E).indicator G (u + w)`. Use function extensionality and compare the values at `u`. Distinguish the cases in `hu : u ∈ valBall E n`. Establish `hu' : u + w ∈ valBall E n` using `add_mem hu hw`. Rewrite using `[Set.indicator_of_mem (show u ∈ (valBall E n : Set E) from hu), Set.indicator_of_mem (show u + w ∈ (valBall E n : Set E) from hu')]`.

Establish `hu' : u + w ∉ valBall E n` using `fun h => hu (by simpa using sub_mem h hw)`. Rewrite using `[Set.indicator_of_notMem (show u ∉ (valBall E n : Set E) from hu), Set.indicator_of_notMem (show u + w ∉ (valBall E n : Set E) from hu')]`. Rewrite using `[← integral_indicator (measurableSet_valBall n), ← integral_indicator (measurableSet_valBall n), e]`. Conclude with `integral_add_right_eq_self _ w`.
-/
theorem setIntegral_ball_add (μ : Measure E) [μ.IsAddHaarMeasure] (G : E → ℂ) {n : ℤ} {w : E}
    (hw : w ∈ valBall E n) :
    ∫ u in (valBall E n : Set E), G (u + w) ∂μ = ∫ u in (valBall E n : Set E), G u ∂μ := by
  have e : (valBall E n : Set E).indicator (fun u => G (u + w)) =
      fun u => (valBall E n : Set E).indicator G (u + w) := by
    funext u
    by_cases hu : u ∈ valBall E n
    · have hu' : u + w ∈ valBall E n := add_mem hu hw
      rw [Set.indicator_of_mem (show u ∈ (valBall E n : Set E) from hu),
        Set.indicator_of_mem (show u + w ∈ (valBall E n : Set E) from hu')]
    · have hu' : u + w ∉ valBall E n := fun h => hu (by simpa using sub_mem h hw)
      rw [Set.indicator_of_notMem (show u ∉ (valBall E n : Set E) from hu),
        Set.indicator_of_notMem (show u + w ∉ (valBall E n : Set E) from hu')]
  rw [← integral_indicator (measurableSet_valBall n), ← integral_indicator (measurableSet_valBall n), e]
  exact integral_add_right_eq_self _ w

/- English proof (translation)
Establish `hN` using `continuous_norm_of (F := F) (E := E) hcont`. Establish `hψ : Continuous (chE E χ)` using `continuous_traceChar hχ hχ1`. Establish `hψ1 : chE E χ ≠ 1` using `traceChar_ne_one hχ hχ1`. Establish `hΦs : Φ ∈ schwartzBruhat E` using `⟨hΦ.1, hΦ.2⟩`. Establish `hFT : ∀ u, FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u)`.

Introduce `u`. Unfold `FTs localFourier`. Use `integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Use `show Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ) = Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)`. Rewrite using `[mul_comm (conj F E u) z]`.

Take `⟨-, M₁, -, hM₁⟩` from `exists_invariant_of_mem_schwartzBruhat (localFourier_mem_schwartzBruhat μ hψ hψ1 hΦs)`. Take `⟨-, M₂, -, hM₂⟩` from `exists_invariant_of_mem_schwartzBruhat hΦs`. Establish `ha0 : algebraMap F E ((a : F)⁻¹) ≠ 0` using `(map_ne_zero _).2 (inv_ne_zero a.ne_zero)`. Establish `hai : algebraMap F E ((a : F)⁻¹) ∈ valBall E (ord (algebraMap F E ((a : F)⁻¹)))` using `(mem_valBall_iff_le_ord ha0).2 le_rfl`. Use `⟨min M₁ (ord (algebraMap F E ((a : F)⁻¹)) + M₂), fun n hn => ?_⟩` and prove the remaining obligations.

Establish `hn₁ : n ≤ M₁` using `hn.trans (min_le_left _ _)`. Establish `hn₂ : n ≤ ord (algebraMap F E ((a : F)⁻¹)) + M₂` using `hn.trans (min_le_right _ _)`. Establish `hfin : IsFiniteMeasure (μ.restrict (valBall E n : Set E))` using `⟨by`. Rewrite using `[Measure.restrict_apply_univ]`. Conclude with `(isCompact_valBall n).measure_lt_top⟩`.

Use `set G : E → ℂ := fun u => (χ ((a : F) * Algebra.norm F u) : ℂ) with hG`. Use `set K : E → E → ℂ := fun u z => G u * (Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)) with hK`. Establish `hint : Integrable (Function.uncurry K) ((μ.restrict (valBall E n : Set E)).prod μ)`. Establish `hΦi : Integrable Φ μ` using `integrable_of_mem_schwartzBruhat μ hΦs`. Establish `hp` using `(integrable_const (μ := μ.restrict (valBall E n : Set E)) (1 : ℂ)).mul_prod hΦi`.

Establish `hc : Continuous fun p : E × E => (χ ((a : F) * Algebra.norm F p.1) : ℂ) * (chE E χ (conj F E p.1 * p.2) : ℂ)` using `((continuous_subtype_val.comp hχ).comp (continuous_const.mul (hN.comp continuous_fst))).mul ((continuous_subtype_val.comp hψ).comp ((continuous_conj.comp continuous_fst).mul continuous_snd))`. Establish `hb` using `hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by`. Rewrite using `[norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul])`. Use `hb.congr (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `show _ = G p.1 * (Φ p.2 * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ))`.

Use `show (χ ((a : F) * Algebra.norm F p.1) : ℂ) * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ) * (1 * Φ p.2) = _`. Simplify using `only [hG]`. Expand and normalize the polynomial expressions, which then agree. Establish `hinner : ∀ z, ∫ u in (valBall E n : Set E), K u z ∂μ = (∫ u in (valBall E n : Set E), G u ∂μ) * ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z)`. Introduce `z`.

Distinguish the cases in `hz : Φ z = 0`. Simplify using `[hK, hz]`. Establish `hw : algebraMap F E ((a : F)⁻¹) * z ∈ valBall E n` using `valBall_antitone hn₂ (mul_mem_valBall hai (hM₂ z hz))`. Establish `e : ∀ u, K u z = ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) * G (u + algebraMap F E ((a : F)⁻¹) * z)`. Introduce `u`.

Establish `h` using `congrArg (fun t => (χ t : ℂ)) (square_identity a u z)`. Simplify using `only [AddChar.map_add_eq_mul, Circle.coe_mul] at h`. Simplify using `only [hK, hG]`. Take the linear combination `Φ z * h`. Simplify using `only [e]`.

Rewrite using `[integral_const_mul, setIntegral_ball_add μ G hw]`. Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm` and prove the remaining obligations. Establish `: localFourier μ (chE E χ) Φ (conj F E u) = 0`.

Assume the negation of the conclusion as `h`. Conclude with `hu (conj_mem_valBall_iff.1 (valBall_antitone hn₁ (hM₁ _ h)))`. Rewrite using `[hFT, this, mul_zero]`. Use `_ = ∫ u in (valBall E n : Set E), ∫ z, K u z ∂μ ∂μ := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations.

Use `show G u * FTs χ (conj F E) μ Φ u = ∫ z, K u z ∂μ`. Simplify using `only [hK]`. Rewrite using `[integral_const_mul]`. Both sides reduce to the same expression. Use `_ = ∫ z, ∫ u in (valBall E n : Set E), K u z ∂μ ∂μ := integral_integral_swap hint`.

Use `_ = _ := by`. Simplify using `only [hinner]`. Rewrite using `[integral_const_mul]`.
-/
theorem core_of_haar {χ : AddChar F Circle} (hχ : Continuous χ) (hχ1 : χ ≠ 1)
    (hcont : Continuous (algebraMap F E)) (μ : Measure E) [μ.IsAddHaarMeasure] (a : Fˣ)
    {Φ : E → ℂ} (hΦ : Φ ∈ SBE E) :
    ∃ n₀ : ℤ, ∀ n ≤ n₀,
      ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTs χ (conj F E) μ Φ u ∂μ =
        (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂μ) *
          ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂μ := by
  have hN := continuous_norm_of (F := F) (E := E) hcont
  have hψ : Continuous (chE E χ) := continuous_traceChar hχ hχ1
  have hψ1 : chE E χ ≠ 1 := traceChar_ne_one hχ hχ1
  have hΦs : Φ ∈ schwartzBruhat E := ⟨hΦ.1, hΦ.2⟩
  have hFT : ∀ u, FTs χ (conj F E) μ Φ u = localFourier μ (chE E χ) Φ (conj F E u) := by
    intro u
    unfold FTs localFourier
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ) =
      Φ z * (χ (Algebra.trace F E (z * conj F E u)) : ℂ)
    rw [mul_comm (conj F E u) z]
  obtain ⟨-, M₁, -, hM₁⟩ := exists_invariant_of_mem_schwartzBruhat
    (localFourier_mem_schwartzBruhat μ hψ hψ1 hΦs)
  obtain ⟨-, M₂, -, hM₂⟩ := exists_invariant_of_mem_schwartzBruhat hΦs
  have ha0 : algebraMap F E ((a : F)⁻¹) ≠ 0 := (map_ne_zero _).2 (inv_ne_zero a.ne_zero)
  have hai : algebraMap F E ((a : F)⁻¹) ∈ valBall E (ord (algebraMap F E ((a : F)⁻¹))) :=
    (mem_valBall_iff_le_ord ha0).2 le_rfl
  refine ⟨min M₁ (ord (algebraMap F E ((a : F)⁻¹)) + M₂), fun n hn => ?_⟩
  have hn₁ : n ≤ M₁ := hn.trans (min_le_left _ _)
  have hn₂ : n ≤ ord (algebraMap F E ((a : F)⁻¹)) + M₂ := hn.trans (min_le_right _ _)
  have hfin : IsFiniteMeasure (μ.restrict (valBall E n : Set E)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (isCompact_valBall n).measure_lt_top⟩
  set G : E → ℂ := fun u => (χ ((a : F) * Algebra.norm F u) : ℂ) with hG
  set K : E → E → ℂ := fun u z => G u * (Φ z * (χ (Algebra.trace F E (conj F E u * z)) : ℂ)) with hK
  have hint : Integrable (Function.uncurry K) ((μ.restrict (valBall E n : Set E)).prod μ) := by
    have hΦi : Integrable Φ μ := integrable_of_mem_schwartzBruhat μ hΦs
    have hp := (integrable_const (μ := μ.restrict (valBall E n : Set E)) (1 : ℂ)).mul_prod hΦi
    have hc : Continuous fun p : E × E => (χ ((a : F) * Algebra.norm F p.1) : ℂ) *
        (chE E χ (conj F E p.1 * p.2) : ℂ) :=
      ((continuous_subtype_val.comp hχ).comp (continuous_const.mul (hN.comp continuous_fst))).mul
        ((continuous_subtype_val.comp hψ).comp
          ((continuous_conj.comp continuous_fst).mul continuous_snd))
    have hb := hp.bdd_mul (c := 1) hc.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      rw [norm_mul, Circle.norm_coe, Circle.norm_coe, one_mul])
    refine hb.congr (Filter.Eventually.of_forall fun p => ?_)
    show _ = G p.1 * (Φ p.2 * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ))
    show (χ ((a : F) * Algebra.norm F p.1) : ℂ) * (χ (Algebra.trace F E (conj F E p.1 * p.2)) : ℂ) *
      (1 * Φ p.2) = _
    simp only [hG]
    ring
  have hinner : ∀ z, ∫ u in (valBall E n : Set E), K u z ∂μ =
      (∫ u in (valBall E n : Set E), G u ∂μ) * ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) := by
    intro z
    by_cases hz : Φ z = 0
    · simp [hK, hz]
    have hw : algebraMap F E ((a : F)⁻¹) * z ∈ valBall E n :=
      valBall_antitone hn₂ (mul_mem_valBall hai (hM₂ z hz))
    have e : ∀ u, K u z = ((χ (-(Algebra.norm F z) / a) : ℂ) * Φ z) *
        G (u + algebraMap F E ((a : F)⁻¹) * z) := by
      intro u
      have h := congrArg (fun t => (χ t : ℂ)) (square_identity a u z)
      simp only [AddChar.map_add_eq_mul, Circle.coe_mul] at h
      simp only [hK, hG]
      linear_combination Φ z * h
    simp only [e]
    rw [integral_const_mul, setIntegral_ball_add μ G hw]
    ring
  calc ∫ u, G u * FTs χ (conj F E) μ Φ u ∂μ
      = ∫ u in (valBall E n : Set E), G u * FTs χ (conj F E) μ Φ u ∂μ := by
        refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => ?_).symm
        have : localFourier μ (chE E χ) Φ (conj F E u) = 0 := by
          by_contra h
          exact hu (conj_mem_valBall_iff.1 (valBall_antitone hn₁ (hM₁ _ h)))
        rw [hFT, this, mul_zero]
    _ = ∫ u in (valBall E n : Set E), ∫ z, K u z ∂μ ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show G u * FTs χ (conj F E) μ Φ u = ∫ z, K u z ∂μ
        simp only [hK]
        rw [integral_const_mul]
        rfl
    _ = ∫ z, ∫ u in (valBall E n : Set E), K u z ∂μ ∂μ := integral_integral_swap hint
    _ = _ := by
        simp only [hinner]
        rw [integral_const_mul]

end Main

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a Φ hΦ`. Use `haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)`. Use `haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont`. Use `haveI : Algebra.IsSeparable F E := inferInstance`.

Establish `hσc : σ = conj F E` using `(eq_one_or_eq_conj σ).resolve_left hσ`. Substitute `hσc` using the available equality. Conclude with `core_of_haar hχ hχ1 hcont (muE E χ) a hΦ`.
-/
theorem gauss_core : ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), ∀ Φ ∈ SBE E, ∃ n₀ : ℤ, ∀ n ≤ n₀,
  ∫ u, (χ ((a : F) * Algebra.norm F u) : ℂ) * FTE E χ σ Φ u ∂muE E χ =
    (∫ u in (valBall E n : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ) *
      ∫ z, (χ (-(Algebra.norm F z) / a) : ℂ) * Φ z ∂muE E χ := by
  intro F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hfr hcont σ hσ η hη a Φ hΦ
  haveI : Fact (Module.finrank F E = 2) := ⟨hfr⟩
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  haveI : ValuativeExtension F E := valuativeExtension_of_continuous hcont
  haveI : Algebra.IsSeparable F E := inferInstance
  have hσc : σ = conj F E := (eq_one_or_eq_conj σ).resolve_left hσ
  subst hσc
  exact core_of_haar hχ hχ1 hcont (muE E χ) a hΦ

end GlobalTheory.CompanionTheory.WeilSquare
