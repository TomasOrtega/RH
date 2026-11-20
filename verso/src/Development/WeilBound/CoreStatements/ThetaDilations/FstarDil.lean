import Development.WeilBound.CoreStatements.ThetaDilations.IntFou
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ThetaFunctionGrowthBoundStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

noncomputable section

namespace PositivityTheory.PlacePermOperatorBicommutantSpan

/- English proof (translation)
Set `L : (InfinitePlace F → ι → ℝ) →ₗ[ℝ] (InfinitePlace F → ι → ℝ)` to `LinearMap.pi fun w => (ρ w a • LinearMap.id) ∘ₗ LinearMap.proj w`. Establish `hdet : |LinearMap.det L| = |((Algebra.norm ℚ a : ℚ) : ℝ)| ^ (2 * M)`. Rewrite using `[LinearMap.det_pi, ← prod_rho hQ.1 hQ.2.2.2.2.1, Finset.abs_prod, ← Finset.prod_pow]`. Simplify using `[hQ.2.1]`. Establish `hn : (0 : ℝ) < |((Algebra.norm ℚ a : ℚ) : ℝ)|` using `abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 ha)`.

Establish `hd : LinearMap.det L ≠ 0` using `abs_pos.1 (by rw [hdet]; positivity)`. Establish `e : gauss B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = fun x => gauss B ρ P τ (L x)`. Use function extensionality and compare the values at `x`. Simplify using `only [gauss, L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply, LinearMap.id_apply, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← Complex.ofReal_pow, Complex.re_ofReal_mul, Complex.im_ofReal_mul]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hm` using `Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (InfinitePlace F → ι → ℝ)) hd`. Establish `e2 : ∫ x, gauss B ρ P τ (L x) = ∫ x, gauss B ρ P τ x ∂(Measure.map L volume)` using `(integral_map_equiv (L.equivOfDetNeZero hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv _).symm`.

Rewrite using `[cG, cG, e, e2, hm, integral_smul_measure, abs_inv, hdet, ENNReal.toReal_ofReal (by positivity), Complex.real_smul, ← pow_mul, mul_comm M 2, inv_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cG_dil {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι] {M : ℕ} {B : Matrix ι ι F}
    {ρ : InfinitePlace F → (F →+* ℝ)} {P : InfinitePlace F → Matrix ι ι ℝ} (hQ : QSetup M B ρ P) {a : F} (ha : a ≠ 0)
    (τ : InfinitePlace F → ℂ) : cG B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) =
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)|⁻¹ ^ M) ^ 2 : ℝ) * cG B ρ P τ := by
  let L : (InfinitePlace F → ι → ℝ) →ₗ[ℝ] (InfinitePlace F → ι → ℝ) :=
    LinearMap.pi fun w => (ρ w a • LinearMap.id) ∘ₗ LinearMap.proj w
  have hdet : |LinearMap.det L| = |((Algebra.norm ℚ a : ℚ) : ℝ)| ^ (2 * M) := by
    rw [LinearMap.det_pi, ← prod_rho hQ.1 hQ.2.2.2.2.1, Finset.abs_prod, ← Finset.prod_pow]
    simp [hQ.2.1]
  have hn : (0 : ℝ) < |((Algebra.norm ℚ a : ℚ) : ℝ)| := abs_pos.2 (by exact_mod_cast Algebra.norm_ne_zero_iff.2 ha)
  have hd : LinearMap.det L ≠ 0 := abs_pos.1 (by rw [hdet]; positivity)
  have e : gauss B ρ P (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = fun x => gauss B ρ P τ (L x) := by
    funext x
    simp only [gauss, L, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, LinearMap.smul_apply,
      LinearMap.id_apply, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, ← Complex.ofReal_pow,
      Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    push_cast
    ring
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (InfinitePlace F → ι → ℝ)) hd
  have e2 : ∫ x, gauss B ρ P τ (L x) = ∫ x, gauss B ρ P τ x ∂(Measure.map L volume) :=
    (integral_map_equiv (L.equivOfDetNeZero hd).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv _).symm
  rw [cG, cG, e, e2, hm, integral_smul_measure, abs_inv, hdet, ENNReal.toReal_ofReal (by positivity),
    Complex.real_smul, ← pow_mul, mul_comm M 2, inv_pow]
  ring

/- English proof (translation)
Use `H.1` as an intermediate fact. Use `H.2.2.2.2.2.2.2.2.2.1` as an intermediate fact. Set `e : (ι → R) ≃ᵐ (ι → R)` to `(Homeomorph.smul a).toMeasurableEquiv`. Establish `he : μ = ENNReal.ofReal m • μ.map e`. Use extensionality with `s hs`.

Rewrite using `[Measure.smul_apply, e.map_apply, smul_eq_mul, ← hμ _ (e.measurable hs)]`. Conclude with `congrArg μ (e.surjective.image_preimage s).symm`. Rewrite using `[fstar, fstar]`. Use `conv_rhs => rw [he]`. Rewrite using `[integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal hm, Complex.real_smul]`.

Use `congr 2`. Use function extensionality and compare the values at `u`. Use `show _ = opU ψ h B b φ ((a : R) • u)`. Simplify using `only [opU, opD, qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.ofReal_one, one_mul]`. Use `congr 2`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem fstar_dil {R : Type} [CommRing R] {ι : Type} [Fintype ι] [TopologicalSpace R] [MeasurableSpace R]
    {ψ : AddChar R ℂ} {h : R} {B : Matrix ι ι R} {μ : Measure (ι → R)} (H : NAQuad ψ h B μ) (a : Rˣ) {m : ℝ}
    (hm : 0 ≤ m) (hμ : ∀ s : Set (ι → R), MeasurableSet s → μ ((fun u => (a : R) • u) '' s) = ENNReal.ofReal m * μ s)
    (φ : (ι → R) → ℂ) (b : R) : m * fstar ψ h B μ (opD 1 (a : R) φ) ((a : R) ^ 2 * b) = fstar ψ h B μ φ b := by
  have := H.1
  have := H.2.2.2.2.2.2.2.2.2.1
  let e : (ι → R) ≃ᵐ (ι → R) := (Homeomorph.smul a).toMeasurableEquiv
  have he : μ = ENNReal.ofReal m • μ.map e := by
    ext s hs
    rw [Measure.smul_apply, e.map_apply, smul_eq_mul, ← hμ _ (e.measurable hs)]
    exact congrArg μ (e.surjective.image_preimage s).symm
  rw [fstar, fstar]
  conv_rhs => rw [he]
  rw [integral_smul_measure, integral_map_equiv, ENNReal.toReal_ofReal hm, Complex.real_smul]
  congr 2
  funext u
  show _ = opU ψ h B b φ ((a : R) • u)
  simp only [opU, opD, qf, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, Complex.ofReal_one, one_mul]
  congr 2
  ring

/- English proof (translation)
Introduce `F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ τ hτ`. Establish `H` using `GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1`. Establish `hD` using `H.2.2.2.2.2`. Establish `hsum : ∀ φ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Summable (eiTerm ψ lf B ρ P φ τ)`. Introduce `φ hφ τ hτ`.

Take `⟨w₀, hw₀⟩` from `Finite.exists_min fun w => (τ w).im`. Take `⟨_, s⟩` from `GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ _ (hτ w₀)`. Conclude with `(s τ hw₀).1.of_norm`. Use `⟨fun b => ?_, fun a ha => ?_, ?_, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[eis, eis, ← (Equiv.addLeft b).tsum_eq (eiTerm ψ lf B ρ P φ τ)]`.

Use `congr 1`. Simplify using `[opU, qf]`. Use `tsum_congr fun b' => ?_` and prove the remaining obligations. Simplify using `only [eiTerm, fstar, opU, Equiv.coe_addLeft, map_add, Complex.ofReal_add, add_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, add_mul, add_comm (algebraMap F (A F) b * _)]`. Rewrite using `[eis, eis, ← (Equiv.mulLeft₀ (a ^ 2) (pow_ne_zero 2 ha)).tsum_eq]`.

Use `congr 1`. Simplify using `[opD]`. Use `tsum_congr fun b' => ?_` and prove the remaining obligations. Establish `e` using `fstar_dil H (uA (Units.mk0 a ha)) (by positivity) (mod_rat hlf h1 hQ.2.1 B (Units.mk0 a ha)) φ (algebraMap F (A F) b')`. Establish `e2` using `cG_dil hQ ha fun w => τ w + (ρ w b' : ℝ)`.

Simplify using `only [eiTerm, Equiv.mulLeft₀_apply, map_mul, map_pow, Complex.ofReal_mul, Complex.ofReal_pow, ← mul_add]`. Rewrite using `[e2, ← e, mul_left_comm, ← mul_assoc]`. Both sides reduce to the same expression. Establish `hτ' : ∀ w, 0 < (-(τ w)⁻¹).im` using `fun w => by`. Rewrite using `[Complex.neg_im, Complex.inv_im, neg_div, neg_neg]`.

Conclude with `div_pos (hτ w) (Complex.normSq_pos.2 fun h0 => by simpa [h0] using hτ w)`. Establish `hF` using `(fou_sb hD hφ).1`. Establish `e1 : cG B ρ P τ * fou (chiB ψ (Bf B)) (muF B lf) φ 0 = eiTerm ψ lf B ρ P φ τ 0`. Simplify using `[eiTerm, fstar, opU, fou, chiB, mul_comm]`. Establish `e2 : cG B ρ P τ * eiTerm ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) 0 = φ 0`.

Use `(GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ τ hτ).2.2.1` as an intermediate fact. Simplify using `only [eiTerm, fstar, opU, map_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, Complex.ofReal_zero, add_zero, int_fou hD hφ]`. Rewrite using `[mul_left_comm, this, mul_one]`. Rewrite using `[eis, eis, (hsum _ hF _ hτ').tsum_eq_add_tsum_ite 0, (hsum _ hφ _ hτ).tsum_eq_add_tsum_ite 0, mul_add, mul_add, e1, e2, ← tsum_mul_left, add_left_comm, ← ((Equiv.inv F).trans (Equiv.neg F)).tsum_eq fun b => if b = 0 then 0 else eiTerm ψ lf B ρ P φ τ b]`. Use `congr 2`.

Use `tsum_congr fun b => ?_` and prove the remaining obligations. Distinguish the cases in `hb : b = 0`. Simplify using `[hb]`. Rewrite using `[if_neg hb, recip F lf hlf h1 ψ hψ ι M B ρ P hQ φ hφ τ hτ b hb]`. Conclude with `(if_neg (by simpa using hb)).symm`.

Simplify using `only [eis, eiTerm, fstar, opU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul, mul_assoc, tsum_mul_left, mul_add]`.
-/
theorem ei_inv : ∀ (F : Type) [Field F] [NumberField F] [MeasurableSpace (A F)] [BorelSpace (A F)] (lf : Measure (A F)), lf.IsAddHaarMeasure → lf (Oh F) = 1 → ∀ ψ : AddChar (A F) ℂ, IsStdChar F ψ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M : ℕ) (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ)) (P : InfinitePlace F → Matrix ι ι ℝ), QSetup M B ρ P → 3 ≤ M → ∀ φ : (ι → A F) → ℂ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → (∀ b : F, eis ψ lf B ρ P (opU ψ (hf F) (Bf B) (algebraMap F (A F) b) φ) (fun w => τ w + (ρ w b : ℝ)) = eis ψ lf B ρ P φ τ) ∧ (∀ a : F, a ≠ 0 → eis ψ lf B ρ P (opD 1 (algebraMap F (A F) a) φ) (fun w => ((ρ w a : ℝ) : ℂ) ^ 2 * τ w) = eis ψ lf B ρ P φ τ) ∧ (cG B ρ P τ * eis ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) = eis ψ lf B ρ P φ τ) ∧ ∀ c : ℂ, eis ψ lf B ρ P (c • φ) τ = c * eis ψ lf B ρ P φ τ := by
  intro F _ _ _ _ lf hlf h1 ψ hψ ι _ _ M B ρ P hQ hM φ hφ τ hτ
  have H := GlobalTheory.T.weil_representation_quadratic_datum F lf hlf h1 ψ hψ ι B hQ.2.2.1 hQ.2.2.2.1
  have hD := H.2.2.2.2.2
  have hsum : ∀ φ, SB φ → ∀ τ : InfinitePlace F → ℂ, (∀ w, 0 < (τ w).im) → Summable (eiTerm ψ lf B ρ P φ τ) := by
    intro φ hφ τ hτ
    obtain ⟨w₀, hw₀⟩ := Finite.exists_min fun w => (τ w).im
    obtain ⟨_, s⟩ := GlobalTheory.T.summable_norm_eiTerm_and_wt_mul_tsum_le F lf hlf h1 ψ hψ ι M B ρ P hQ hM φ hφ _ (hτ w₀)
    exact (s τ hw₀).1.of_norm
  refine ⟨fun b => ?_, fun a ha => ?_, ?_, fun c => ?_⟩
  · rw [eis, eis, ← (Equiv.addLeft b).tsum_eq (eiTerm ψ lf B ρ P φ τ)]
    congr 1
    · simp [opU, qf]
    · refine tsum_congr fun b' => ?_
      simp only [eiTerm, fstar, opU, Equiv.coe_addLeft, map_add, Complex.ofReal_add, add_assoc, ← mul_assoc,
        ← AddChar.map_add_eq_mul, add_mul, add_comm (algebraMap F (A F) b * _)]
  · rw [eis, eis, ← (Equiv.mulLeft₀ (a ^ 2) (pow_ne_zero 2 ha)).tsum_eq]
    congr 1
    · simp [opD]
    · refine tsum_congr fun b' => ?_
      have e := fstar_dil H (uA (Units.mk0 a ha)) (by positivity) (mod_rat hlf h1 hQ.2.1 B (Units.mk0 a ha)) φ
        (algebraMap F (A F) b')
      have e2 := cG_dil hQ ha fun w => τ w + (ρ w b' : ℝ)
      simp only [eiTerm, Equiv.mulLeft₀_apply, map_mul, map_pow, Complex.ofReal_mul, Complex.ofReal_pow, ← mul_add]
      rw [e2, ← e, mul_left_comm, ← mul_assoc]
      rfl
  · have hτ' : ∀ w, 0 < (-(τ w)⁻¹).im := fun w => by
      rw [Complex.neg_im, Complex.inv_im, neg_div, neg_neg]
      exact div_pos (hτ w) (Complex.normSq_pos.2 fun h0 => by simpa [h0] using hτ w)
    classical
    have hF := (fou_sb hD hφ).1
    have e1 : cG B ρ P τ * fou (chiB ψ (Bf B)) (muF B lf) φ 0 = eiTerm ψ lf B ρ P φ τ 0 := by
      simp [eiTerm, fstar, opU, fou, chiB, mul_comm]
    have e2 : cG B ρ P τ * eiTerm ψ lf B ρ P (fou (chiB ψ (Bf B)) (muF B lf) φ) (fun w => -(τ w)⁻¹) 0 = φ 0 := by
      have := (GlobalTheory.T.archimedean_gaussian_fourier F ι M B ρ P hQ τ hτ).2.2.1
      simp only [eiTerm, fstar, opU, map_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, Complex.ofReal_zero, add_zero,
        int_fou hD hφ]
      rw [mul_left_comm, this, mul_one]
    rw [eis, eis, (hsum _ hF _ hτ').tsum_eq_add_tsum_ite 0, (hsum _ hφ _ hτ).tsum_eq_add_tsum_ite 0, mul_add, mul_add,
      e1, e2, ← tsum_mul_left, add_left_comm, ← ((Equiv.inv F).trans (Equiv.neg F)).tsum_eq
        fun b => if b = 0 then 0 else eiTerm ψ lf B ρ P φ τ b]
    congr 2
    refine tsum_congr fun b => ?_
    by_cases hb : b = 0
    · simp [hb]
    · rw [if_neg hb, recip F lf hlf h1 ψ hψ ι M B ρ P hQ φ hφ τ hτ b hb]
      exact (if_neg (by simpa using hb)).symm
  · simp only [eis, eiTerm, fstar, opU, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c, integral_const_mul, mul_assoc,
      tsum_mul_left, mul_add]

end PositivityTheory.PlacePermOperatorBicommutantSpan
