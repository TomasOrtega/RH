import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.MatNDHHolds

noncomputable section

namespace PI.AprimeInfW.GenericDensity

open scoped RealInnerProductSpace FourierTransform
open MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {V W ι : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [MeasurableSpace V]
  [BorelSpace V] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W]
  [BorelSpace W] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y` using `fun r x y => map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x`. Establish `sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y` using `fun r x y => map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y`. Set `A : W →ₗ[ℝ] W` to `{ toFun := fun y => ∑ i, β (b i) y • b i map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib] map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }`. Establish `hA : ∀ x y, β x y = ⟪x, A y⟫`. Introduce `x y`.

Establish `h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y` using `by conv_lhs => rw [← b.sum_repr' x]`. Express the relevant statement in the definitionally equal form `(AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _`. Rewrite using `[map_sum]`. Simplify using `[sL]`. Establish `h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫`.

Simplify using `[A, inner_sum, inner_smul_right]`. Rewrite using `[h1, h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[real_inner_comm, mul_comm]`. Use `⟨A, hA, ?_⟩` and prove the remaining obligations.

Rewrite using `[← LinearMap.det_toMatrix b.toBasis]`. Use `congr 1`. Use extensionality with `i j`. Rewrite using `[LinearMap.toMatrix_apply, Matrix.of_apply, hA]`. Simplify using `[OrthonormalBasis.repr_apply_apply]`.
-/
private theorem exists_linearMap_inner_eq_and_det_eq_gram_det (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (b : OrthonormalBasis ι ℝ W) :
    ∃ A : W →ₗ[ℝ] W, (∀ x y, β x y = ⟪x, A y⟫) ∧
      LinearMap.det A = (Matrix.of fun i j => β (b i) (b j)).det := by
  have sL : ∀ (r : ℝ) x y, β (r • x) y = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (hcL y) r x
  have sR : ∀ (r : ℝ) x y, β x (r • y) = r * β x y := fun r x y =>
    map_real_smul (AddMonoidHom.mk' (fun y => β x y) (fun y y' => hR x y y')) (hcR x) r y
  let A : W →ₗ[ℝ] W :=
    { toFun := fun y => ∑ i, β (b i) y • b i
      map_add' := fun y y' => by simp only [hR, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r y => by simp only [sR, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hA : ∀ x y, β x y = ⟪x, A y⟫ := by
    intro x y
    have h1 : β x y = ∑ i, ⟪b i, x⟫ * β (b i) y := by
      conv_lhs => rw [← b.sum_repr' x]
      change (AddMonoidHom.mk' (fun x => β x y) (fun x x' => hL x x' y)) (∑ i, ⟪b i, x⟫ • b i) = _
      rw [map_sum]
      simp [sL]
    have h2 : ⟪x, A y⟫ = ∑ i, β (b i) y * ⟪x, b i⟫ := by
      simp [A, inner_sum, inner_smul_right]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm, mul_comm]
  refine ⟨A, hA, ?_⟩
  rw [← LinearMap.det_toMatrix b.toBasis]
  congr 1
  ext i j
  rw [LinearMap.toMatrix_apply, Matrix.of_apply, hA]
  simp [OrthonormalBasis.repr_apply_apply]

/- English proof (translation)
Establish `hme : MeasurableEmbedding e` using `e.measurableEmbedding`. Establish `hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ` using `fun g => hme.integral_map g`. Establish `hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ)` using `fun x y => by`. Simplify using `using hχ (e x) (e y)`. Use `set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef`.

Establish `hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y)`. Introduce `y`. Simplify using `only [hFdef, hmap, Function.comp_apply, hχ']`. Establish `hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ`. Simplify using `only [hF]`.

Conclude with `hme.integrable_map_iff.mp hint`. Establish `key` using `hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)`. Establish `hneg : e (-(e.symm z)) = -z`. Use `map_neg (AddMonoidHom.mk' e he) (e.symm z)` as an intermediate fact. Simplify using `using this`.

Simplify using `only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key`. Rewrite using `[hmap]`. Simplify using `only [hFdef, hmap]`. Conclude with `key`.
-/
private theorem integral_fourier_map_eq_neg_of_integrable (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (Φ : W → ℂ) (hΦc : Continuous Φ) (hΦs : HasCompactSupport Φ)
    (hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) (μ.map e))
    (z : W) :
    ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e)) * ((𝐞 (β y z) : Circle) : ℂ) ∂(μ.map e)
      = Φ (-z) := by
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hmap : ∀ g : W → ℂ, ∫ w, g w ∂(μ.map e) = ∫ x, g (e x) ∂μ := fun g => hme.integral_map g
  have hχ' : ∀ x y, χ x y = ((𝐞 (β (e x) (e y)) : Circle) : ℂ) := fun x y => by
    simpa using hχ (e x) (e y)
  set F := fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂(μ.map e) with hFdef
  have hF : ∀ y, ∫ x, (Φ ∘ e) x * χ x y ∂μ = F (e y) := by
    intro y
    simp only [hFdef, hmap, Function.comp_apply, hχ']
  have hint' : Integrable (fun y => ∫ x, (Φ ∘ e) x * χ x y ∂μ) μ := by
    simp only [hF]
    exact hme.integrable_map_iff.mp hint
  have key := hμ.2 (Φ ∘ e) (hΦc.comp e.continuous) (hΦs.comp_homeomorph e) hint' (e.symm z)
  have hneg : e (-(e.symm z)) = -z := by
    have := map_neg (AddMonoidHom.mk' e he) (e.symm z)
    simpa using this
  simp only [hF, hχ', Homeomorph.apply_symm_apply, Function.comp_apply, hneg] at key
  rw [hmap]
  simp only [hFdef, hmap]
  exact key

/- English proof (translation)
Establish `hkpos : 0 < ‖k‖` using `norm_pos_iff.mpr hk`. Set `bump : ContDiffBump (0 : W)` to `⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩`. Set `ψ : W → ℂ` to `fun x => ((bump x : ℝ) : ℂ)`. Establish `hψc : Continuous ψ` using `Complex.continuous_ofReal.comp bump.continuous`. Establish `hψs : HasCompactSupport ψ` using `bump.hasCompactSupport.comp_left Complex.ofReal_zero`.

Establish `hψs' : HasCompactSupport (fun x => ψ (x + k))` using `hψs.comp_homeomorph (Homeomorph.addRight k)`. Set `Φ : W → ℂ` to `fun x => ψ x - ψ (x + k)`. Establish `hΦc : Continuous Φ` using `hψc.sub (hψc.comp (continuous_add_right k))`. Establish `hΦs : HasCompactSupport Φ` using `hψs.sub hψs'`. Establish `hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0`.

Introduce `y`. Set `g : W → ℂ` to `fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)`. Establish `hgc : Continuous g`. Use `hcL y` as an intermediate fact. Use `fun_prop`.

Establish `hg : Integrable g ν` using `hgc.integrable_of_hasCompactSupport hψs.mul_right`. Establish `heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k)`. Use function extensionality and compare the values at `x`. Simplify using `only [Φ, g, hL, hk0, add_zero]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]`. Establish `hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν`. Simplify using `only [hzero]`. Conclude with `integrable_zero _ _ _`. Establish `key` using `hP Φ hΦc hΦs hint 0`.

Simplify using `only [hzero, zero_mul, integral_zero, neg_zero] at key`. Establish `h0 : bump 0 = 1` using `bump.one_of_mem_closedBall (by simp; positivity)`. Establish `h1 : bump k = 0`. Apply `Function.notMem_support.mp` to reduce the goal to its premises. Rewrite using `[bump.support_eq]`.

Simplify using the standard rewrite rules. Conclude with `le_rfl`. Simplify using `[Φ, ψ, h0, h1] at key`.
-/
private theorem false_of_degenerate_of_fourier_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (β : W → W → ℝ)
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hcL : ∀ y, Continuous fun x => β x y)
    (k : W) (hk : k ≠ 0) (hk0 : ∀ y, β k y = 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) * ((𝐞 (β y z) : Circle) : ℂ) ∂ν = Φ (-z)) :
    False := by
  have hkpos : 0 < ‖k‖ := norm_pos_iff.mpr hk
  let bump : ContDiffBump (0 : W) := ⟨‖k‖ / 2, ‖k‖, by positivity, by linarith⟩
  let ψ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hψc : Continuous ψ := Complex.continuous_ofReal.comp bump.continuous
  have hψs : HasCompactSupport ψ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hψs' : HasCompactSupport (fun x => ψ (x + k)) := hψs.comp_homeomorph (Homeomorph.addRight k)
  let Φ : W → ℂ := fun x => ψ x - ψ (x + k)
  have hΦc : Continuous Φ := hψc.sub (hψc.comp (continuous_add_right k))
  have hΦs : HasCompactSupport Φ := hψs.sub hψs'
  have hzero : ∀ y, ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν = 0 := by
    intro y
    let g : W → ℂ := fun x => ψ x * ((𝐞 (β x y) : Circle) : ℂ)
    have hgc : Continuous g := by
      have := hcL y
      fun_prop
    have hg : Integrable g ν := hgc.integrable_of_hasCompactSupport hψs.mul_right
    have heq : (fun x => Φ x * ((𝐞 (β x y) : Circle) : ℂ)) = fun x => g x - g (x + k) := by
      funext x
      simp only [Φ, g, hL, hk0, add_zero]
      ring
    rw [heq, integral_sub hg (hg.comp_add_right k), integral_add_right_eq_self, sub_self]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 (β x y) : Circle) : ℂ) ∂ν) ν := by
    simp only [hzero]
    exact integrable_zero _ _ _
  have key := hP Φ hΦc hΦs hint 0
  simp only [hzero, zero_mul, integral_zero, neg_zero] at key
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; positivity)
  have h1 : bump k = 0 := by
    apply Function.notMem_support.mp
    rw [bump.support_eq]
    simp
    exact le_rfl
  simp [Φ, ψ, h0, h1] at key

/- English proof (translation)
Use `set s := ν.addHaarScalarFactor volume with hsdef`. Establish `hs : 0 < s` using `Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume`. Establish `hν : ν = (s : ENNReal) • volume`. Rewrite using `[← ENNReal.smul_def]`. Conclude with `Measure.isAddLeftInvariant_eq_smul ν volume`.

Set `bump : ContDiffBump (0 : W)` to `⟨1, 2, one_pos, one_lt_two⟩`. Establish `h0 : bump 0 = 1` using `bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)`. Set `Φ : W → ℂ` to `fun x => ((bump x : ℝ) : ℂ)`. Establish `hΦs : HasCompactSupport Φ` using `bump.hasCompactSupport.comp_left Complex.ofReal_zero`. Establish `hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ` using `Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))`.

Set `S : SchwartzMap W ℂ` to `hΦs.toSchwartzMap hΦd`. Establish `hSΦ : (S : W → ℂ) = Φ` using `rfl`. Set `g : W → ℂ` to `𝓕⁻ Φ`. Establish `hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ)` using `by rw [SchwartzMap.fourierInv_coe, hSΦ]`. Establish `hgi : Integrable g` using `by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable`.

Establish `hgg : ∫ v, g v = 1`. Establish `h1 : 𝓕⁻ g 0 = ∫ v, g v` using `by simp [Real.fourierInv_eq]`. Establish `h2 : 𝓕⁻ g 0 = Φ 0`. Rewrite using `[Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe, FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]`. Rewrite using `[← h1, h2]`.

Simplify using `[Φ, h0]`. Establish `hAc : Continuous A` using `A.continuous_of_finiteDimensional`. Establish `hAm : AEMeasurable A volume` using `hAc.measurable.aemeasurable`. Establish `hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume` using `Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet`. Establish `hgim : Integrable g ((volume : Measure W).map A)`.

Rewrite using `[hmapA]`. Conclude with `hgi.smul_measure ENNReal.ofReal_ne_top`. Establish `hgA : Integrable (fun y => g (A y)) volume` using `(integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim`. Establish `hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y)`. Introduce `y`.

Use `show _ = (s : ℝ) • 𝓕⁻ Φ (A y)`. Rewrite using `[hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Rewrite using `[Circle.smul_def, smul_eq_mul, mul_comm]`. Establish `hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν`. Simplify using `only [hinner]`. Rewrite using `[hν]`. Conclude with `(hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top`.

Establish `hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ)`. Rewrite using `[← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]`. Establish `key` using `hP Φ hΦd.continuous hΦs hint 0`. Simplify using `only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key`. Rewrite `key` using `[hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal, ENNReal.toReal_ofReal (abs_nonneg _)]`.

Establish `hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1`. Establish `h2 : Φ (-0) = 1` using `by simp [Φ, h0]`. Rewrite `key` using `[h2]`. Use `congrArg Complex.re key` as an intermediate fact. Simplify using `only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this`.

Conclude with `this`. Establish `hdpos : 0 < |LinearMap.det A|` using `abs_pos.mpr hdet`. Establish `hsq : (s : ℝ) ^ 2 = |LinearMap.det A|`. Rewrite `hreal` using `[abs_inv]`. Clear denominators, using `at hreal` for the nonvanishing conditions.

Use polynomial arithmetic with `[hreal]`. Rewrite using `[hν]`. Use `congr 1`. Rewrite using `[← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]`.
-/
private theorem measure_eq_sqrt_abs_det_smul_volume_of_inversion (ν : Measure W) [ν.IsAddHaarMeasure] (A : W →ₗ[ℝ] W)
    (hdet : LinearMap.det A ≠ 0)
    (hP : ∀ Φ : W → ℂ, Continuous Φ → HasCompactSupport Φ →
      Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν → ∀ z : W,
      ∫ y, (∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) * ((𝐞 ⟪A y, z⟫ : Circle) : ℂ) ∂ν = Φ (-z)) :
    ν = ENNReal.ofReal (Real.sqrt |LinearMap.det A|) • volume := by
  set s := ν.addHaarScalarFactor volume with hsdef
  have hs : 0 < s := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure ν volume
  have hν : ν = (s : ENNReal) • volume := by
    rw [← ENNReal.smul_def]
    exact Measure.isAddLeftInvariant_eq_smul ν volume
  let bump : ContDiffBump (0 : W) := ⟨1, 2, one_pos, one_lt_two⟩
  have h0 : bump 0 = 1 := bump.one_of_mem_closedBall (by simp; exact bump.rIn_pos.le)
  let Φ : W → ℂ := fun x => ((bump x : ℝ) : ℂ)
  have hΦs : HasCompactSupport Φ := bump.hasCompactSupport.comp_left Complex.ofReal_zero
  have hΦd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ :=
    Complex.ofRealCLM.contDiff.comp (bump.contDiff (n := ⊤))
  let S : SchwartzMap W ℂ := hΦs.toSchwartzMap hΦd
  have hSΦ : (S : W → ℂ) = Φ := rfl
  let g : W → ℂ := 𝓕⁻ Φ
  have hgS : g = ⇑(𝓕⁻ S : SchwartzMap W ℂ) := by rw [SchwartzMap.fourierInv_coe, hSΦ]
  have hgi : Integrable g := by rw [hgS]; exact (𝓕⁻ S : SchwartzMap W ℂ).integrable
  have hgg : ∫ v, g v = 1 := by
    have h1 : 𝓕⁻ g 0 = ∫ v, g v := by simp [Real.fourierInv_eq]
    have h2 : 𝓕⁻ g 0 = Φ 0 := by
      rw [Real.fourierInv_eq_fourier_neg, hgS, ← SchwartzMap.fourier_coe,
        FourierInvPair.fourier_fourierInv_eq, hSΦ, neg_zero]
    rw [← h1, h2]
    simp [Φ, h0]
  have hAc : Continuous A := A.continuous_of_finiteDimensional
  have hAm : AEMeasurable A volume := hAc.measurable.aemeasurable
  have hmapA : (volume : Measure W).map A = ENNReal.ofReal |(LinearMap.det A)⁻¹| • volume :=
    Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet
  have hgim : Integrable g ((volume : Measure W).map A) := by
    rw [hmapA]
    exact hgi.smul_measure ENNReal.ofReal_ne_top
  have hgA : Integrable (fun y => g (A y)) volume :=
    (integrable_map_measure hgim.aestronglyMeasurable hAm).mp hgim
  have hinner : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν = (s : ℝ) • g (A y) := by
    intro y
    show _ = (s : ℝ) • 𝓕⁻ Φ (A y)
    rw [hν, integral_smul_measure, ENNReal.coe_toReal, Real.fourierInv_eq]
    congr 1
    congr 1
    funext x
    rw [Circle.smul_def, smul_eq_mul, mul_comm]
  have hint : Integrable (fun y => ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂ν) ν := by
    simp only [hinner]
    rw [hν]
    exact (hgA.smul (s : ℝ)).smul_measure ENNReal.coe_ne_top
  have hcomp : ∫ y, g (A y) = (ENNReal.ofReal |(LinearMap.det A)⁻¹|).toReal • (1 : ℂ) := by
    rw [← integral_map hAm hgim.aestronglyMeasurable, hmapA, integral_smul_measure, hgg]
  have key := hP Φ hΦd.continuous hΦs hint 0
  simp only [hinner, inner_zero_right, AddChar.map_zero_eq_one, Circle.coe_one, mul_one] at key
  rw [hν, integral_smul_measure, integral_smul, hcomp, ENNReal.coe_toReal,
    ENNReal.toReal_ofReal (abs_nonneg _)] at key
  have hreal : (s : ℝ) * ((s : ℝ) * |(LinearMap.det A)⁻¹|) = 1 := by
    have h2 : Φ (-0) = 1 := by simp [Φ, h0]
    rw [h2] at key
    have := congrArg Complex.re key
    simp only [Complex.smul_re, Complex.one_re, smul_eq_mul, mul_one] at this
    exact this
  have hdpos : 0 < |LinearMap.det A| := abs_pos.mpr hdet
  have hsq : (s : ℝ) ^ 2 = |LinearMap.det A| := by
    rw [abs_inv] at hreal
    field_simp at hreal
    nlinarith [hreal]
  rw [hν]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, ← hsq, Real.sqrt_sq s.coe_nonneg]

/- English proof (translation)
Take `⟨A, hA, hdet⟩` from `exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b`. Establish `hP` using `fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z`. Use `haveI : μ.IsAddHaarMeasure := hμ.1`. Use `haveI : (μ.map e).IsAddHaarMeasure := Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective e.isClosedEmbedding.tendsto_cocompact`. Distinguish the cases in `hd : (Matrix.of fun i j => β (b i) (b j)).det = 0`.

It suffices to derive a contradiction. Rewrite `hd` using `[← hdet]`. Take `⟨k, hkker, hk⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)`. Establish `hk0 : ∀ y, β k y = 0` using `fun y => by`. Rewrite using `[hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]`.

Conclude with `false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP`. Rewrite `hd`, the goal using `[← hdet]`. Apply `measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd` to reduce the goal to its premises. Introduce `Φ hc hs hi z`. Establish `hβ' : ∀ y z, ⟪A y, z⟫ = β y z` using `fun y z => by rw [hS, hA, real_inner_comm]`.

Simplify using `only [← hA, hβ'] at hi ⊢`. Conclude with `hP Φ hc hs hi z`.
-/
theorem dens_generic (μ : Measure V) (χ : V → V → ℂ) (hμ : SelfDual μ χ) (e : V ≃ₜ W)
    (he : ∀ x y, e (x + y) = e x + e y) (β : W → W → ℝ)
    (hχ : ∀ x y, χ (e.symm x) (e.symm y) = ((𝐞 (β x y) : Circle) : ℂ))
    (hL : ∀ x x' y, β (x + x') y = β x y + β x' y) (hR : ∀ x y y', β x (y + y') = β x y + β x y')
    (hcL : ∀ y, Continuous fun x => β x y) (hcR : ∀ x, Continuous fun y => β x y)
    (hS : ∀ x y, β x y = β y x) (b : OrthonormalBasis ι ℝ W) :
    μ.map e = ENNReal.ofReal (Real.sqrt |(Matrix.of fun i j => β (b i) (b j)).det|) • volume := by
  obtain ⟨A, hA, hdet⟩ := exists_linearMap_inner_eq_and_det_eq_gram_det β hL hR hcL hcR b
  have hP := fun Φ hc hs hi z => integral_fourier_map_eq_neg_of_integrable μ χ hμ e he β hχ Φ hc hs hi z
  haveI : μ.IsAddHaarMeasure := hμ.1
  haveI : (μ.map e).IsAddHaarMeasure :=
    Measure.isAddHaarMeasure_map μ (AddMonoidHom.mk' e he) e.continuous e.surjective
      e.isClosedEmbedding.tendsto_cocompact
  by_cases hd : (Matrix.of fun i j => β (b i) (b j)).det = 0
  · exfalso
    rw [← hdet] at hd
    obtain ⟨k, hkker, hk⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
    have hk0 : ∀ y, β k y = 0 := fun y => by
      rw [hS, hA, LinearMap.mem_ker.mp hkker, inner_zero_right]
    exact false_of_degenerate_of_fourier_inversion (μ.map e) β hL hcL k hk hk0 hP
  · rw [← hdet] at hd ⊢
    apply measure_eq_sqrt_abs_det_smul_volume_of_inversion (μ.map e) A hd
    intro Φ hc hs hi z
    have hβ' : ∀ y z, ⟪A y, z⟫ = β y z := fun y z => by rw [hS, hA, real_inner_comm]
    simp only [← hA, hβ'] at hi ⊢
    exact hP Φ hc hs hi z

end PI.AprimeInfW.GenericDensity
