import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial MeasureTheory Filter Topology

variable {J : Type} [Fintype J] {D : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨y, hy, 1, one_ne_zero, (one_smul ℂ (γ y)).symm⟩`.
-/
theorem adens_mem_coneOver_self {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} {y : Fin D → ℂ}
    (hy : y ∈ U) : γ y ∈ coneOver U γ := ⟨y, hy, 1, one_ne_zero, (one_smul ℂ (γ y)).symm⟩

/- English proof (translation)
Take `⟨y, hy, d, hd, rfl⟩` from `hz`. Conclude with `⟨y, hy, c * d, mul_ne_zero hc hd, (mul_smul c d (γ y)).symm⟩`.
-/
theorem adens_smul_mem_coneOver {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} {z : J → ℂ}
    (hz : z ∈ coneOver U γ) {c : ℂ} (hc : c ≠ 0) : c • z ∈ coneOver U γ := by
  obtain ⟨y, hy, d, hd, rfl⟩ := hz
  exact ⟨y, hy, c * d, mul_ne_zero hc hd, (mul_smul c d (γ y)).symm⟩

/- English proof (translation)
Use `⟨fun h => ?_, fun h => adens_smul_mem_coneOver h hc⟩` and prove the remaining obligations. Establish `h2` using `adens_smul_mem_coneOver h (inv_ne_zero hc)`. Rewrite `h2` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis.
-/
theorem adens_smul_mem_coneOver_iff {U : Set (Fin D → ℂ)} {γ : (Fin D → ℂ) → J → ℂ} {z : J → ℂ}
    {c : ℂ} (hc : c ≠ 0) : c • z ∈ coneOver U γ ↔ z ∈ coneOver U γ := by
  refine ⟨fun h => ?_, fun h => adens_smul_mem_coneOver h hc⟩
  have h2 := adens_smul_mem_coneOver h (inv_ne_zero hc)
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h2

/- English proof (translation)
Establish `h1 : IsClosed {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0}`. Establish `hset : {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} = ⋂ f ∈ P, {z : J → ℂ | MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Rewrite using `[hset]`.

Conclude with `isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const`. Establish `h2 : MeasurableSet {z : J → ℂ | z ≠ 0}` using `(measurableSet_singleton (0 : J → ℂ)).compl`. Conclude with `h2.inter h1.measurableSet`.
-/
theorem adens_measurableSet_pts (P : Ideal (MvPolynomial J ℤ)) : MeasurableSet (pts P) := by
  have h1 : IsClosed {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
    have hset : {z : J → ℂ | ∀ f ∈ P, MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} =
        ⋂ f ∈ P, {z : J → ℂ | MvPolynomial.eval z (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext z
      simp
    rw [hset]
    exact isClosed_biInter fun f _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const
  have h2 : MeasurableSet {z : J → ℂ | z ≠ 0} := (measurableSet_singleton (0 : J → ℂ)).compl
  exact h2.inter h1.measurableSet

/- English proof (translation)
Establish `hmeas : Measurable (O.piecewise q (fun _ => (0 : Fin D → ℂ)))` using `ContinuousOn.measurable_piecewise hq continuousOn_const hO.measurableSet`. Establish `hset : {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} = O ∩ pts P ∩ (O.piecewise q (fun _ => (0 : Fin D → ℂ))) ⁻¹' A`. Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2, h3⟩`.

Use `⟨⟨h1, h2⟩, ?_⟩` and prove the remaining obligations. Use `show O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A`. Rewrite using `[Set.piecewise_eq_of_mem _ _ _ h1]` and apply the resulting hypothesis. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations.

Establish `h3' : O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A` using `h3`. Rewrite `h3'` using `[Set.piecewise_eq_of_mem _ _ _ h1]`. Then use the resulting hypothesis. Rewrite using `[hset]`. Conclude with `(hO.measurableSet.inter (adens_measurableSet_pts P)).inter (hmeas hA)`.
-/
theorem adens_measurableSet_cut {O : Set (J → ℂ)} {q : (J → ℂ) → Fin D → ℂ} (hO : IsOpen O)
    (hq : ContinuousOn q O) (P : Ideal (MvPolynomial J ℤ)) {A : Set (Fin D → ℂ)}
    (hA : MeasurableSet A) : MeasurableSet {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} := by
  classical
  have hmeas : Measurable (O.piecewise q (fun _ => (0 : Fin D → ℂ))) :=
    ContinuousOn.measurable_piecewise hq continuousOn_const hO.measurableSet
  have hset : {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} =
      O ∩ pts P ∩ (O.piecewise q (fun _ => (0 : Fin D → ℂ))) ⁻¹' A := by
    ext z
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      show O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A
      rwa [Set.piecewise_eq_of_mem _ _ _ h1]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨h1, h2, ?_⟩
      have h3' : O.piecewise q (fun _ => (0 : Fin D → ℂ)) z ∈ A := h3
      rwa [Set.piecewise_eq_of_mem _ _ _ h1] at h3'
  rw [hset]
  exact (hO.measurableSet.inter (adens_measurableSet_pts P)).inter (hmeas hA)

/- English proof (translation)
Establish `hfun : (fun z => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) z)) = S.indicator (fun _ => (1 : ENNReal))`. Use function extensionality and compare the values at `z`. Apply the tactic sequence `by_cases hz : z ∈ S <;> simp [hz]`. Rewrite using `[hfun, lintegral_indicator_const hS, one_mul, Measure.restrict_apply hS]`.
-/
theorem adens_lintegral_ofReal_indicator_one {α : Type*} [MeasurableSpace α] (ν : Measure α) {S C : Set α}
    (hS : MeasurableSet S) :
    ∫⁻ z in C, ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) z) ∂ν = ν (S ∩ C) := by
  have hfun : (fun z => ENNReal.ofReal (S.indicator (fun _ => (1 : ℝ)) z)) =
      S.indicator (fun _ => (1 : ENNReal)) := by
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  rw [hfun, lintegral_indicator_const hS, one_mul, Measure.restrict_apply hS]

/- English proof (translation)
Take `⟨hU, hγ, hpts, O, q, hO, hq, hOP, hsc, hqγ⟩` from `h`. Use `set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef`. Use `set V := U ∩ γ ⁻¹' O' with hVdef`. Establish `hV : IsOpen V` using `hγ.continuousOn.isOpen_inter_preimage hU hO'`. Establish `hyV : y ∈ V` using `⟨hy, hyO⟩`.

Establish `hτan : AnalyticOnNhd ℂ τ V` using `fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)`. Establish `hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w)`. Introduce `w hw`. Establish `hm : γ w ∈ O' ∩ pts P` using `⟨hw.2, hpts w hw.1⟩`. Rewrite `hm` using `[hOP']`.

Take `⟨y', hy', c, hc, he⟩` from `hm`. Establish `hO'y : γ' y' ∈ O'` using `(hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1`. Establish `: τ w = y'`. Simplify using `only [hτdef, Function.comp, he, (hsc' _ hO'y c hc).2, hqγ' y' hy']`. Conclude with `⟨this ▸ hy', c, hc, this ▸ he⟩`.

Establish `hγO : ∀ w ∈ U, γ w ∈ O` using `fun w hw => (hOP ▸ adens_mem_coneOver_self hw : γ w ∈ O ∩ pts P).1`. Establish `hinj : Set.InjOn τ V`. Introduce `w₁ h₁ w₂ h₂ he`. Take `⟨-, c₁, hc₁, e₁⟩` from `hfac w₁ h₁`. Take `⟨-, c₂, hc₂, e₂⟩` from `hfac w₂ h₂`.

Establish `: γ w₂ = (c₂ / c₁) • γ w₁`. Rewrite using `[e₂, e₁, he, smul_smul, div_mul_cancel₀ _ hc₁]`. Establish `h2` using `hqγ w₂ h₂.1`. Rewrite `h2` using `[this, (hsc _ (hγO w₁ h₁.1) _ (div_ne_zero hc₂ hc₁)).2, hqγ w₁ h₁.1]`. Conclude with `h2`.

Establish `hdet : ∀ w ∈ V, |(fderiv ℝ τ w).det| = Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det`. Introduce `w hw`. Establish `hd : DifferentiableAt ℂ τ w` using `(hτan w hw).differentiableAt`. Rewrite using `[hd.fderiv_restrictScalars ℝ]`. Establish `: ((fderiv ℂ τ w).restrictScalars ℝ).det = Complex.normSq (LinearMap.det (fderiv ℂ τ w : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)))` using `ReciprocityTheory.AnForm.A.det_restrictScalars_real _`.

Rewrite using `[this, ← ReciprocityTheory.AnForm.A.det_jacC, abs_of_nonneg (Complex.normSq_nonneg _)]`. Establish `hkey : ∀ A : Set (Fin D → ℂ), MeasurableSet A → A ⊆ V → ∫⁻ w in A, ENNReal.ofReal (ν w) = ∫⁻ w in A, ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)`. Introduce `A hA hAV`. Use `set S := {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} with hSdef`. Establish `hSm : MeasurableSet S` using `adens_measurableSet_cut hO hq.continuousOn P hA`.

Use `set g : (J → ℂ) → ℝ := S.indicator (fun _ => 1) with hgdef`. Establish `hgm : Measurable g` using `measurable_const.indicator hSm`. Establish `hg0 : ∀ z, 0 ≤ g z` using `fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z`. Establish `hSc : ∀ z, ∀ c : ℂ, c ≠ 0 → z ∈ S → c • z ∈ S`. Introduce and unpack `z c hc ⟨h1, h2, h3⟩`.

Establish `hz : z ∈ coneOver U γ` using `hOP ▸ ⟨h1, h2⟩`. Establish `hcz : c • z ∈ O ∩ pts P` using `hOP ▸ adens_smul_mem_coneOver hz hc`. Conclude with `⟨hcz.1, hcz.2, by rwa [(hsc z h1 c hc).2]⟩`. Establish `hgdeg : IsDegZero g`. Introduce `c z hc`.

Distinguish the cases in `hz : z ∈ S`. Simplify using `[hgdef, hz, hSc z c hc hz]`. Establish `: c • z ∉ S` using `fun h' => hz (by`. Use `hSc _ c⁻¹ (inv_ne_zero hc) h'` as an intermediate fact. Rewrite using `[smul_smul, inv_mul_cancel₀ hc, one_smul] at this)` and apply the resulting hypothesis.

Simplify using `[hgdef, hz, this]`. Establish `hSsub : S ⊆ coneOver U γ` using `fun z hz => hOP ▸ ⟨hz.1, hz.2.1⟩`. Establish `hSsub' : S ⊆ coneOver U' γ'`. Introduce and unpack `z ⟨h1, h2, h3⟩`. Establish `hz : z ∈ coneOver U γ` using `hOP ▸ ⟨h1, h2⟩`.

Take `⟨w, hw, c, hc, rfl⟩` from `hz`. Establish `hqw : q (c • γ w) = w` using `by rw [(hsc _ (hγO w hw) c hc).2, hqγ w hw]`. Rewrite `h3` using `[hqw]`. Take `⟨hτU, c', hc', e⟩` from `hfac w (hAV h3)`. Conclude with `⟨τ w, hτU, c * c', mul_ne_zero hc hc', by rw [e, smul_smul]⟩`.

Establish `e1` using `hν.2.2 g hgm hgdeg hg0`. Establish `e2` using `hν'.2.2 g hgm hgdeg hg0`. Rewrite `e1` using `[adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub]`. Rewrite `e2` using `[adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub']`. Establish `r1 : ∫⁻ w in U, ENNReal.ofReal (g (γ w) * ν w) = ∫⁻ w in A, ENNReal.ofReal (ν w)`.

Establish `: ∀ w ∈ U, ENNReal.ofReal (g (γ w) * ν w) = A.indicator (fun w => ENNReal.ofReal (ν w)) w`. Introduce `w hw`. Establish `hmem : γ w ∈ S ↔ w ∈ A`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, -, h3⟩`.

Rewrite `h3` using `[hqγ w hw]`. Then use the resulting hypothesis. Introduce `hwA; exact ⟨hγO w hw, hpts w hw, by rwa [hqγ w hw]⟩`. Distinguish the cases in `hwA : w ∈ A`. Simplify using `[hgdef, hmem.2 hwA, hwA]`. Simplify using `[hgdef, mt hmem.1 hwA, hwA]`.

Rewrite using `[setLIntegral_congr_fun hU.measurableSet this, lintegral_indicator hA, Measure.restrict_restrict hA, Set.inter_eq_left.2 (hAV.trans Set.inter_subset_left)]`. Establish `hderiv : ∀ x ∈ A, HasFDerivWithinAt τ (fderiv ℝ τ x) A x` using `fun x hx => ((hτan x (hAV hx)).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt`. Establish `hτA : MeasurableSet (τ '' A)` using `measurable_image_of_fderivWithin hA hderiv (hinj.mono hAV)`. Establish `hτsub : τ '' A ⊆ U'` using `by rintro _ ⟨w, hw, rfl⟩; exact (hfac w (hAV hw)).1`. Establish `r2 : ∫⁻ y' in U', ENNReal.ofReal (g (γ' y') * ν' y') = ∫⁻ y' in τ '' A, ENNReal.ofReal (ν' y')`.

Establish `: ∀ y' ∈ U', ENNReal.ofReal (g (γ' y') * ν' y') = (τ '' A).indicator (fun y' => ENNReal.ofReal (ν' y')) y'`. Introduce `y' hy'`. Establish `hO'y : γ' y' ∈ O'` using `(hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1`. Establish `hmem : γ' y' ∈ S ↔ y' ∈ τ '' A`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Establish `hz : γ' y' ∈ coneOver U γ` using `hOP ▸ ⟨h1, h2⟩`. Take `⟨w, hw, c, hc, e⟩` from `hz`. Establish `hqw : q (γ' y') = w` using `by rw [e, (hsc _ (hγO w hw) c hc).2, hqγ w hw]`. Use `⟨w, hqw ▸ h3, ?_⟩` and prove the remaining obligations.

Establish `: γ w = c⁻¹ • γ' y'` using `by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Use `show q' (γ w) = y'`. Rewrite using `[this, (hsc' _ hO'y _ (inv_ne_zero hc)).2, hqγ' y' hy']`. Introduce and unpack `⟨w, hwA, rfl⟩`. Take `⟨-, c, hc, e⟩` from `hfac w (hAV hwA)`.

Establish `: γ' (τ w) = c⁻¹ • γ w` using `by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Establish `hz : c⁻¹ • γ w ∈ O ∩ pts P` using `hOP ▸ adens_smul_mem_coneOver (adens_mem_coneOver_self (hAV hwA).1) (inv_ne_zero hc)`. Rewrite using `[this]`. Conclude with `⟨hz.1, hz.2, by`. Rewrite using `[(hsc _ (hγO w (hAV hwA).1) _ (inv_ne_zero hc)).2, hqγ w (hAV hwA).1]⟩` and apply the resulting hypothesis.

Distinguish the cases in `h' : y' ∈ τ '' A`. Simplify using `[hgdef, hmem.2 h', h']`. Simplify using `[hgdef, mt hmem.1 h', h']`. Rewrite using `[setLIntegral_congr_fun hU'.measurableSet this, lintegral_indicator hτA, Measure.restrict_restrict hτA, Set.inter_eq_left.2 hτsub]`. Establish `r3` using `lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv (hinj.mono hAV) (fun y' => ENNReal.ofReal (ν' y'))`.

Rewrite using `[← r1, ← e1, e2, r2, r3]`. Use `setLIntegral_congr_fun hA (fun w hw => ?_)` and prove the remaining obligations. Rewrite using `[hdet w (hAV hw), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]`. Establish `hcontν : ContinuousOn (fun w => ENNReal.ofReal (ν w)) V` using `ENNReal.continuous_ofReal.comp_continuousOn (hν.1.continuousOn.mono Set.inter_subset_left)`. Establish `hτc : ContinuousOn τ V` using `hτan.continuousOn`.

Establish `hNc : ContinuousOn (fun w => Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det) V`. Establish `hf : ContinuousOn (fderiv ℂ τ) V` using `(hτan.fderiv).continuousOn`. Establish `hj : ContinuousOn (fun w => ReciprocityTheory.AnForm.A.jacC τ w) V`. Use `continuousOn_pi.2 fun a => continuousOn_pi.2 fun k => ?_` and prove the remaining obligations. Conclude with `(continuous_apply a).comp_continuousOn ((ContinuousLinearMap.apply ℂ (Fin D → ℂ) (Pi.single k 1)).continuous.comp_continuousOn hf)`.

Conclude with `Complex.continuous_normSq.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hj)`. Establish `hcont' : ContinuousOn (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)) V`. Use `ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ hNc)` and prove the remaining obligations. Conclude with `hν'.1.continuousOn.comp hτc (fun w hw => (hfac w hw).1)`. Establish `hae : (fun w => ENNReal.ofReal (ν w)) =ᵐ[volume.restrict V] (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det))`.

Use `ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (hcontν.aemeasurable hV.measurableSet) (hcont'.aemeasurable hV.measurableSet) ?_` and prove the remaining obligations. Introduce `s hs _`. Rewrite using `[Measure.restrict_restrict hs]`. Conclude with `hkey _ (hs.inter hV.measurableSet) Set.inter_subset_right`. Use `Measure.eqOn_open_of_ae_eq hae hV hcontν hcont' hyV` as an intermediate fact.

Simplify using `only at this`. Rewrite `this` using `[ENNReal.ofReal_eq_ofReal_iff (hν.2.1 y hy).le (mul_nonneg (hν'.2.1 _ (hfac y hyV).1).le (Complex.normSq_nonneg _))]`. Then use the resulting hypothesis.
-/
theorem adens_density_compare {P : Ideal (MvPolynomial J ℤ)} {μ : Measure (J → ℂ)}
    {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ} {ν ν' : (Fin D → ℂ) → ℝ}
    (h : IsParam P U γ) (hν : IsDensityFor μ U γ ν) (hU' : IsOpen U')
    (hγ' : AnalyticOnNhd ℂ γ' U') (hν' : IsDensityFor μ U' γ' ν')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    ν y = ν' (q' (γ y)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC (q' ∘ γ) y).det := by
  classical
  obtain ⟨hU, hγ, hpts, O, q, hO, hq, hOP, hsc, hqγ⟩ := h
  set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef
  set V := U ∩ γ ⁻¹' O' with hVdef
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU hO'
  have hyV : y ∈ V := ⟨hy, hyO⟩
  have hτan : AnalyticOnNhd ℂ τ V := fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)

  have hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w) := by
    intro w hw
    have hm : γ w ∈ O' ∩ pts P := ⟨hw.2, hpts w hw.1⟩
    rw [hOP'] at hm
    obtain ⟨y', hy', c, hc, he⟩ := hm
    have hO'y : γ' y' ∈ O' := (hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1
    have : τ w = y' := by
      simp only [hτdef, Function.comp, he, (hsc' _ hO'y c hc).2, hqγ' y' hy']
    exact ⟨this ▸ hy', c, hc, this ▸ he⟩
  have hγO : ∀ w ∈ U, γ w ∈ O := fun w hw => (hOP ▸ adens_mem_coneOver_self hw : γ w ∈ O ∩ pts P).1
  have hinj : Set.InjOn τ V := by
    intro w₁ h₁ w₂ h₂ he
    obtain ⟨-, c₁, hc₁, e₁⟩ := hfac w₁ h₁
    obtain ⟨-, c₂, hc₂, e₂⟩ := hfac w₂ h₂
    have : γ w₂ = (c₂ / c₁) • γ w₁ := by
      rw [e₂, e₁, he, smul_smul, div_mul_cancel₀ _ hc₁]
    have h2 := hqγ w₂ h₂.1
    rw [this, (hsc _ (hγO w₁ h₁.1) _ (div_ne_zero hc₂ hc₁)).2, hqγ w₁ h₁.1] at h2
    exact h2
  have hdet : ∀ w ∈ V, |(fderiv ℝ τ w).det| = Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det := by
    intro w hw
    have hd : DifferentiableAt ℂ τ w := (hτan w hw).differentiableAt
    rw [hd.fderiv_restrictScalars ℝ]
    have : ((fderiv ℂ τ w).restrictScalars ℝ).det =
        Complex.normSq (LinearMap.det (fderiv ℂ τ w : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))) :=
      ReciprocityTheory.AnForm.A.det_restrictScalars_real _
    rw [this, ← ReciprocityTheory.AnForm.A.det_jacC, abs_of_nonneg (Complex.normSq_nonneg _)]
  have hkey : ∀ A : Set (Fin D → ℂ), MeasurableSet A → A ⊆ V →
      ∫⁻ w in A, ENNReal.ofReal (ν w) =
        ∫⁻ w in A, ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det) := by
    intro A hA hAV
    set S := {z | z ∈ O ∧ z ∈ pts P ∧ q z ∈ A} with hSdef
    have hSm : MeasurableSet S := adens_measurableSet_cut hO hq.continuousOn P hA
    set g : (J → ℂ) → ℝ := S.indicator (fun _ => 1) with hgdef
    have hgm : Measurable g := measurable_const.indicator hSm
    have hg0 : ∀ z, 0 ≤ g z := fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z
    have hSc : ∀ z, ∀ c : ℂ, c ≠ 0 → z ∈ S → c • z ∈ S := by
      rintro z c hc ⟨h1, h2, h3⟩
      have hz : z ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
      have hcz : c • z ∈ O ∩ pts P := hOP ▸ adens_smul_mem_coneOver hz hc
      exact ⟨hcz.1, hcz.2, by rwa [(hsc z h1 c hc).2]⟩
    have hgdeg : IsDegZero g := by
      intro c z hc
      by_cases hz : z ∈ S
      · simp [hgdef, hz, hSc z c hc hz]
      · have : c • z ∉ S := fun h' => hz (by
          have := hSc _ c⁻¹ (inv_ne_zero hc) h'
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this)
        simp [hgdef, hz, this]
    have hSsub : S ⊆ coneOver U γ := fun z hz => hOP ▸ ⟨hz.1, hz.2.1⟩
    have hSsub' : S ⊆ coneOver U' γ' := by
      rintro z ⟨h1, h2, h3⟩
      have hz : z ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
      obtain ⟨w, hw, c, hc, rfl⟩ := hz
      have hqw : q (c • γ w) = w := by rw [(hsc _ (hγO w hw) c hc).2, hqγ w hw]
      rw [hqw] at h3
      obtain ⟨hτU, c', hc', e⟩ := hfac w (hAV h3)
      exact ⟨τ w, hτU, c * c', mul_ne_zero hc hc', by rw [e, smul_smul]⟩
    have e1 := hν.2.2 g hgm hgdeg hg0
    have e2 := hν'.2.2 g hgm hgdeg hg0
    rw [adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub] at e1
    rw [adens_lintegral_ofReal_indicator_one _ hSm, Set.inter_eq_left.2 hSsub'] at e2
    have r1 : ∫⁻ w in U, ENNReal.ofReal (g (γ w) * ν w) = ∫⁻ w in A, ENNReal.ofReal (ν w) := by
      have : ∀ w ∈ U, ENNReal.ofReal (g (γ w) * ν w) =
          A.indicator (fun w => ENNReal.ofReal (ν w)) w := by
        intro w hw
        have hmem : γ w ∈ S ↔ w ∈ A := by
          constructor
          · rintro ⟨-, -, h3⟩; rwa [hqγ w hw] at h3
          · intro hwA; exact ⟨hγO w hw, hpts w hw, by rwa [hqγ w hw]⟩
        by_cases hwA : w ∈ A
        · simp [hgdef, hmem.2 hwA, hwA]
        · simp [hgdef, mt hmem.1 hwA, hwA]
      rw [setLIntegral_congr_fun hU.measurableSet this, lintegral_indicator hA,
        Measure.restrict_restrict hA, Set.inter_eq_left.2 (hAV.trans Set.inter_subset_left)]
    have hderiv : ∀ x ∈ A, HasFDerivWithinAt τ (fderiv ℝ τ x) A x := fun x hx =>
      ((hτan x (hAV hx)).differentiableAt.restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt
    have hτA : MeasurableSet (τ '' A) :=
      measurable_image_of_fderivWithin hA hderiv (hinj.mono hAV)
    have hτsub : τ '' A ⊆ U' := by rintro _ ⟨w, hw, rfl⟩; exact (hfac w (hAV hw)).1
    have r2 : ∫⁻ y' in U', ENNReal.ofReal (g (γ' y') * ν' y') =
        ∫⁻ y' in τ '' A, ENNReal.ofReal (ν' y') := by
      have : ∀ y' ∈ U', ENNReal.ofReal (g (γ' y') * ν' y') =
          (τ '' A).indicator (fun y' => ENNReal.ofReal (ν' y')) y' := by
        intro y' hy'
        have hO'y : γ' y' ∈ O' := (hOP' ▸ adens_mem_coneOver_self hy' : γ' y' ∈ O' ∩ pts P).1
        have hmem : γ' y' ∈ S ↔ y' ∈ τ '' A := by
          constructor
          · rintro ⟨h1, h2, h3⟩
            have hz : γ' y' ∈ coneOver U γ := hOP ▸ ⟨h1, h2⟩
            obtain ⟨w, hw, c, hc, e⟩ := hz
            have hqw : q (γ' y') = w := by rw [e, (hsc _ (hγO w hw) c hc).2, hqγ w hw]
            refine ⟨w, hqw ▸ h3, ?_⟩
            have : γ w = c⁻¹ • γ' y' := by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
            show q' (γ w) = y'
            rw [this, (hsc' _ hO'y _ (inv_ne_zero hc)).2, hqγ' y' hy']
          · rintro ⟨w, hwA, rfl⟩
            obtain ⟨-, c, hc, e⟩ := hfac w (hAV hwA)
            have : γ' (τ w) = c⁻¹ • γ w := by rw [e, smul_smul, inv_mul_cancel₀ hc, one_smul]
            have hz : c⁻¹ • γ w ∈ O ∩ pts P :=
              hOP ▸ adens_smul_mem_coneOver (adens_mem_coneOver_self (hAV hwA).1) (inv_ne_zero hc)
            rw [this]
            exact ⟨hz.1, hz.2, by
              rwa [(hsc _ (hγO w (hAV hwA).1) _ (inv_ne_zero hc)).2, hqγ w (hAV hwA).1]⟩
        by_cases h' : y' ∈ τ '' A
        · simp [hgdef, hmem.2 h', h']
        · simp [hgdef, mt hmem.1 h', h']
      rw [setLIntegral_congr_fun hU'.measurableSet this, lintegral_indicator hτA,
        Measure.restrict_restrict hτA, Set.inter_eq_left.2 hτsub]
    have r3 := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hA hderiv (hinj.mono hAV)
      (fun y' => ENNReal.ofReal (ν' y'))
    rw [← r1, ← e1, e2, r2, r3]
    refine setLIntegral_congr_fun hA (fun w hw => ?_)
    rw [hdet w (hAV hw), ← ENNReal.ofReal_mul (Complex.normSq_nonneg _), mul_comm]
  have hcontν : ContinuousOn (fun w => ENNReal.ofReal (ν w)) V :=
    ENNReal.continuous_ofReal.comp_continuousOn (hν.1.continuousOn.mono Set.inter_subset_left)
  have hτc : ContinuousOn τ V := hτan.continuousOn
  have hNc : ContinuousOn (fun w => Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det) V := by
    have hf : ContinuousOn (fderiv ℂ τ) V := (hτan.fderiv).continuousOn
    have hj : ContinuousOn (fun w => ReciprocityTheory.AnForm.A.jacC τ w) V := by
      refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun k => ?_
      exact (continuous_apply a).comp_continuousOn
        ((ContinuousLinearMap.apply ℂ (Fin D → ℂ) (Pi.single k 1)).continuous.comp_continuousOn hf)
    exact Complex.continuous_normSq.comp_continuousOn ((continuous_id.matrix_det).comp_continuousOn hj)
  have hcont' : ContinuousOn
      (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)) V := by
    refine ENNReal.continuous_ofReal.comp_continuousOn (ContinuousOn.mul ?_ hNc)
    exact hν'.1.continuousOn.comp hτc (fun w hw => (hfac w hw).1)
  have hae : (fun w => ENNReal.ofReal (ν w)) =ᵐ[volume.restrict V]
      (fun w => ENNReal.ofReal (ν' (τ w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC τ w).det)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ (hcontν.aemeasurable hV.measurableSet)
      (hcont'.aemeasurable hV.measurableSet) ?_
    intro s hs _
    rw [Measure.restrict_restrict hs]
    exact hkey _ (hs.inter hV.measurableSet) Set.inter_subset_right
  have := Measure.eqOn_open_of_ae_eq hae hV hcontν hcont' hyV
  simp only at this
  rwa [ENNReal.ofReal_eq_ofReal_iff (hν.2.1 y hy).le
    (mul_nonneg (hν'.2.1 _ (hfac y hyV).1).le (Complex.normSq_nonneg _))] at this

/- English proof (translation)
Establish `hmem : γ w ∈ O' ∩ pts P` using `⟨hwO, hpts w hw⟩`. Rewrite `hmem` using `[hOP']`. Take `⟨y', hy', c, hc, hcw⟩` from `hmem`. Establish `hinv : c⁻¹ • γ w = γ' y'` using `by rw [hcw, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Establish `hq : q' (γ w) = y'`.

Rewrite using `[← (hsc' (γ w) hwO c⁻¹ (inv_ne_zero hc)).2, hinv, hqγ' y' hy']`. Use `⟨by rw [hq]; exact hy', c, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hq]`. Conclude with `hcw`.
-/
theorem adens_trans_fac {P : Ideal (MvPolynomial J ℤ)} {U U' : Set (Fin D → ℂ)}
    {γ γ' : (Fin D → ℂ) → J → ℂ} (hpts : ∀ y ∈ U, γ y ∈ pts P) {O' : Set (J → ℂ)}
    {q' : (J → ℂ) → Fin D → ℂ} (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {w : Fin D → ℂ} (hw : w ∈ U) (hwO : γ w ∈ O') :
    q' (γ w) ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (q' (γ w)) := by
  have hmem : γ w ∈ O' ∩ pts P := ⟨hwO, hpts w hw⟩
  rw [hOP'] at hmem
  obtain ⟨y', hy', c, hc, hcw⟩ := hmem
  have hinv : c⁻¹ • γ w = γ' y' := by rw [hcw, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hq : q' (γ w) = y' := by
    rw [← (hsc' (γ w) hwO c⁻¹ (inv_ne_zero hc)).2, hinv, hqγ' y' hy']
  refine ⟨by rw [hq]; exact hy', c, hc, ?_⟩
  rw [hq]
  exact hcw

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem adens_maDensity_eq_maDens (φ : Fin D → (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    maDensity φ z = ReciprocityTheory.AnForm.maDens φ z := rfl

/- English proof (translation)
Conclude with `(h.fderiv (𝕜 := ℝ)).fderiv_eq`.
-/
theorem adens_fderiv_fderiv_congr {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := by
  exact (h.fderiv (𝕜 := ℝ)).fderiv_eq

/- English proof (translation)
Unfold `ReciprocityTheory.AnForm.hessC`. Rewrite using `[adens_fderiv_fderiv_congr h]`.
-/
theorem adens_hessC_congr {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (h : f =ᶠ[𝓝 y] g) :
    ReciprocityTheory.AnForm.hessC f y = ReciprocityTheory.AnForm.hessC g y := by
  unfold ReciprocityTheory.AnForm.hessC
  rw [adens_fderiv_fderiv_congr h]

/- English proof (translation)
Establish `hρ' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) m.ρ {z | z ≠ 0}` using `contDiffOn_infty.1 hsm 2`. Establish `hρ : ContDiffAt ℝ 2 m.ρ (γ' v)` using `hρ'.contDiffAt (isOpen_ne.mem_nhds hne)`. Establish `hγ : ContDiffAt ℝ 2 γ' v` using `(hγ'.contDiffAt).restrict_scalars ℝ`. Conclude with `(hρ.comp v hγ).log (m.pos _ hne).ne'`.
-/
theorem adens_contDiffAt_logρ {m : ConeMetric ℂ J} (hsm : IsSmoothMetric m) {γ' : (Fin D → ℂ) → J → ℂ}
    {v : Fin D → ℂ} (hγ' : AnalyticAt ℂ γ' v) (hne : γ' v ≠ 0) :
    ContDiffAt ℝ 2 (fun w => Real.log (m.ρ (γ' w))) v := by
  have hρ' : ContDiffOn ℝ ((2 : ℕ) : WithTop ℕ∞) m.ρ {z | z ≠ 0} := contDiffOn_infty.1 hsm 2
  have hρ : ContDiffAt ℝ 2 m.ρ (γ' v) := hρ'.contDiffAt (isOpen_ne.mem_nhds hne)
  have hγ : ContDiffAt ℝ 2 γ' v := (hγ'.contDiffAt).restrict_scalars ℝ
  exact (hρ.comp v hγ).log (m.pos _ hne).ne'

/- English proof (translation)
Take `⟨hU, hγ, hpts, -⟩` from `h`. Use `set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef`. Use `set V := U ∩ γ ⁻¹' O' with hVdef`. Establish `hV : IsOpen V` using `hγ.continuousOn.isOpen_inter_preimage hU hO'`. Establish `hyV : y ∈ V` using `⟨hy, hyO⟩`.

Establish `hτan : AnalyticOnNhd ℂ τ V` using `fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)`. Establish `hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w)` using `fun w hw => adens_trans_fac hpts hOP' hsc' hqγ' hw.1 hw.2`. Establish `hpts' : ∀ v ∈ U', γ' v ∈ pts P` using `fun v hv => (hOP' ▸ adens_mem_coneOver_self hv : γ' v ∈ O' ∩ pts P).2`. Establish `hτy : τ y ∈ U'` using `(hfac y hyV).1`. Establish `hne : γ' (τ y) ≠ 0` using `(hpts' _ hτy).1`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, γ' (τ y) i ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hne (funext hc)`. Establish `hgτ : AnalyticAt ℂ (fun w => γ' (τ w)) y` using `(hγ' _ hτy).comp (hτan y hyV)`.

Establish `hgτi : AnalyticAt ℂ (fun w => γ' (τ w) i) y` using `analyticAt_pi_iff.1 hgτ i`. Establish `hγi : AnalyticAt ℂ (fun w => γ w i) y` using `analyticAt_pi_iff.1 (hγ y hy) i`. Use `set c : (Fin D → ℂ) → ℂ := fun w => γ w i / γ' (τ w) i with hcdef`. Establish `hcan : AnalyticAt ℂ c y` using `hγi.div hgτi hi`. Take `⟨c₀, hc₀, e₀⟩` from `(hfac y hyV).2`.

Establish `hcy : c y ≠ 0`. Establish `: γ y i = c₀ * γ' (τ y) i` using `by rw [e₀]; rfl`. Simplify using `only [hcdef, this, mul_div_assoc, div_self hi, mul_one]`. Conclude with `hc₀`. Use `set φ' : (Fin D → ℂ) → ℝ := fun w => Real.log (m.ρ (γ' w)) with hφ'def`.

Establish `hev : (fun w => Real.log (m.ρ (γ w))) =ᶠ[𝓝 y] fun w => φ' (τ w) + Real.log ‖c w‖`. Establish `h1 : ∀ᶠ w in 𝓝 y, w ∈ V` using `hV.mem_nhds hyV`. Establish `h2 : ∀ᶠ w in 𝓝 y, γ' (τ w) i ≠ 0` using `hgτi.continuousAt.eventually_ne hi`. Use `filter_upwards [h1, h2] with w hw hwi`. Take `⟨hτw, c₁, hc₁, e₁⟩` from `hfac w hw`.

Establish `hcw : c w = c₁`. Establish `: γ w i = c₁ * γ' (τ w) i` using `by rw [e₁]; rfl`. Simplify using `only [hcdef, this, mul_div_assoc, div_self hwi, mul_one]`. Establish `hne' : γ' (τ w) ≠ 0` using `(hpts' _ hτw).1`. Simplify using `only [hφ'def]`.

Rewrite using `[hcw, e₁, m.smul, Real.log_mul (norm_ne_zero_iff.2 hc₁) (m.pos _ hne').ne', add_comm]`. Establish `hφ'τ : ContDiffAt ℝ 2 (fun w => φ' (τ w)) y` using `(adens_contDiffAt_logρ hsm hgτ (by simpa using hne))`. Establish `hH : ReciprocityTheory.AnForm.hessC (fun w => Real.log (m.ρ (γ w))) y = ReciprocityTheory.AnForm.hessC (φ' ∘ τ) y`. Rewrite using `[adens_hessC_congr hev]`. Conclude with `ReciprocityTheory.AnForm.A.hessC_add_log_norm _ c y hφ'τ hcan hcy`.

Establish `hcomp` using `ReciprocityTheory.AnForm.A.maDens_comp (fun _ : Fin D => φ') τ y (hτan y hyV) (fun _ => adens_contDiffAt_logρ hsm (hγ' _ hτy) hne)`. Rewrite using `[adens_maDensity_eq_maDens, adens_maDensity_eq_maDens]`. Express the relevant statement in the definitionally equal form `_ = ReciprocityTheory.AnForm.maDens (fun _ : Fin D => φ') (τ y) * _`. Rewrite using `[← hcomp]`. Unfold `ReciprocityTheory.AnForm.maDens`.

Simplify using `only [hH]`.
-/
theorem adens_maDensity_compare {P : Ideal (MvPolynomial J ℤ)} {m : ConeMetric ℂ J}
    (hsm : IsSmoothMetric m) {U U' : Set (Fin D → ℂ)} {γ γ' : (Fin D → ℂ) → J → ℂ}
    (h : IsParam P U γ) (hγ' : AnalyticOnNhd ℂ γ' U')
    {O' : Set (J → ℂ)} {q' : (J → ℂ) → Fin D → ℂ} (hO' : IsOpen O') (hq' : AnalyticOnNhd ℂ q' O')
    (hOP' : O' ∩ pts P = coneOver U' γ')
    (hsc' : ∀ z ∈ O', ∀ c : ℂ, c ≠ 0 → c • z ∈ O' ∧ q' (c • z) = q' z)
    (hqγ' : ∀ y ∈ U', q' (γ' y) = y) {y : Fin D → ℂ} (hy : y ∈ U) (hyO : γ y ∈ O') :
    maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ w))) y =
      maDensity (fun _ : Fin D => fun w => Real.log (m.ρ (γ' w))) (q' (γ y)) *
        Complex.normSq (ReciprocityTheory.AnForm.A.jacC (q' ∘ γ) y).det := by
  classical
  obtain ⟨hU, hγ, hpts, -⟩ := h
  set τ : (Fin D → ℂ) → Fin D → ℂ := q' ∘ γ with hτdef
  set V := U ∩ γ ⁻¹' O' with hVdef
  have hV : IsOpen V := hγ.continuousOn.isOpen_inter_preimage hU hO'
  have hyV : y ∈ V := ⟨hy, hyO⟩
  have hτan : AnalyticOnNhd ℂ τ V := fun w hw => (hq' (γ w) hw.2).comp (hγ w hw.1)
  have hfac : ∀ w ∈ V, τ w ∈ U' ∧ ∃ c : ℂ, c ≠ 0 ∧ γ w = c • γ' (τ w) := fun w hw =>
    adens_trans_fac hpts hOP' hsc' hqγ' hw.1 hw.2
  have hpts' : ∀ v ∈ U', γ' v ∈ pts P := fun v hv =>
    (hOP' ▸ adens_mem_coneOver_self hv : γ' v ∈ O' ∩ pts P).2
  have hτy : τ y ∈ U' := (hfac y hyV).1
  have hne : γ' (τ y) ≠ 0 := (hpts' _ hτy).1
  obtain ⟨i, hi⟩ : ∃ i, γ' (τ y) i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hne (funext hc)
  have hgτ : AnalyticAt ℂ (fun w => γ' (τ w)) y := (hγ' _ hτy).comp (hτan y hyV)
  have hgτi : AnalyticAt ℂ (fun w => γ' (τ w) i) y := analyticAt_pi_iff.1 hgτ i
  have hγi : AnalyticAt ℂ (fun w => γ w i) y := analyticAt_pi_iff.1 (hγ y hy) i
  set c : (Fin D → ℂ) → ℂ := fun w => γ w i / γ' (τ w) i with hcdef
  have hcan : AnalyticAt ℂ c y := hγi.div hgτi hi
  obtain ⟨c₀, hc₀, e₀⟩ := (hfac y hyV).2
  have hcy : c y ≠ 0 := by
    have : γ y i = c₀ * γ' (τ y) i := by rw [e₀]; rfl
    simp only [hcdef, this, mul_div_assoc, div_self hi, mul_one]
    exact hc₀
  set φ' : (Fin D → ℂ) → ℝ := fun w => Real.log (m.ρ (γ' w)) with hφ'def
  have hev : (fun w => Real.log (m.ρ (γ w))) =ᶠ[𝓝 y] fun w => φ' (τ w) + Real.log ‖c w‖ := by
    have h1 : ∀ᶠ w in 𝓝 y, w ∈ V := hV.mem_nhds hyV
    have h2 : ∀ᶠ w in 𝓝 y, γ' (τ w) i ≠ 0 := hgτi.continuousAt.eventually_ne hi
    filter_upwards [h1, h2] with w hw hwi
    obtain ⟨hτw, c₁, hc₁, e₁⟩ := hfac w hw
    have hcw : c w = c₁ := by
      have : γ w i = c₁ * γ' (τ w) i := by rw [e₁]; rfl
      simp only [hcdef, this, mul_div_assoc, div_self hwi, mul_one]
    have hne' : γ' (τ w) ≠ 0 := (hpts' _ hτw).1
    simp only [hφ'def]
    rw [hcw, e₁, m.smul, Real.log_mul (norm_ne_zero_iff.2 hc₁) (m.pos _ hne').ne', add_comm]
  have hφ'τ : ContDiffAt ℝ 2 (fun w => φ' (τ w)) y :=
    (adens_contDiffAt_logρ hsm hgτ (by simpa using hne))
  have hH : ReciprocityTheory.AnForm.hessC (fun w => Real.log (m.ρ (γ w))) y =
      ReciprocityTheory.AnForm.hessC (φ' ∘ τ) y := by
    rw [adens_hessC_congr hev]
    exact ReciprocityTheory.AnForm.A.hessC_add_log_norm _ c y hφ'τ hcan hcy
  have hcomp := ReciprocityTheory.AnForm.A.maDens_comp (fun _ : Fin D => φ') τ y (hτan y hyV)
    (fun _ => adens_contDiffAt_logρ hsm (hγ' _ hτy) hne)
  rw [adens_maDensity_eq_maDens, adens_maDensity_eq_maDens]
  change _ = ReciprocityTheory.AnForm.maDens (fun _ : Fin D => φ') (τ y) * _
  rw [← hcomp]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
