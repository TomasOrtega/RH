import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsBergDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.SectionModuleEqSpanPow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AParamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ABridgeStB
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.BergmanDerivSt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.GeometryOfNumbersTheory MvPolynomial MeasureTheory Module Filter Asymptotics
open scoped ComplexOrder

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] {D : ℕ}

/- English proof (translation)
Use `haveI : Module.Finite ℤ (sec ℤ x n) := by`. Rewrite using `[Module.finite_def, Submodule.fg_top]`. Conclude with `(homogeneousSubmodule_fg (Ix κ) ℤ n).map _`. Use `haveI : Module.Free ℤ (sec ℤ x n) := Module.free_of_finite_type_torsion_free'`. Set `bas` to `Module.finBasis ℤ (sec ℤ x n)`.

Establish `hmem : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ aeval x f = ((bas k : sec ℤ x n) : Ω)`. Introduce `k`. Take `⟨f, hf, hfx⟩` from `Submodule.mem_map.1 (bas k).2`. Conclude with `⟨f, (mem_homogeneousSubmodule n f).1 hf, hfx⟩`. Use `choose f hfh hfx using hmem`.

Establish `hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g`. Introduce `g`. Rewrite using `[← algebraMap_int_eq, aeval_map_algebraMap]`. Establish `hval : (fun k => aeval x (map (Int.castRingHom ℚ) (f k))) = (sec ℤ x n).subtype ∘ bas`. Use function extensionality and compare the values at `k`.

Rewrite using `[hcast, hfx]`. Both sides reduce to the same expression. Use `⟨fun k => map (Int.castRingHom ℚ) (f k), fun k => ⟨f k, hfh k, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Conclude with `bas.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)`.

Rewrite using `[hval, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]`.
-/
theorem exists_isSecBasis (x : Ix κ → Ω) (n : ℕ) :
    ∃ b : Fin (finrank ℤ (sec ℤ x n)) → MvPolynomial (Ix κ) ℚ, IsSecBasis x n b := by
  classical
  haveI : Module.Finite ℤ (sec ℤ x n) := by
    rw [Module.finite_def, Submodule.fg_top]
    exact (homogeneousSubmodule_fg (Ix κ) ℤ n).map _
  haveI : Module.Free ℤ (sec ℤ x n) := Module.free_of_finite_type_torsion_free'
  let bas := Module.finBasis ℤ (sec ℤ x n)
  have hmem : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ aeval x f = ((bas k : sec ℤ x n) : Ω) := by
    intro k
    obtain ⟨f, hf, hfx⟩ := Submodule.mem_map.1 (bas k).2
    exact ⟨f, (mem_homogeneousSubmodule n f).1 hf, hfx⟩
  choose f hfh hfx using hmem
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  have hval : (fun k => aeval x (map (Int.castRingHom ℚ) (f k))) = (sec ℤ x n).subtype ∘ bas := by
    funext k
    rw [hcast, hfx]
    rfl
  refine ⟨fun k => map (Int.castRingHom ℚ) (f k), fun k => ⟨f k, hfh k, rfl⟩, ?_, ?_⟩
  · rw [hval]
    exact bas.linearIndependent.map' (sec ℤ x n).subtype (Submodule.ker_subtype _)
  · rw [hval, Set.range_comp, Submodule.span_image, bas.span_eq, Submodule.map_subtype_top]

/- English proof (translation)
Rewrite using `[← hb.2.2, finrank_span_eq_card hb.2.1, Fintype.card_fin]`.
-/
theorem IsSecBasis.card_eq {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : r = finrank ℤ (sec ℤ x n) := by
  rw [← hb.2.2, finrank_span_eq_card hb.2.1, Fintype.card_fin]

/- English proof (translation)
The claim follows from `hm.continuousOn.mono fun _ hz => hz`.
-/
theorem continuousOn_rho {J : Type} [Fintype J] {m : ConeMetric ℂ J} (hm : IsSmoothMetric m) :
    ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz

/- English proof (translation)
Establish `hm : IsSmoothMetric m` using `hg.semipos.1`. Establish `hρ : ContinuousOn m.ρ {0}ᶜ` using `hm.continuousOn.mono fun _ hz => hz`. Use `haveI : IsProbabilityMeasure μ := hg.vol.1`. Establish `hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x)`. Rewrite using `[ae_iff]`.

Conclude with `hg.vol.2.1`. Establish `hbound : ∀ k, ∃ C : ℝ, ∀ z : Ix κ → ℂ, z ≠ 0 → ‖secFun (b k) z‖ ^ 2 * wgt m n z ≤ C`. Introduce `k`. Establish `hdeg : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → ‖secFun (b k) (c • z)‖ ^ 2 * wgt m n (c • z) = ‖secFun (b k) z‖ ^ 2 * wgt m n z`. Introduce `c z hc`.

Establish `hn : ‖c‖ ≠ 0` using `norm_ne_zero_iff.2 hc`. Establish `hpow : ‖c‖ ^ (2 * n) ≠ 0` using `pow_ne_zero _ hn`. Simplify using `only [wgt]`. Rewrite using `[secFun_smul (hb.1 k), m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖c‖), mul_inv, ← pow_mul]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Establish `hcont : ContinuousOn (fun z => ‖secFun (b k) z‖ ^ 2 * wgt m n z) {0}ᶜ`. Use `ContinuousOn.mul ?_ ?_` and prove the remaining obligations. Conclude with `((continuous_secFun (b k)).norm.pow 2).continuousOn`. Conclude with `ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'`.

Establish `hS : IsCompact (Metric.sphere (0 : Ix κ → ℂ) 1)` using `isCompact_sphere 0 1`. Establish `hSsub : Metric.sphere (0 : Ix κ → ℂ) 1 ⊆ {0}ᶜ`. Introduce `z hz h0`. Rewrite `h0` using `[Set.mem_singleton_iff]`. Rewrite `hz` using `[h0, mem_sphere_iff_norm, sub_zero, norm_zero]`.

Conclude with `zero_ne_one hz`. Take `⟨C, hC⟩` from `hS.exists_bound_of_continuousOn (hcont.mono hSsub)`. Use `⟨C, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hnz : ((‖z‖ : ℝ) : ℂ)⁻¹ ≠ 0` using `inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hz)`. Establish `h1` using `hdeg _ z hnz`.

Establish `hz1 : ((‖z‖ : ℝ) : ℂ)⁻¹ • z ∈ Metric.sphere (0 : Ix κ → ℂ) 1`. Rewrite using `[mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]`. Establish `h2` using `hC _ hz1`. Rewrite using `[← h1]`. Conclude with `(le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h2)`.

Take `⟨Ci, hCi⟩` from `hbound i`. Take `⟨Cj, hCj⟩` from `hbound j`. Establish `hρm : Measurable m.ρ`. Establish `h` using `ContinuousOn.measurable_piecewise hρ (by rw [compl_compl]; exact continuousOn_singleton m.ρ 0) (measurableSet_singleton (0 : Ix κ → ℂ)).compl`. Rewrite `h` using `[Set.piecewise_same]`. Then use the resulting hypothesis.

Establish `hw : Measurable (wgt m n)` using `(hρm.pow_const _).inv`. Establish `hF : Measurable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ))` using `((Complex.continuous_conj.comp (continuous_secFun (b i))).mul (continuous_secFun (b j))).measurable.mul (Complex.measurable_ofReal.comp hw)`. Use `Integrable.mono' (integrable_const ((Ci + Cj) / 2)) hF.aestronglyMeasurable ?_` and prove the remaining obligations. Use `filter_upwards [hpts] with z hz`. Establish `hz0 : z ≠ 0` using `hz.1`.

Establish `hwz : 0 ≤ wgt m n z` using `inv_nonneg.2 (pow_nonneg (m.pos z hz0).le _)`. Rewrite using `[norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwz, Complex.norm_conj]`. Establish `e1` using `hCi z hz0`. Establish `e2` using `hCj z hz0`. Use polynomial arithmetic with `[mul_nonneg (sq_nonneg (‖secFun (b i) z‖ - ‖secFun (b j) z‖)) hwz]`.
-/
theorem integrable_secFun {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (i j : Fin r) :
    Integrable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) μ := by
  classical
  have hm : IsSmoothMetric m := hg.semipos.1
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  haveI : IsProbabilityMeasure μ := hg.vol.1
  have hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := by
    rw [ae_iff]
    exact hg.vol.2.1
  have hbound : ∀ k, ∃ C : ℝ, ∀ z : Ix κ → ℂ, z ≠ 0 → ‖secFun (b k) z‖ ^ 2 * wgt m n z ≤ C := by
    intro k
    have hdeg : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 →
        ‖secFun (b k) (c • z)‖ ^ 2 * wgt m n (c • z) = ‖secFun (b k) z‖ ^ 2 * wgt m n z := by
      intro c z hc
      have hn : ‖c‖ ≠ 0 := norm_ne_zero_iff.2 hc
      have hpow : ‖c‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
      simp only [wgt]
      rw [secFun_smul (hb.1 k), m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖c‖), mul_inv, ← pow_mul]
      field_simp
      ring
    have hcont : ContinuousOn (fun z => ‖secFun (b k) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
      refine ContinuousOn.mul ?_ ?_
      · exact ((continuous_secFun (b k)).norm.pow 2).continuousOn
      · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'
    have hS : IsCompact (Metric.sphere (0 : Ix κ → ℂ) 1) := isCompact_sphere 0 1
    have hSsub : Metric.sphere (0 : Ix κ → ℂ) 1 ⊆ {0}ᶜ := by
      intro z hz h0
      rw [Set.mem_singleton_iff] at h0
      rw [h0, mem_sphere_iff_norm, sub_zero, norm_zero] at hz
      exact zero_ne_one hz
    obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (hcont.mono hSsub)
    refine ⟨C, fun z hz => ?_⟩
    have hnz : ((‖z‖ : ℝ) : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast norm_ne_zero_iff.2 hz)
    have h1 := hdeg _ z hnz
    have hz1 : ((‖z‖ : ℝ) : ℂ)⁻¹ • z ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg (norm_nonneg _), inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]
    have h2 := hC _ hz1
    rw [← h1]
    exact (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h2)
  obtain ⟨Ci, hCi⟩ := hbound i
  obtain ⟨Cj, hCj⟩ := hbound j
  have hρm : Measurable m.ρ := by
    have h := ContinuousOn.measurable_piecewise hρ
      (by rw [compl_compl]; exact continuousOn_singleton m.ρ 0)
      (measurableSet_singleton (0 : Ix κ → ℂ)).compl
    rwa [Set.piecewise_same] at h
  have hw : Measurable (wgt m n) := (hρm.pow_const _).inv
  have hF : Measurable (fun z => starRingEnd ℂ (secFun (b i) z) * secFun (b j) z * (wgt m n z : ℂ)) :=
    ((Complex.continuous_conj.comp (continuous_secFun (b i))).mul (continuous_secFun (b j))).measurable.mul
      (Complex.measurable_ofReal.comp hw)
  refine Integrable.mono' (integrable_const ((Ci + Cj) / 2)) hF.aestronglyMeasurable ?_
  filter_upwards [hpts] with z hz
  have hz0 : z ≠ 0 := hz.1
  have hwz : 0 ≤ wgt m n z := inv_nonneg.2 (pow_nonneg (m.pos z hz0).le _)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hwz, Complex.norm_conj]
  have e1 := hCi z hz0
  have e2 := hCj z hz0
  nlinarith [mul_nonneg (sq_nonneg (‖secFun (b i) z‖ - ‖secFun (b j) z‖)) hwz]

/- English proof (translation)
Take `⟨ρ₀, γ, hρ₀, hpar, hγ0⟩` from `exists_isParam hg hz₀`. Take `⟨ν, hν, hνpos, hint⟩` from `hg.vol.2.2 _ γ hpar`. Establish `hmeas : Measurable g` using `measurable_of_continuousOn_compl_singleton 0 hcont`. Establish `h1` using `hint g hmeas hdeg hnn`. Establish `h0 : ∫⁻ z in coneOver (Metric.ball 0 ρ₀) γ, ENNReal.ofReal (g z) ∂μ = 0`.

Rewrite using `[lintegral_congr_ae (g := fun _ => 0)]`. Simplify using the standard rewrite rules. Conclude with `ae_restrict_of_ae (hae.mono fun z hz => by simp [hz])`. Rewrite `h1` using `[h0]`. Use `set U := Metric.ball (0 : Fin D → ℂ) ρ₀ with hUdef`.

Establish `hγc : ContinuousOn γ U` using `hpar.2.1.continuousOn`. Establish `hγne : Set.MapsTo γ U ({0}ᶜ : Set (Ix κ → ℂ))` using `fun y hy => (hpar.2.2.1 y hy).1`. Establish `hφc : ContinuousOn (fun y => g (γ y) * ν y) U` using `(hcont.comp hγc hγne).mul hν.continuousOn`. Establish `hU0 : (0 : Fin D → ℂ) ∈ U` using `Metric.mem_ball_self hρ₀`. Assume the negation of the conclusion as `hne`.

Establish `hpos : 0 < g (γ 0) * ν 0`. Rewrite using `[hγ0]`. Conclude with `mul_pos (lt_of_le_of_ne (hnn _) (Ne.symm hne)) (hνpos 0 hU0)`. Establish `hev : ∀ᶠ y in nhds (0 : Fin D → ℂ), 0 < g (γ y) * ν y` using `(hφc.continuousAt (Metric.isOpen_ball.mem_nhds hU0)).eventually (lt_mem_nhds hpos)`. Take `⟨V, hVsub, hVo, hV0⟩` from `mem_nhds_iff.mp (Filter.inter_mem hev (Metric.isOpen_ball.mem_nhds hU0))`.

Establish `hae2` using `(lintegral_eq_zero_iff' (hφc.aemeasurable measurableSet_ball).ennreal_ofReal).mp h1.symm`. Establish `hae3 : ∀ᵐ y ∂(volume : Measure (Fin D → ℂ)), y ∈ U → ENNReal.ofReal (g (γ y) * ν y) = 0` using `(ae_restrict_iff' measurableSet_ball).mp (hae2.mono fun y hy => by simpa using hy)`. Establish `hnull : (volume : Measure (Fin D → ℂ)) V = 0`. Use `measure_mono_null (fun y hy => ?_) (ae_iff.mp hae3)` and prove the remaining obligations. Take `⟨hy1, hy2⟩` from `hVsub hy`.

Conclude with `fun h => (ENNReal.ofReal_pos.mpr hy1).ne' (h hy2)`. Conclude with `hVo.measure_ne_zero volume ⟨0, hV0⟩ hnull`.
-/
theorem eq_zero_of_ae_zero {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {g : (Ix κ → ℂ) → ℝ} (hcont : ContinuousOn g {0}ᶜ) (hdeg : IsDegZero g)
    (hnn : ∀ z, 0 ≤ g z) (hae : g =ᵐ[μ] 0) {z₀ : Ix κ → ℂ} (hz₀ : z₀ ∈ pts (coordIdeal ℤ x)) :
    g z₀ = 0 := by
  obtain ⟨ρ₀, γ, hρ₀, hpar, hγ0⟩ := exists_isParam hg hz₀
  obtain ⟨ν, hν, hνpos, hint⟩ := hg.vol.2.2 _ γ hpar
  have hmeas : Measurable g := measurable_of_continuousOn_compl_singleton 0 hcont
  have h1 := hint g hmeas hdeg hnn
  have h0 : ∫⁻ z in coneOver (Metric.ball 0 ρ₀) γ, ENNReal.ofReal (g z) ∂μ = 0 := by
    rw [lintegral_congr_ae (g := fun _ => 0)]
    · simp
    · exact ae_restrict_of_ae (hae.mono fun z hz => by simp [hz])
  rw [h0] at h1
  set U := Metric.ball (0 : Fin D → ℂ) ρ₀ with hUdef
  have hγc : ContinuousOn γ U := hpar.2.1.continuousOn
  have hγne : Set.MapsTo γ U ({0}ᶜ : Set (Ix κ → ℂ)) := fun y hy => (hpar.2.2.1 y hy).1
  have hφc : ContinuousOn (fun y => g (γ y) * ν y) U := (hcont.comp hγc hγne).mul hν.continuousOn
  have hU0 : (0 : Fin D → ℂ) ∈ U := Metric.mem_ball_self hρ₀
  by_contra hne
  have hpos : 0 < g (γ 0) * ν 0 := by
    rw [hγ0]
    exact mul_pos (lt_of_le_of_ne (hnn _) (Ne.symm hne)) (hνpos 0 hU0)
  have hev : ∀ᶠ y in nhds (0 : Fin D → ℂ), 0 < g (γ y) * ν y :=
    (hφc.continuousAt (Metric.isOpen_ball.mem_nhds hU0)).eventually (lt_mem_nhds hpos)
  obtain ⟨V, hVsub, hVo, hV0⟩ :=
    mem_nhds_iff.mp (Filter.inter_mem hev (Metric.isOpen_ball.mem_nhds hU0))
  have hae2 := (lintegral_eq_zero_iff' (hφc.aemeasurable measurableSet_ball).ennreal_ofReal).mp h1.symm
  have hae3 : ∀ᵐ y ∂(volume : Measure (Fin D → ℂ)), y ∈ U → ENNReal.ofReal (g (γ y) * ν y) = 0 :=
    (ae_restrict_iff' measurableSet_ball).mp (hae2.mono fun y hy => by simpa using hy)
  have hnull : (volume : Measure (Fin D → ℂ)) V = 0 := by
    refine measure_mono_null (fun y hy => ?_) (ae_iff.mp hae3)
    obtain ⟨hy1, hy2⟩ := hVsub hy
    exact fun h => (ENNReal.ofReal_pos.mpr hy1).ne' (h hy2)
  exact hVo.measure_ne_zero volume ⟨0, hV0⟩ hnull

/- English proof (translation)
Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[secFun_smul (hb i)]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sum_secFun_smul {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) (a : ℂ) (w : Ix κ → ℂ) :
    ∑ i, c i * secFun (b i) (a • w) = a ^ n * ∑ i, c i * secFun (b i) w := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secFun_smul (hb i)]
  ring

/- English proof (translation)
Introduce `a z ha`. Establish `hn : ‖a‖ ≠ 0` using `norm_ne_zero_iff.2 ha`. Establish `hpow : ‖a‖ ^ (2 * n) ≠ 0` using `pow_ne_zero _ hn`. Simplify using `only [wgt]`. Rewrite using `[sum_secFun_smul hb, m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖a‖), mul_inv, ← pow_mul]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isDegZero_normSq {m : ConeMetric ℂ (Ix κ)} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : ∀ k, ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b k = map (Int.castRingHom ℚ) f)
    (c : Fin r → ℂ) : IsDegZero fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z := by
  intro a z ha
  have hn : ‖a‖ ≠ 0 := norm_ne_zero_iff.2 ha
  have hpow : ‖a‖ ^ (2 * n) ≠ 0 := pow_ne_zero _ hn
  simp only [wgt]
  rw [sum_secFun_smul hb, m.smul, norm_mul, norm_pow, mul_pow, mul_pow (‖a‖), mul_inv, ← pow_mul]
  field_simp
  ring

/- English proof (translation)
Establish `hρ : ContinuousOn m.ρ {0}ᶜ` using `hm.continuousOn.mono fun _ hz => hz`. Use `ContinuousOn.mul ?_ ?_` and prove the remaining obligations. Conclude with `((continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_secFun (b i))).norm.pow 2).continuousOn`. Conclude with `ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'`.
-/
theorem continuousOn_normSq {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) {n r : ℕ}
    (b : Fin r → MvPolynomial (Ix κ) ℚ) (c : Fin r → ℂ) :
    ContinuousOn (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) {0}ᶜ := by
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn.mono fun _ hz => hz
  refine ContinuousOn.mul ?_ ?_
  · exact ((continuous_finset_sum _ fun i _ => continuous_const.mul (continuous_secFun (b i))).norm.pow 2).continuousOn
  · exact ContinuousOn.inv₀ (hρ.pow _) fun z hz => pow_ne_zero _ (m.pos z hz).ne'

/- English proof (translation)
Assume the negation of the conclusion as `h`. Rewrite `h` using `[Set.not_nonempty_iff_eq_empty]`. Take `⟨hprob, hnull, -⟩` from `hg.vol`. Rewrite `hnull` using `[h, Set.compl_empty]`. Use `haveI := hprob`.

Rewrite `hnull` using `[measure_univ]`. Conclude with `one_ne_zero hnull`.
-/
theorem nonempty_pts {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) : (pts (coordIdeal ℤ x)).Nonempty := by
  by_contra h
  rw [Set.not_nonempty_iff_eq_empty] at h
  obtain ⟨hprob, hnull, -⟩ := hg.vol
  rw [h, Set.compl_empty] at hnull
  haveI := hprob
  rw [measure_univ] at hnull
  exact one_ne_zero hnull

/- English proof (translation)
The claim follows from `(LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.2.1`.
-/
theorem linIndep_rat_of_isSecBasis {x : Ix κ → Ω} {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ}
    (hb : IsSecBasis x n b) : LinearIndependent ℚ fun k => aeval x (b k) :=
  (LinearIndependent.iff_fractionRing ℤ ℚ).1 hb.2.1

/- English proof (translation)
Establish `hint` using `integrable_secFun hg hb`. Establish `hρ00 : m.ρ 0 = 0`. Establish `h` using `m.smul 0 0`. Rewrite `h` using `[zero_smul, norm_zero, zero_mul]`. Then use the resulting hypothesis. Establish `hρ0 : ∀ z, 0 ≤ m.ρ z` using `fun z => by`.

Distinguish the cases in `hz : z = 0`. Rewrite using `[hz, hρ00]`. Conclude with `(m.pos z hz).le`. Establish `hwnn : ∀ z, 0 ≤ wgt m n z` using `fun z => inv_nonneg.2 (pow_nonneg (hρ0 z) _)`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_` and prove the remaining obligations.

Rewrite using `[dot_bGram _ _ _ hint c, Complex.zero_lt_real]`. Establish `hgnn : ∀ z, 0 ≤ ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z` using `fun z => mul_nonneg (sq_nonneg _) (hwnn z)`. Establish `hgint : Integrable (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) μ` using `integrable_normSq_mul μ _ _ hint c`. Assume the negation of the conclusion as `hle`. Use `push_neg at hle`.

Establish `h0 : ∫ z, ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z ∂μ = 0` using `le_antisymm hle (integral_nonneg hgnn)`. Establish `hae` using `(integral_eq_zero_iff_of_nonneg hgnn hgint).1 h0`. Establish `hvan : ∀ z₀ ∈ pts (coordIdeal ℤ x), ∑ i, c i * secFun (b i) z₀ = 0`. Introduce `z₀ hz₀`. Establish `hg0` using `eq_zero_of_ae_zero hg (continuousOn_normSq hg.semipos.1 b c) (isDegZero_normSq hb.1 c) hgnn hae hz₀`.

Establish `hw : 0 < wgt m n z₀` using `inv_pos.2 (pow_pos (m.pos z₀ hz₀.1) _)`. Establish `h1` using `(mul_eq_zero.1 hg0).resolve_right hw.ne'`. Simplify using `using h1`. Apply `hc` to reduce the goal to its premises. Apply `coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb)` to reduce the goal to its premises.

Introduce `z hz`. Distinguish the cases in `hz0 : z = 0`. Take `⟨z₀, hz₀⟩` from `nonempty_pts hg`. Establish `h2` using `sum_secFun_smul hb.1 c 0 z₀`. Rewrite `h2` using `[zero_smul, hvan z₀ hz₀, mul_zero]`.

Rewrite using `[hz0]`. Conclude with `h2`. Conclude with `hvan z ⟨hz0, hz⟩`.
-/
theorem posDef_bGram_secFun {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b) :
    (bGram μ (fun k => secFun (b k)) (wgt m n)).PosDef := by
  have hint := integrable_secFun hg hb
  have hρ00 : m.ρ 0 = 0 := by
    have h := m.smul 0 0
    rwa [zero_smul, norm_zero, zero_mul] at h
  have hρ0 : ∀ z, 0 ≤ m.ρ z := fun z => by
    by_cases hz : z = 0
    · rw [hz, hρ00]
    · exact (m.pos z hz).le
  have hwnn : ∀ z, 0 ≤ wgt m n z := fun z => inv_nonneg.2 (pow_nonneg (hρ0 z) _)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (bGram_isHermitian _ _ _) fun c hc => ?_
  rw [dot_bGram _ _ _ hint c, Complex.zero_lt_real]
  have hgnn : ∀ z, 0 ≤ ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z :=
    fun z => mul_nonneg (sq_nonneg _) (hwnn z)
  have hgint : Integrable (fun z => ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z) μ :=
    integrable_normSq_mul μ _ _ hint c
  by_contra hle
  push_neg at hle
  have h0 : ∫ z, ‖∑ i, c i * secFun (b i) z‖ ^ 2 * wgt m n z ∂μ = 0 :=
    le_antisymm hle (integral_nonneg hgnn)
  have hae := (integral_eq_zero_iff_of_nonneg hgnn hgint).1 h0
  have hvan : ∀ z₀ ∈ pts (coordIdeal ℤ x), ∑ i, c i * secFun (b i) z₀ = 0 := by
    intro z₀ hz₀
    have hg0 := eq_zero_of_ae_zero hg (continuousOn_normSq hg.semipos.1 b c) (isDegZero_normSq hb.1 c)
      hgnn hae hz₀
    have hw : 0 < wgt m n z₀ := inv_pos.2 (pow_pos (m.pos z₀ hz₀.1) _)
    have h1 := (mul_eq_zero.1 hg0).resolve_right hw.ne'
    simpa using h1
  apply hc
  apply coeff_eq_zero_of_vanish (linIndep_rat_of_isSecBasis hb)
  intro z hz
  by_cases hz0 : z = 0
  · obtain ⟨z₀, hz₀⟩ := nonempty_pts hg
    have h2 := sum_secFun_smul hb.1 c 0 z₀
    rw [zero_smul, hvan z₀ hz₀, mul_zero] at h2
    rw [hz0]
    exact h2
  · exact hvan z ⟨hz0, hz⟩

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [bGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]`. Establish `hae : (fun z => starRingEnd ℂ (s' i z) * s' j z * (w z : ℂ)) =ᵐ[μ] fun z => ∑ k, ∑ l, ((A i k : ℂ) * (A j l : ℂ)) * (starRingEnd ℂ (s k z) * s l z * (w z : ℂ))` using `by filter_upwards [hs i, hs j] with z hi hj`. Rewrite using `[hi, hj]`. Simplify using `only [map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`. Rewrite using `[integral_congr_ae hae, integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => (hint k l).const_mul _)]`. Repeatedly rewrite using `[integral_finset_sum _ (fun l _ => (hint _ l).const_mul _), integral_const_mul]`. Simplify using `only [Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring`.
-/
theorem bGram_change {J : Type} {μ : Measure (J → ℂ)} {r : ℕ} (s s' : Fin r → (J → ℂ) → ℂ)
    (w : (J → ℂ) → ℝ) (A : Matrix (Fin r) (Fin r) ℤ)
    (hint : ∀ i j, Integrable (fun z => starRingEnd ℂ (s i z) * s j z * (w z : ℂ)) μ)
    (hs : ∀ k, s' k =ᵐ[μ] fun z => ∑ l, (A k l : ℂ) * s l z) :
    bGram μ s' w = A.map (Int.cast : ℤ → ℂ) * bGram μ s w * (A.map (Int.cast : ℤ → ℂ)).transpose := by
  ext i j
  simp only [bGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  have hae : (fun z => starRingEnd ℂ (s' i z) * s' j z * (w z : ℂ)) =ᵐ[μ]
      fun z => ∑ k, ∑ l, ((A i k : ℂ) * (A j l : ℂ)) * (starRingEnd ℂ (s k z) * s l z * (w z : ℂ)) := by
    filter_upwards [hs i, hs j] with z hi hj
    rw [hi, hj]
    simp only [map_sum, map_mul, map_intCast, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  rw [integral_congr_ae hae,
    integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun l _ => (hint k l).const_mul _)]
  simp_rw [integral_finset_sum _ (fun l _ => (hint _ l).const_mul _), integral_const_mul]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/- English proof (translation)
Establish `hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x)`. Rewrite using `[ae_iff]`. Conclude with `hg.vol.2.1`. Establish `hmem : ∀ k, ∃ a : Fin r → ℤ, ∑ l, a l • aeval x (b l) = aeval x (b' k)`. Introduce `k`.

Establish `hk : aeval x (b' k) ∈ sec ℤ x n`. Rewrite using `[← hb'.2.2]`. Conclude with `Submodule.subset_span ⟨k, rfl⟩`. Rewrite `hk` using `[← hb.2.2, Submodule.mem_span_range_iff_exists_fun]`. Conclude with `hk`.

Use `choose A hA using hmem`. Use `choose f hfh hf using hb.1`. Establish `hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g`. Introduce `g`. Rewrite using `[← algebraMap_int_eq, aeval_map_algebraMap]`.

Use `⟨Matrix.of A, fun k => ?_⟩` and prove the remaining obligations. Take `⟨f', hf'h, hf'⟩` from `hb'.1 k`. Set `d : MvPolynomial (Ix κ) ℤ` to `f' - ∑ l, C (A k l) * f l`. Establish `hdh : d.IsHomogeneous n`. Rewrite using `[← mem_homogeneousSubmodule]`.

Use `Submodule.sub_mem _ ((mem_homogeneousSubmodule n _).2 hf'h) (Submodule.sum_mem _ fun l _ => (mem_homogeneousSubmodule n _).2 ((hfh l).C_mul _))` and prove the remaining obligations. Establish `hd0 : aeval x d = 0`. Establish `e1 : aeval x f' = aeval x (b' k)` using `by rw [hf', hcast]`. Establish `e2 : ∀ l, aeval x (f l) = aeval x (b l)` using `fun l => by rw [hf l, hcast]`. Simplify using `only [d, map_sub, map_sum, map_mul, aeval_C, algebraMap_int_eq, eq_intCast, map_intCast, e1, e2]`.

Rewrite using `[← hA k, sub_eq_zero]`. Conclude with `Finset.sum_congr rfl fun l _ => zsmul_eq_mul _ _`. Use `filter_upwards [hpts] with z hz`. Establish `h` using `secFun_eq_zero_of_pts hdh hd0 hz`. Rewrite `h` using `[secFun_map_int]`.

Simplify using `only [d, map_sub, map_sum, map_mul, map_C, eval_sub, eval_sum, eval_mul, eval_C, eq_intCast, map_intCast] at h`. Rewrite using `[hf', secFun_map_int]`. Simplify using `only [Matrix.of_apply, hf, secFun_map_int]`. Take the linear combination `h`.
-/
theorem ae_secFun_change {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b b' : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (hb' : IsSecBasis x n b') :
    ∃ A : Matrix (Fin r) (Fin r) ℤ, ∀ k, (fun z => secFun (b' k) z) =ᵐ[μ]
      fun z => ∑ l, (A k l : ℂ) * secFun (b l) z := by
  classical
  have hpts : ∀ᵐ z ∂μ, z ∈ pts (coordIdeal ℤ x) := by
    rw [ae_iff]
    exact hg.vol.2.1
  have hmem : ∀ k, ∃ a : Fin r → ℤ, ∑ l, a l • aeval x (b l) = aeval x (b' k) := by
    intro k
    have hk : aeval x (b' k) ∈ sec ℤ x n := by
      rw [← hb'.2.2]
      exact Submodule.subset_span ⟨k, rfl⟩
    rw [← hb.2.2, Submodule.mem_span_range_iff_exists_fun] at hk
    exact hk
  choose A hA using hmem
  choose f hfh hf using hb.1
  have hcast : ∀ g : MvPolynomial (Ix κ) ℤ, aeval x (map (Int.castRingHom ℚ) g) = aeval x g := by
    intro g
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  refine ⟨Matrix.of A, fun k => ?_⟩
  obtain ⟨f', hf'h, hf'⟩ := hb'.1 k
  let d : MvPolynomial (Ix κ) ℤ := f' - ∑ l, C (A k l) * f l
  have hdh : d.IsHomogeneous n := by
    rw [← mem_homogeneousSubmodule]
    refine Submodule.sub_mem _ ((mem_homogeneousSubmodule n _).2 hf'h)
      (Submodule.sum_mem _ fun l _ => (mem_homogeneousSubmodule n _).2 ((hfh l).C_mul _))
  have hd0 : aeval x d = 0 := by
    have e1 : aeval x f' = aeval x (b' k) := by rw [hf', hcast]
    have e2 : ∀ l, aeval x (f l) = aeval x (b l) := fun l => by rw [hf l, hcast]
    simp only [d, map_sub, map_sum, map_mul, aeval_C, algebraMap_int_eq, eq_intCast, map_intCast, e1, e2]
    rw [← hA k, sub_eq_zero]
    exact Finset.sum_congr rfl fun l _ => zsmul_eq_mul _ _
  filter_upwards [hpts] with z hz
  have h := secFun_eq_zero_of_pts hdh hd0 hz
  rw [secFun_map_int] at h
  simp only [d, map_sub, map_sum, map_mul, map_C, eval_sub, eval_sum, eval_mul, eval_C, eq_intCast,
    map_intCast] at h
  rw [hf', secFun_map_int]
  simp only [Matrix.of_apply, hf, secFun_map_int]
  linear_combination h

/- English proof (translation)
Take `⟨A, hA⟩` from `ae_secFun_change hg hb hb'`. Take `⟨B, hB⟩` from `ae_secFun_change hg hb' hb`. Establish `h1` using `bGram_change _ _ (wgt m n) A (integrable_secFun hg hb) hA`. Establish `h2` using `bGram_change _ _ (wgt m n) B (integrable_secFun hg hb') hB`. Establish `hG0 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det ≠ 0` using `(posDef_bGram_secFun hg hb).det_pos.ne'`.

Establish `hcast : ∀ M : Matrix (Fin r) (Fin r) ℤ, (M.map (Int.cast : ℤ → ℂ)).det = ((M.det : ℤ) : ℂ)` using `fun M => (RingHom.map_det (Int.castRingHom ℂ) M).symm`. Establish `e1 : (bGram μ (fun k => secFun (b' k)) (wgt m n)).det = ((A.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b k)) (wgt m n)).det`. Rewrite using `[h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det = ((B.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b' k)) (wgt m n)).det`.

Rewrite using `[h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ((A.det : ℤ) : ℂ) ^ 2 * ((B.det : ℤ) : ℂ) ^ 2 = 1`. Establish `h` using `e2`. Rewrite `h` using `[e1]`.

Establish `h3 : (((B.det : ℤ) : ℂ) ^ 2 * ((A.det : ℤ) : ℂ) ^ 2 - 1) * (bGram μ (fun k => secFun (b k)) (wgt m n)).det = 0`. Take the linear combination `(-1 : ℂ) * h`. Establish `h4` using `(mul_eq_zero.1 h3).resolve_right hG0`. Take the linear combination `h4`. Establish `keyZ : A.det ^ 2 * B.det ^ 2 = 1` using `by exact_mod_cast key`.

Establish `hA2 : A.det ^ 2 = 1` using `Int.eq_one_of_mul_eq_one_right (sq_nonneg _) keyZ`. Establish `hA2' : ((A.det : ℤ) : ℂ) ^ 2 = 1` using `by exact_mod_cast hA2`. Rewrite using `[e1, hA2', one_mul]`.
-/
theorem det_bGram_eq {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b b' : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b)
    (hb' : IsSecBasis x n b') :
    (bGram μ (fun k => secFun (b' k)) (wgt m n)).det =
      (bGram μ (fun k => secFun (b k)) (wgt m n)).det := by
  obtain ⟨A, hA⟩ := ae_secFun_change hg hb hb'
  obtain ⟨B, hB⟩ := ae_secFun_change hg hb' hb
  have h1 := bGram_change _ _ (wgt m n) A (integrable_secFun hg hb) hA
  have h2 := bGram_change _ _ (wgt m n) B (integrable_secFun hg hb') hB
  have hG0 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det ≠ 0 :=
    (posDef_bGram_secFun hg hb).det_pos.ne'
  have hcast : ∀ M : Matrix (Fin r) (Fin r) ℤ, (M.map (Int.cast : ℤ → ℂ)).det = ((M.det : ℤ) : ℂ) :=
    fun M => (RingHom.map_det (Int.castRingHom ℂ) M).symm
  have e1 : (bGram μ (fun k => secFun (b' k)) (wgt m n)).det =
      ((A.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b k)) (wgt m n)).det := by
    rw [h1, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]
    ring
  have e2 : (bGram μ (fun k => secFun (b k)) (wgt m n)).det =
      ((B.det : ℤ) : ℂ) ^ 2 * (bGram μ (fun k => secFun (b' k)) (wgt m n)).det := by
    rw [h2, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hcast]
    ring
  have key : ((A.det : ℤ) : ℂ) ^ 2 * ((B.det : ℤ) : ℂ) ^ 2 = 1 := by
    have h := e2
    rw [e1] at h
    have h3 : (((B.det : ℤ) : ℂ) ^ 2 * ((A.det : ℤ) : ℂ) ^ 2 - 1) *
        (bGram μ (fun k => secFun (b k)) (wgt m n)).det = 0 := by
      linear_combination (-1 : ℂ) * h
    have h4 := (mul_eq_zero.1 h3).resolve_right hG0
    linear_combination h4
  have keyZ : A.det ^ 2 * B.det ^ 2 = 1 := by exact_mod_cast key
  have hA2 : A.det ^ 2 = 1 := Int.eq_one_of_mul_eq_one_right (sq_nonneg _) keyZ
  have hA2' : ((A.det : ℤ) : ℂ) ^ 2 = 1 := by exact_mod_cast hA2
  rw [e1, hA2', one_mul]

/- English proof (translation)
Establish `hmat : bGram μ (fun k => secFun (b k)) (wgt m n) = (realGram (K` using `ℚ) (fun _ => m) (fun _ => μ) n b).map Complex.ofRealHom := by`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, realGram_eq]`. Conclude with `((Complex.conj_eq_iff_re.1 (conj_bGram hm hμ n b i j)).symm)`. Rewrite using `[hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]`.

Both sides reduce to the same expression.
-/
theorem realGram_det {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)} (hm : IsConjInvariant m)
    (hμ : μ.map conjPt = μ) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Ix κ) ℚ) :
    (realGram (K := ℚ) (fun _ => m) (fun _ => μ) n b).det =
      (bGram μ (fun k => secFun (b k)) (wgt m n)).det.re := by
  have hmat : bGram μ (fun k => secFun (b k)) (wgt m n) =
      (realGram (K := ℚ) (fun _ => m) (fun _ => μ) n b).map Complex.ofRealHom := by
    ext i j
    rw [Matrix.map_apply, realGram_eq]
    exact ((Complex.conj_eq_iff_re.1 (conj_bGram hm hμ n b i j)).symm)
  rw [hmat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  rfl

/- English proof (translation)
Establish `hex : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n p.2` using `⟨⟨r, b⟩, hb⟩`. Establish `hspec` using `hex.choose_spec`. Rewrite using `[chi, dif_pos hex]`. Break down `hp : hex.choose with ⟨r', b'⟩` into its components or cases. Rewrite `hspec` using `[hp]`.

Establish `hr : r' = r` using `(IsSecBasis.card_eq hspec).trans (IsSecBasis.card_eq hb).symm`. Substitute `hr` using the available equality. Simplify using `only [l2Degree]`. Rewrite using `[realGram_det hg.conjM hg.conjMu n b', det_bGram_eq hg hb hspec, NumberField.totalWeight_eq_finrank, Module.finrank_self]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem chi_eq {x : Ix κ → Ω} {m : ConeMetric ℂ (Ix κ)} {μ : Measure (Ix κ → ℂ)}
    (hg : IsGood D x m μ) {n r : ℕ} {b : Fin r → MvPolynomial (Ix κ) ℚ} (hb : IsSecBasis x n b) :
    chi x m μ n = -(1 / 2) * Real.log (bGram μ (fun k => secFun (b k)) (wgt m n)).det.re := by
  have hex : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis x n p.2 := ⟨⟨r, b⟩, hb⟩
  have hspec := hex.choose_spec
  rw [chi, dif_pos hex]
  rcases hp : hex.choose with ⟨r', b'⟩
  rw [hp] at hspec
  have hr : r' = r := (IsSecBasis.card_eq hspec).trans (IsSecBasis.card_eq hb).symm
  subst hr
  simp only [l2Degree]
  rw [realGram_det hg.conjM hg.conjMu n b', det_bGram_eq hg hb hspec,
    NumberField.totalWeight_eq_finrank, Module.finrank_self]
  push_cast
  ring

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
