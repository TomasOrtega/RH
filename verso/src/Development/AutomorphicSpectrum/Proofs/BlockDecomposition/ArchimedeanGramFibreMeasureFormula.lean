import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitHermOfDet
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensor
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorel
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramRightActionIdentities
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUniqueSquareRootNearOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLowerBoundNearInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LintegralUniformNearParameterStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsBumpWithNonzeroIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibrationUniqueStatement
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal NNReal Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.FibN

/- English proof (translation)
Introduce `B V _ _ _ _ _ _ ψ hψ hψ' ad hadc hmul h1 c ci hc1 hc2 hcs`. Take `⟨r, U, hU, hr1, hr2, hinj⟩` from `GlobalTheory.T.local_unique_square_root_near_one B V ψ hψ hψ'`. Establish `hci : ad ci = ci`. Establish `h2 : ad ci * c = 1` using `by rw [← h1, ← hc1, hmul, hcs]`. Combine the equalities or inequalities in the displayed calculation.

Set `θ : B → B` to `fun x => ci * ad x * c`. Establish `hθc : Continuous θ` using `(continuous_const.mul hadc).mul continuous_const`. Establish `hθ1 : θ 1 = 1` using `by simp only [θ, h1, mul_one, hc2]`. Establish `hθm : ∀ x y, θ (x * y) = θ y * θ x`. Introduce `x y`.

Simplify using `only [θ, hmul]`. Combine the equalities or inequalities in the displayed calculation. Set `F : Filter B` to `nhdsWithin c {s | ad s = s}`. Establish `hp : Filter.Tendsto (fun s => ci * s) F (nhds 1)`. Establish `h2 : Filter.Tendsto (fun s => ci * s) (nhds c) (nhds (ci * c))` using `(continuous_const.mul continuous_id).tendsto c`.

Rewrite `h2` using `[hc2]`. Conclude with `h2.mono_left nhdsWithin_le_nhds`. Establish `ht : Filter.Tendsto (fun s => r (ci * s)) F (nhds 1)` using `hr1.comp hp`. Establish `hθt : Filter.Tendsto (fun s => θ (r (ci * s))) F (nhds 1)`. Establish `h2` using `(hθc.tendsto 1).comp ht`.

Rewrite `h2` using `[hθ1]`. Then use the resulting hypothesis. Use `⟨fun s => r (ci * s), ht, ?_⟩` and prove the remaining obligations. Establish `hself : ∀ᶠ s in F, ad s = s` using `self_mem_nhdsWithin`. Use `filter_upwards [hp.eventually hr2, ht.eventually hU, hθt.eventually hU, hself] with s e1 e2 e3 e4`. Use `set g := r (ci * s) with hg`.

Establish `hθh : θ (ci * s) = ci * s`. Simplify using `only [θ, hmul, hci, e4]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : θ g * θ g = g * g` using `by rw [← hθm, e1, hθh]`. Establish `hfix : θ g = g` using `hinj _ e3 _ e2 hsq`.

Establish `hcg : ad g * c = c * g`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem orbit_section : ∀ (B V : Type) [Ring B] [TopologicalSpace B] [IsTopologicalRing B] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (ψ : B ≃+ V), Continuous ψ → Continuous ψ.symm → ∀ (ad : B → B), Continuous ad → (∀ x y, ad (x * y) = ad y * ad x) → ad 1 = 1 → ∀ (c ci : B), c * ci = 1 → ci * c = 1 → ad c = c → ∃ t : B → B, Filter.Tendsto t (nhdsWithin c {s | ad s = s}) (nhds 1) ∧ ∀ᶠ s in nhdsWithin c {s | ad s = s}, ad (t s) * c * t s = s := by
  intro B V _ _ _ _ _ _ ψ hψ hψ' ad hadc hmul h1 c ci hc1 hc2 hcs
  obtain ⟨r, U, hU, hr1, hr2, hinj⟩ := GlobalTheory.T.local_unique_square_root_near_one B V ψ hψ hψ'
  have hci : ad ci = ci := by
    have h2 : ad ci * c = 1 := by rw [← h1, ← hc1, hmul, hcs]
    calc ad ci = ad ci * (c * ci) := by rw [hc1, mul_one]
      _ = ci := by rw [← mul_assoc, h2, one_mul]
  let θ : B → B := fun x => ci * ad x * c
  have hθc : Continuous θ := (continuous_const.mul hadc).mul continuous_const
  have hθ1 : θ 1 = 1 := by simp only [θ, h1, mul_one, hc2]
  have hθm : ∀ x y, θ (x * y) = θ y * θ x := by
    intro x y
    simp only [θ, hmul]
    calc ci * (ad y * ad x) * c = ci * ad y * 1 * ad x * c := by simp only [mul_one, mul_assoc]
      _ = ci * ad y * (c * ci) * ad x * c := by rw [hc1]
      _ = _ := by simp only [mul_assoc]
  let F : Filter B := nhdsWithin c {s | ad s = s}
  have hp : Filter.Tendsto (fun s => ci * s) F (nhds 1) := by
    have h2 : Filter.Tendsto (fun s => ci * s) (nhds c) (nhds (ci * c)) :=
      (continuous_const.mul continuous_id).tendsto c
    rw [hc2] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have ht : Filter.Tendsto (fun s => r (ci * s)) F (nhds 1) := hr1.comp hp
  have hθt : Filter.Tendsto (fun s => θ (r (ci * s))) F (nhds 1) := by
    have h2 := (hθc.tendsto 1).comp ht
    rwa [hθ1] at h2
  refine ⟨fun s => r (ci * s), ht, ?_⟩
  have hself : ∀ᶠ s in F, ad s = s := self_mem_nhdsWithin
  filter_upwards [hp.eventually hr2, ht.eventually hU, hθt.eventually hU, hself] with s e1 e2 e3 e4
  set g := r (ci * s) with hg
  have hθh : θ (ci * s) = ci * s := by
    simp only [θ, hmul, hci, e4]
    calc ci * (s * ci) * c = ci * s * (ci * c) := by simp only [mul_assoc]
      _ = ci * s := by rw [hc2, mul_one]
  have hsq : θ g * θ g = g * g := by rw [← hθm, e1, hθh]
  have hfix : θ g = g := hinj _ e3 _ e2 hsq
  have hcg : ad g * c = c * g := by
    calc ad g * c = (c * ci) * ad g * c := by rw [hc1, one_mul]
      _ = c * θ g := by simp only [θ, mul_assoc]
      _ = c * g := by rw [hfix]
  calc ad g * c * g = c * (g * g) := by rw [hcg, mul_assoc]
    _ = c * (ci * s) := by rw [e1]
    _ = s := by rw [← mul_assoc, hc1, one_mul]

/- English proof (translation)
Use `set k : ℕ := N + 1 with hk`. Use `⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun y => ?_⟩` and prove the remaining obligations. Establish `h1` using `SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f y`. Rewrite `h1` using `[norm_iteratedFDeriv_zero]`. Establish `hy : 0 < 1 + ‖y‖` using `by positivity`.

Rewrite using `[Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`. Combine the linear relations using `[h1, mul_comm (‖f y‖) ((1 + ‖y‖) ^ k)]`.
-/
theorem schwartz_decay {N : ℕ} (f : SchwartzMap (Fin N → ℝ) ℂ) :
    ∃ C : ℝ, ∀ y, ‖f y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
  set k : ℕ := N + 1 with hk
  refine ⟨2 ^ k * ((Finset.Iic (k, 0)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, fun y => ?_⟩
  have h1 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0) le_rfl le_rfl f y
  rw [norm_iteratedFDeriv_zero] at h1
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith [h1, mul_comm (‖f y‖) ((1 + ‖y‖) ^ k)]

/- English proof (translation)
Establish `h1 : HasCompactSupport fun y => v y * (1 + ‖y‖) ^ (N + 1)` using `hs.mul_right`. Take `⟨C, hC⟩` from `h1.exists_bound_of_continuous (hv.mul ((continuous_const.add continuous_norm).pow _))`. Use `⟨C, fun y => ?_⟩` and prove the remaining obligations. Establish `hy : 0 < 1 + ‖y‖` using `by positivity`. Rewrite using `[Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]`.

Establish `h2` using `hC y`. Rewrite `h2` using `[norm_mul, norm_pow, Real.norm_of_nonneg hy.le]`. Simplify using `using h2`.
-/
theorem compact_decay {N : ℕ} (v : (Fin N → ℝ) → ℝ) (hv : Continuous v) (hs : HasCompactSupport v) :
    ∃ C : ℝ, ∀ y, ‖((v y : ℝ) : ℂ)‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ)) := by
  have h1 : HasCompactSupport fun y => v y * (1 + ‖y‖) ^ (N + 1) := hs.mul_right
  obtain ⟨C, hC⟩ := h1.exists_bound_of_continuous
    (hv.mul ((continuous_const.add continuous_norm).pow _))
  refine ⟨C, fun y => ?_⟩
  have hy : 0 < 1 + ‖y‖ := by positivity
  rw [Real.rpow_neg hy.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h2 := hC y
  rw [norm_mul, norm_pow, Real.norm_of_nonneg hy.le] at h2
  simpa using h2

/- English proof (translation)
Introduce `X P _ _ _ _ _ _ N e he hes c m m0 A κ hAc hAt hinj hm hfin χ hχc hχs hχt hχ0 f`. Take `⟨δ, hδ, hlow⟩` from `GlobalTheory.T.uniform_lower_bound_near_injective X P N e he hes c A hAc hAt hinj`. Set `eh : X ≃ₜ (Fin N → ℝ)` to `{ e.toEquiv with continuous_toFun := he, continuous_invFun := hes }`. Set `v : (Fin N → ℝ) → ℝ` to `fun y => χ (e.symm y)`. Establish `hvc : Continuous v` using `hχc.comp hes`.

Establish `hvs : HasCompactSupport v` using `hχs.comp_homeomorph eh.symm`. Set `u : (Fin N → ℝ) → ℂ` to `fun y => ((v y : ℝ) : ℂ)`. Establish `huc : Continuous u` using `Complex.continuous_ofReal.comp hvc`. Take `⟨Cf, hCf⟩` from `schwartz_decay f`. Take `⟨Cu, hCu⟩` from `compact_decay v hvc hvs`.

Take `⟨hI1, hI2⟩` from `GlobalTheory.T.lintegral_uniform_near_parameter X P N e he c m0 A hAc hAt δ hδ hlow hfin f Cf f.continuous hCf`. Take `⟨-, hJ2⟩` from `GlobalTheory.T.lintegral_uniform_near_parameter X P N e he c m0 A hAc hAt δ hδ hlow hfin u Cu huc hCu`. Establish `hAm : ∀ s, Measurable (A s)` using `fun s => (hAc s).measurable`. Establish `key : ∀ (G : X → ℂ), Continuous G → ∀ s, m s = κ s • m0.map (A s) → ∫ x, G x ∂(m s) = (κ s : ℂ) * ∫ x, G (A s x) ∂m0`. Introduce `G hG s hs`.

Rewrite using `[hs, integral_smul_nnreal_measure, integral_map (hAm s).aemeasurable hG.measurable.aestronglyMeasurable, NNReal.smul_def, Complex.real_smul]`. Set `Jc : P → ℂ` to `fun s => ∫ x, u (e (A s x)) ∂m0`. Set `If : P → ℂ` to `fun s => ∫ x, f (e (A s x)) ∂m0`. Establish `hGχ : Continuous fun x => ((χ x : ℝ) : ℂ)` using `Complex.continuous_ofReal.comp hχc`. Establish `hRJ : ∀ s, m s = κ s • m0.map (A s) → ((∫ x, χ x ∂(m s) : ℝ) : ℂ) = (κ s : ℂ) * Jc s`.

Introduce `s hs`. Rewrite using `[← integral_complex_ofReal, key _ hGχ s hs]`. Use `congr 1`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `[u, v]`.

Establish `hmc` using `hm.self_of_nhds`. Establish `hJ0 : Jc c ≠ 0`. Introduce `h0`. Establish `h1` using `hRJ c hmc`. Rewrite `h1` using `[h0, mul_zero]`.

Conclude with `hχ0 (by exact_mod_cast h1)`. Establish `hGf : Continuous fun x => f (e x)` using `f.continuous.comp he`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hm, hI1] with s hs hint`. Rewrite using `[hs]`.

Conclude with `((integrable_map_measure hGf.measurable.aestronglyMeasurable (hAm s).aemeasurable).2 hint).smul_measure_nnreal`. Establish `hR : ContinuousAt (fun s => ((∫ x, χ x ∂(m s) : ℝ) : ℂ)) c` using `Complex.continuous_ofReal.continuousAt.comp hχt`. Establish `hH : ContinuousAt (fun s => ((∫ x, χ x ∂(m s) : ℝ) : ℂ) / Jc s * If s) c` using `(hR.div hJ2 hJ0).mul hI2`. Use `hH.congr ?_` and prove the remaining obligations. Establish `hJne : ∀ᶠ s in nhds c, Jc s ≠ 0` using `hJ2.eventually_ne hJ0`.

Use `filter_upwards [hm, hJne] with s hs hne`. Rewrite using `[hRJ s hs, key _ hGf s hs, mul_div_cancel_right₀ _ hne]`.
-/
theorem family_core : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (m : P → Measure X) (m0 : Measure X) (A : P → X →+ X) (κ : P → ℝ≥0), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → (∀ᶠ s in nhds c, m s = κ s • m0.map (A s)) → ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ → ∀ χ : X → ℝ, Continuous χ → HasCompactSupport χ → ContinuousAt (fun s => ∫ x, χ x ∂(m s)) c → ∫ x, χ x ∂(m c) ≠ 0 → ∀ f : SchwartzMap (Fin N → ℝ) ℂ, (∀ᶠ s in nhds c, Integrable (fun x => f (e x)) (m s)) ∧ ContinuousAt (fun s => ∫ x, f (e x) ∂(m s)) c := by
  intro X P _ _ _ _ _ _ N e he hes c m m0 A κ hAc hAt hinj hm hfin χ hχc hχs hχt hχ0 f
  obtain ⟨δ, hδ, hlow⟩ := GlobalTheory.T.uniform_lower_bound_near_injective X P N e he hes c A hAc hAt hinj
  let eh : X ≃ₜ (Fin N → ℝ) := { e.toEquiv with continuous_toFun := he, continuous_invFun := hes }
  let v : (Fin N → ℝ) → ℝ := fun y => χ (e.symm y)
  have hvc : Continuous v := hχc.comp hes
  have hvs : HasCompactSupport v := hχs.comp_homeomorph eh.symm
  let u : (Fin N → ℝ) → ℂ := fun y => ((v y : ℝ) : ℂ)
  have huc : Continuous u := Complex.continuous_ofReal.comp hvc
  obtain ⟨Cf, hCf⟩ := schwartz_decay f
  obtain ⟨Cu, hCu⟩ := compact_decay v hvc hvs
  obtain ⟨hI1, hI2⟩ := GlobalTheory.T.lintegral_uniform_near_parameter X P N e he c m0 A hAc hAt δ hδ hlow hfin f Cf f.continuous hCf
  obtain ⟨-, hJ2⟩ := GlobalTheory.T.lintegral_uniform_near_parameter X P N e he c m0 A hAc hAt δ hδ hlow hfin u Cu huc hCu
  have hAm : ∀ s, Measurable (A s) := fun s => (hAc s).measurable
  have key : ∀ (G : X → ℂ), Continuous G → ∀ s, m s = κ s • m0.map (A s) →
      ∫ x, G x ∂(m s) = (κ s : ℂ) * ∫ x, G (A s x) ∂m0 := by
    intro G hG s hs
    rw [hs, integral_smul_nnreal_measure,
      integral_map (hAm s).aemeasurable hG.measurable.aestronglyMeasurable, NNReal.smul_def, Complex.real_smul]
  let Jc : P → ℂ := fun s => ∫ x, u (e (A s x)) ∂m0
  let If : P → ℂ := fun s => ∫ x, f (e (A s x)) ∂m0
  have hGχ : Continuous fun x => ((χ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hχc
  have hRJ : ∀ s, m s = κ s • m0.map (A s) → ((∫ x, χ x ∂(m s) : ℝ) : ℂ) = (κ s : ℂ) * Jc s := by
    intro s hs
    rw [← integral_complex_ofReal, key _ hGχ s hs]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp [u, v]
  have hmc := hm.self_of_nhds
  have hJ0 : Jc c ≠ 0 := by
    intro h0
    have h1 := hRJ c hmc
    rw [h0, mul_zero] at h1
    exact hχ0 (by exact_mod_cast h1)
  have hGf : Continuous fun x => f (e x) := f.continuous.comp he
  refine ⟨?_, ?_⟩
  · filter_upwards [hm, hI1] with s hs hint
    rw [hs]
    exact ((integrable_map_measure hGf.measurable.aestronglyMeasurable (hAm s).aemeasurable).2 hint).smul_measure_nnreal
  · have hR : ContinuousAt (fun s => ((∫ x, χ x ∂(m s) : ℝ) : ℂ)) c :=
      Complex.continuous_ofReal.continuousAt.comp hχt
    have hH : ContinuousAt (fun s => ((∫ x, χ x ∂(m s) : ℝ) : ℂ) / Jc s * If s) c :=
      (hR.div hJ2 hJ0).mul hI2
    refine hH.congr ?_
    have hJne : ∀ᶠ s in nhds c, Jc s ≠ 0 := hJ2.eventually_ne hJ0
    filter_upwards [hm, hJne] with s hs hne
    rw [hRJ s hs, key _ hGf s hs, mul_div_cancel_right₀ _ hne]

end GlobalTheory.CompanionTheory.SiegelND.Coef.FibN

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.FibN

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hle : (⊤ : ℝ≥0∞) * ν O ≤ ∫⁻ b, ∫⁻ v, f v ∂(fib b) ∂ν`. Rewrite using `[← lintegral_indicator_const hO]`. Use `lintegral_mono fun S => ?_` and prove the remaining obligations.

Distinguish the cases in `hS : S ∈ O`. Rewrite using `[Set.indicator_of_mem hS, hcon S hS]`. Rewrite using `[Set.indicator_of_notMem hS]`. Conclude with `bot_le`. Rewrite `hle` using `[ENNReal.top_mul hpos, top_le_iff, ← h]`.

Conclude with `hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))`.
-/
theorem exists_fin_point {V P : Type} [MeasurableSpace V] [MeasurableSpace P]
    (μ : Measure V) (ν : Measure P) (U : Set V) (fib : P → Measure V) (f : V → ℝ≥0∞)
    (h : ∫⁻ v in U, f v ∂μ = ∫⁻ b, ∫⁻ v, f v ∂(fib b) ∂ν) (hfin : ∫⁻ v, f v ∂μ ≠ ⊤)
    (O : Set P) (hO : MeasurableSet O) (hpos : ν O ≠ 0) : ∃ s ∈ O, ∫⁻ v, f v ∂(fib s) ≠ ⊤ := by
  by_contra hcon
  push_neg at hcon
  have hle : (⊤ : ℝ≥0∞) * ν O ≤ ∫⁻ b, ∫⁻ v, f v ∂(fib b) ∂ν := by
    rw [← lintegral_indicator_const hO]
    refine lintegral_mono fun S => ?_
    by_cases hS : S ∈ O
    · rw [Set.indicator_of_mem hS, hcon S hS]
    · rw [Set.indicator_of_notMem hS]
      exact bot_le
  rw [ENNReal.top_mul hpos, top_le_iff, ← h] at hle
  exact hfin (top_le_iff.1 (hle ▸ setLIntegral_le_lintegral _ _))

def rmulHom (R : Type) {F E : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) :
    (Fin n → Fin M → R ⊗[F] E) →+ (Fin n → Fin M → R ⊗[F] E) :=
  AddMonoidHom.mk' (fun X => GlobalTheory.CompanionTheory.SW.rmul R X g) (by
    intro X Y
    funext a i
    simp [GlobalTheory.CompanionTheory.SW.rmul, add_mul, Finset.sum_add_distrib])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rmulHom_apply (R : Type) {F E : Type} [Field F] [Field E] [Algebra F E] [CommRing R] [Algebra F R] {M n : ℕ}
    (g : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    rmulHom R g X = GlobalTheory.CompanionTheory.SW.rmul R X g := rfl

def matCoords {K W : Type} [AddCommGroup K] [AddCommGroup W] (ε : K ≃+ W) (n : ℕ) :
    Matrix (Fin n) (Fin n) K ≃+ (Fin n → Fin n → W) where
  toFun X i j := ε (X i j)
  invFun Y i j := ε.symm (Y i j)
  left_inv X := by funext i j; simp
  right_inv Y := by funext i j; simp
  map_add' X Y := by funext i j; simp

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ n hn d b laminf hlam minf hm c hc φ hφ`. Establish `hlH : laminf.IsAddHaarMeasure` using `hlam.1`. Establish `hloc` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1`. Take `⟨ρ, e0, -, he0, -⟩` from `GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1`. Take `⟨hTR, hLC, hSC, hT2, -⟩` from `id hloc`.

Use `haveI := hTR`. Use `haveI := hLC`. Use `haveI := hSC`. Use `haveI := hT2`. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`.

Take `⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)`. Use `haveI := hB n M`. Take `⟨hLH, hSH, hT2H, hBH, -⟩` from `GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n`. Use `haveI := hLH`. Use `haveI := hSH`.

Use `haveI := hT2H`. Use `haveI := hBH`. Take `⟨-, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hlH`. Use `haveI := hW n M`. Use `haveI := hH n`.

Take `⟨halg, hcomp, hone, hmem, -⟩` from `GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hCM M J hJ (Ainf F) n`. Establish `hKu` using `GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM (Ainf F) hloc`. Take `⟨N, e, he, hes, f, hf⟩` from `hφ`. Establish `hφe : φ = fun x => f (e x)` using `funext hf`. Establish `hφc : Continuous φ` using `by rw [hφe]; exact f.continuous.comp he`.

Use `⟨hφc.measurable, ?_⟩` and prove the remaining obligations. Set `H1` to `(hrepr d b).homeomorph`. Set `H2 : (Fin d → Ainf F) ≃ₜ (Fin d → InfinitePlace F → ℝ)` to `Homeomorph.piCongrRight fun _ => he0.homeomorph`. Set `Hc` to `H1.trans H2`. Set `ε : (Ainf F ⊗[F] E) ≃+ (Fin d → InfinitePlace F → ℝ)` to `{ Hc.toEquiv with map_add' := by`.

Introduce `x y`. Use function extensionality and compare the values at `k w`. Use `show e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr (x + y) k) w = e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr x k) w + e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w`. Simplify using `only [map_add, Finsupp.add_apply, Pi.add_apply] }`. Establish `hεc : Continuous ε` using `Hc.continuous`.

Establish `hεs : Continuous ε.symm` using `Hc.symm.continuous`. Set `ψ` to `matCoords ε n`. Establish `hψ : Continuous ψ` using `continuous_pi fun i => continuous_pi fun j => hεc.comp ((continuous_apply j).comp (continuous_apply i))`. Establish `hψ' : Continuous ψ.symm` using `continuous_pi fun i => continuous_pi fun j => hεs.comp ((continuous_apply j).comp (continuous_apply i))`. Set `ad : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)` to `HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ)`.

Establish `hadc : Continuous ad` using `continuous_pi fun i => continuous_pi fun j => hsc.comp ((continuous_apply i).comp (continuous_apply j))`. Establish `hadm : ∀ x y, ad (x * y) = ad y * ad x` using `fun x y => HeckeCharacterZeroLocus.SiegelWeilU.cT_mul _ _ _`. Establish `had1 : ad 1 = 1` using `by show HeckeCharacterZeroLocus.SiegelWeilU.cT _ _ = _`. Unfold `HeckeCharacterZeroLocus.SiegelWeilU.cT`. Rewrite using `[Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]`.

Establish `hherm : ∀ s : HermR (Ainf F) σ n, ad (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = s`. Introduce `s`. Use extensionality with `i j`. Conclude with `s.2 i j`. Take `⟨t, ht1, ht2⟩` from `orbit_section _ _ ψ hψ hψ' ad hadc hadm had1 (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))⁻¹ (Matrix.mul_nonsing_inv _ hc) (Matrix.nonsing_inv_mul _ hc) (hherm c)`.

Establish `hι : Filter.Tendsto (fun s : HermR (Ainf F) σ n => (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) (nhds c) (nhdsWithin (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) {s | ad s = s})` using `tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto c, Filter.Eventually.of_forall hherm⟩`. Establish `hT1` using `ht1.comp hι`. Establish `hT2'` using `hι.eventually ht2`. Set `Bl : Set (HermR (Ainf F) σ n)` to `{S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}`. Establish `hBo : IsOpen Bl`.

Establish `: Bl = (fun S : HermR (Ainf F) σ n => (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det) ⁻¹' Set.range (Units.val : (Ainf F ⊗[F] E)ˣ → Ainf F ⊗[F] E)`. Use extensionality with `S`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hKu.isOpen_range.preimage continuous_subtype_val.matrix_det`.

Establish `hev` using `hT2'.and (hBo.mem_nhds hc)`. Take `⟨O, hOs, hOo, hcO⟩` from `eventually_nhds_iff.1 hev`. Use `set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M with hμ`. Use `set ν := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n with hν`. Establish `hm' : IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | IsUnit (gramR (Ainf F) σ J X).det} ν Bl minf` using `hm`.

Use `haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes`. Set `W0 : (Fin N → ℝ) → ℝ` to `fun y => (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))`. Establish `hW0m : Measurable W0` using `(measurable_const.add measurable_norm).pow_const _`. Establish `hWi : Integrable W0 (μ.map e)` using `integrable_one_add_norm (by simp)`. Establish `hlin : ∫⁻ x, ENNReal.ofReal (W0 (e x)) ∂μ ≠ ⊤`.

Establish `h1` using `((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).1 hWi.2).ne`. Rewrite `h1` using `[lintegral_map (f := fun y => ENNReal.ofReal (W0 y)) (ENNReal.measurable_ofReal.comp hW0m) he.measurable]`. Then use the resulting hypothesis. Establish `hOm : MeasurableSet O` using `MeasurableSpace.measurableSet_generateFrom hOo`. Establish `hOp : ν O ≠ 0` using `(hH n).toIsOpenPosMeasure.open_pos O hOo ⟨c, hcO⟩`. Take `⟨s0, hs0O, hs0fin⟩` from `exists_fin_point μ ν _ minf (fun x => ENNReal.ofReal (W0 (e x))) (hm'.2.1 _ (ENNReal.measurable_ofReal.comp (hW0m.comp he.measurable))) hlin O hOm hOp`.

Establish `hdetO : ∀ s ∈ O, IsUnit (t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det`. Introduce `s hs`. Establish `h1` using `(hOs s hs).1`. Establish `h2 : IsUnit (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det` using `(hOs s hs).2`. Establish `h3 : IsUnit (ad (t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) * (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det`.

Rewrite using `[h1]`. Conclude with `h2`. Rewrite `h3` using `[Matrix.det_mul]`. Conclude with `isUnit_of_mul_isUnit_right h3`. Use `set g0 := t (s0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) with hg0`.

Establish `hg0d : IsUnit g0.det` using `hdetO s0 hs0O`. Establish `hgi1 : g0 * g0⁻¹ = 1` using `Matrix.mul_nonsing_inv g0 hg0d`. Establish `hgi2 : g0⁻¹ * g0 = 1` using `Matrix.nonsing_inv_mul g0 hg0d`. Establish `hgid : IsUnit (g0⁻¹).det` using `Matrix.isUnit_nonsing_inv_det g0 hg0d`. Set `A : HermR (Ainf F) σ n → (Fin n → Fin M → Ainf F ⊗[F] E) →+ (Fin n → Fin M → Ainf F ⊗[F] E)` to `fun s => rmulHom (Ainf F) (g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)))`.

Establish `hκ : ∀ s ∈ O, ∃ κ : ℝ≥0, κ ≠ 0 ∧ minf s = κ • (minf s0).map (A s)`. Introduce `s hs`. Establish `hd : IsUnit (g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det`. Rewrite using `[Matrix.det_mul]`. Conclude with `hgid.mul (hdetO s hs)`.

Take `⟨κ, hκ0, hκ⟩` from `GlobalTheory.T.local_gram_fibration_unique F E σ hCM M J hJ (Ainf F) hloc n μ ν minf (hW n M) (hH n) hm _ hd`. Use `⟨κ, hκ0, hκ s0 s ?_⟩` and prove the remaining obligations. Use `show (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ad _ * _ * _`. Establish `h0 : (s0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ad g0 * c * g0` using `(hOs s0 hs0O).1.symm`. Establish `h1 : ad g0⁻¹ * ad g0 = 1` using `by rw [← hadm, hgi1, had1]`.

Rewrite using `[hadm, h0]`. Combine the equalities or inequalities in the displayed calculation. Use `choose! κ hκ0 hκ using hκ`. Use `haveI : T2Space (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := inferInstanceAs (T2Space (Fin n → Fin n → Ainf F ⊗[F] E))`. Establish `htc : t (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = 1` using `tendsto_nhds_unique (tendsto_pure_nhds _ c) (hT1.mono_left (pure_le_nhds c))`.

Establish `hrc : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E), Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h`. Introduce `h`. Use `continuous_pi fun b => continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [GlobalTheory.CompanionTheory.SW.rmul]`. Use `continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations.

Establish `h1 : Continuous fun Y : Fin n → Fin M → Ainf F ⊗[F] E => Y k i` using `(continuous_apply i).comp (continuous_apply k)`. Conclude with `h1.mul continuous_const`. Establish `hrg : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E, Continuous fun h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h`. Introduce `X`. Use `continuous_pi fun b => continuous_pi fun i => ?_` and prove the remaining obligations.

Simplify using `only [GlobalTheory.CompanionTheory.SW.rmul]`. Use `continuous_finset_sum _ fun k _ => ?_` and prove the remaining obligations. Establish `h1 : Continuous fun h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => h k b` using `(continuous_apply b).comp (continuous_apply k)`. Conclude with `continuous_const.mul h1`. Establish `hAc : ∀ s, Continuous (A s)` using `fun s => hrc _`.

Establish `hAt : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))`. Introduce `x`. Establish `h1 : Filter.Tendsto (fun s : HermR (Ainf F) σ n => g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) (nhds c) (nhds (g0⁻¹ * t (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))))`. Rewrite using `[htc]`. Conclude with `hT1.const_mul g0⁻¹`.

Conclude with `((hrg x).tendsto _).comp h1`. Establish `hAinj : Function.Injective (A c)`. Introduce `x y hxy`. Establish `h1 : GlobalTheory.CompanionTheory.SW.rmul (Ainf F) x g0⁻¹ = GlobalTheory.CompanionTheory.SW.rmul (Ainf F) y g0⁻¹`. Use `hxy` as an intermediate fact.

Simplify using `only [A, rmulHom_apply, htc, mul_one] at this`. Conclude with `this`. Establish `h2` using `congrArg (fun Z => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) Z g0) h1`. Simplify `h2` using `only [hcomp, hgi2, hone]`. Establish `hAm : ∀ s, Measurable (A s)` using `fun s => (hAc s).measurable`.

Distinguish the cases in `h0 : minf c = 0`. Establish `hc0 : (minf s0).map (A c) Set.univ = 0`. Establish `h1` using `congrArg (fun m : Measure _ => m Set.univ) (hκ c hcO)`. Simplify using `only [h0, Measure.coe_zero, Pi.zero_apply, Measure.smul_apply] at h1`. Establish `h2` using `h1.symm`.

Rewrite `h2` using `[ENNReal.smul_def, smul_eq_mul, mul_eq_zero]`. Break down `h2 with h2 | h2` into its components or cases. Conclude with `absurd (by simpa using h2) (hκ0 c hcO)`. Conclude with `h2`. Establish `hs00 : minf s0 = 0`.

Establish `: (minf s0).map (A c) = 0` using `Measure.measure_univ_eq_zero.1 hc0`. Conclude with `(Measure.map_eq_zero_iff (hAm c).aemeasurable).1 this`. Establish `hz : ∀ s ∈ O, minf s = 0`. Introduce `s hs`. Rewrite using `[hκ s hs, hs00]`.

Simplify using the standard rewrite rules. Establish `hOn : O ∈ nhds c` using `hOo.mem_nhds hcO`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hOn] with s hs`. Rewrite using `[hz s hs]`.

Conclude with `integrable_zero_measure`. Establish `: ContinuousAt (fun _ : HermR (Ainf F) σ n => (0 : ℂ)) c` using `continuousAt_const`. Use `this.congr ?_` and prove the remaining obligations. Use `filter_upwards [hOn] with s hs`. Rewrite using `[hz s hs]`.

Simplify using the standard rewrite rules. Establish `hUo : IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | IsUnit (gramR (Ainf F) σ J X).det}`. Establish `: {X : Fin n → Fin M → Ainf F ⊗[F] E | IsUnit (gramR (Ainf F) σ J X).det} = (fun X => (gramR (Ainf F) σ J X).det) ⁻¹' Set.range (Units.val : (Ainf F ⊗[F] E)ˣ → Ainf F ⊗[F] E)`. Use extensionality with `X`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `hKu.isOpen_range.preimage (hgc n M J).matrix_det`. Establish `hsupp : minf c {X | IsUnit (gramR (Ainf F) σ J X).det}ᶜ = 0` using `measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hm'.1 c)`. Take `⟨χ, hχc, hχs, hχU, hχ0⟩` from `GlobalTheory.T.exists_bump_with_nonzero_integral _ (minf c) _ hUo hsupp h0 (fun χ h1 h2 h3 => (hm'.2.2 χ h1 h2 h3).1 c hc)`. Establish `hχt : ContinuousAt (fun s => ∫ x, χ x ∂(minf s)) c` using `((hm'.2.2 χ hχc hχs hχU).2).continuousAt (hBo.mem_nhds hc)`.

Establish `hev2 : ∀ᶠ s in nhds c, minf s = κ s • (minf s0).map (A s)` using `by filter_upwards [hOo.mem_nhds hcO] with s hs`. Conclude with `hκ s hs`. Use `haveI : SecondCountableTopology (HermR (Ainf F) σ n) := hSH`. Rewrite using `[hφe]`. Conclude with `family_core _ _ N e he hes c minf (minf s0) A κ hAc hAt hAinj hev2 hs0fin χ hχc hχs hχt hχ0 f`.
-/
theorem fibre_schwartzN : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → ∀ minf : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Ainf F) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) minf → ∀ c : HermR (Ainf F) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, IsSchwartzArch φ → Measurable φ ∧ (∀ᶠ s in nhds c, Integrable φ (minf s)) ∧ ContinuousAt (fun s => ∫ X, φ X ∂(minf s)) c := by
  intro F E _ _ _ _ _ σ hCM M J hJ n hn d b laminf hlam minf hm c hc φ hφ
  have hlH : laminf.IsAddHaarMeasure := hlam.1
  have hloc := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨ρ, e0, -, he0, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := id hloc
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, hsc, -, hrepr, hB, -, hgc⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hB n M
  obtain ⟨hLH, hSH, hT2H, hBH, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) n
  haveI := hLH
  haveI := hSH
  haveI := hT2H
  haveI := hBH
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hlH
  haveI := hW n M
  haveI := hH n
  obtain ⟨halg, hcomp, hone, hmem, -⟩ := GlobalTheory.CompanionTheory.SW.GramAlg.gram_algebra F E σ hCM M J hJ (Ainf F) n
  have hKu := GlobalTheory.CompanionTheory.SW.KUnits.units_val_isOpenEmbedding F E σ hCM (Ainf F) hloc
  obtain ⟨N, e, he, hes, f, hf⟩ := hφ
  have hφe : φ = fun x => f (e x) := funext hf
  have hφc : Continuous φ := by rw [hφe]; exact f.continuous.comp he
  refine ⟨hφc.measurable, ?_⟩

  let H1 := (hrepr d b).homeomorph
  let H2 : (Fin d → Ainf F) ≃ₜ (Fin d → InfinitePlace F → ℝ) :=
    Homeomorph.piCongrRight fun _ => he0.homeomorph
  let Hc := H1.trans H2
  let ε : (Ainf F ⊗[F] E) ≃+ (Fin d → InfinitePlace F → ℝ) :=
    { Hc.toEquiv with
      map_add' := by
        intro x y
        funext k w
        show e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr (x + y) k) w =
          e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr x k) w +
            e0 ((Algebra.TensorProduct.basis (Ainf F) b).repr y k) w
        simp only [map_add, Finsupp.add_apply, Pi.add_apply] }
  have hεc : Continuous ε := Hc.continuous
  have hεs : Continuous ε.symm := Hc.symm.continuous
  let ψ := matCoords ε n
  have hψ : Continuous ψ := continuous_pi fun i => continuous_pi fun j =>
    hεc.comp ((continuous_apply j).comp (continuous_apply i))
  have hψ' : Continuous ψ.symm := continuous_pi fun i => continuous_pi fun j =>
    hεs.comp ((continuous_apply j).comp (continuous_apply i))

  let ad : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) :=
    HeckeCharacterZeroLocus.SiegelWeilU.cT (sigR (Ainf F) σ)
  have hadc : Continuous ad := continuous_pi fun i => continuous_pi fun j =>
    hsc.comp ((continuous_apply i).comp (continuous_apply j))
  have hadm : ∀ x y, ad (x * y) = ad y * ad x := fun x y => HeckeCharacterZeroLocus.SiegelWeilU.cT_mul _ _ _
  have had1 : ad 1 = 1 := by
    show HeckeCharacterZeroLocus.SiegelWeilU.cT _ _ = _
    unfold HeckeCharacterZeroLocus.SiegelWeilU.cT
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]
  have hherm : ∀ s : HermR (Ainf F) σ n, ad (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = s := by
    intro s
    ext i j
    exact s.2 i j
  obtain ⟨t, ht1, ht2⟩ := orbit_section _ _ ψ hψ hψ' ad hadc hadm had1
    (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))⁻¹
    (Matrix.mul_nonsing_inv _ hc) (Matrix.nonsing_inv_mul _ hc) (hherm c)
  have hι : Filter.Tendsto (fun s : HermR (Ainf F) σ n => (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) (nhds c)
      (nhdsWithin (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) {s | ad s = s}) :=
    tendsto_nhdsWithin_iff.2 ⟨continuous_subtype_val.tendsto c, Filter.Eventually.of_forall hherm⟩
  have hT1 := ht1.comp hι
  have hT2' := hι.eventually ht2

  let Bl : Set (HermR (Ainf F) σ n) := {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det}
  have hBo : IsOpen Bl := by
    have : Bl = (fun S : HermR (Ainf F) σ n => (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det) ⁻¹'
        Set.range (Units.val : (Ainf F ⊗[F] E)ˣ → Ainf F ⊗[F] E) := by
      ext S
      rfl
    rw [this]
    exact hKu.isOpen_range.preimage continuous_subtype_val.matrix_det
  have hev := hT2'.and (hBo.mem_nhds hc)
  obtain ⟨O, hOs, hOo, hcO⟩ := eventually_nhds_iff.1 hev
  set μ := GlobalTheory.CompanionTheory.SW.coordW (Ainf F) b laminf n M with hμ
  set ν := GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n with hν
  have hm' : IsFibreFamily μ (gramR (Ainf F) σ J) Subtype.val {X | IsUnit (gramR (Ainf F) σ J X).det} ν Bl minf := hm
  haveI hμe : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he hes
  let W0 : (Fin N → ℝ) → ℝ := fun y => (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))
  have hW0m : Measurable W0 := (measurable_const.add measurable_norm).pow_const _
  have hWi : Integrable W0 (μ.map e) := integrable_one_add_norm (by simp)
  have hlin : ∫⁻ x, ENNReal.ofReal (W0 (e x)) ∂μ ≠ ⊤ := by
    have h1 := ((hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).1 hWi.2).ne
    rwa [lintegral_map (f := fun y => ENNReal.ofReal (W0 y)) (ENNReal.measurable_ofReal.comp hW0m) he.measurable] at h1
  have hOm : MeasurableSet O := MeasurableSpace.measurableSet_generateFrom hOo
  have hOp : ν O ≠ 0 := (hH n).toIsOpenPosMeasure.open_pos O hOo ⟨c, hcO⟩
  obtain ⟨s0, hs0O, hs0fin⟩ := exists_fin_point μ ν _ minf (fun x => ENNReal.ofReal (W0 (e x)))
    (hm'.2.1 _ (ENNReal.measurable_ofReal.comp (hW0m.comp he.measurable))) hlin O hOm hOp
  have hdetO : ∀ s ∈ O, IsUnit (t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det := by
    intro s hs
    have h1 := (hOs s hs).1
    have h2 : IsUnit (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det := (hOs s hs).2
    have h3 : IsUnit (ad (t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))) *
        (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det := by
      rw [h1]; exact h2
    rw [Matrix.det_mul] at h3
    exact isUnit_of_mul_isUnit_right h3
  set g0 := t (s0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) with hg0
  have hg0d : IsUnit g0.det := hdetO s0 hs0O
  have hgi1 : g0 * g0⁻¹ = 1 := Matrix.mul_nonsing_inv g0 hg0d
  have hgi2 : g0⁻¹ * g0 = 1 := Matrix.nonsing_inv_mul g0 hg0d
  have hgid : IsUnit (g0⁻¹).det := Matrix.isUnit_nonsing_inv_det g0 hg0d
  let A : HermR (Ainf F) σ n → (Fin n → Fin M → Ainf F ⊗[F] E) →+ (Fin n → Fin M → Ainf F ⊗[F] E) :=
    fun s => rmulHom (Ainf F) (g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)))
  have hκ : ∀ s ∈ O, ∃ κ : ℝ≥0, κ ≠ 0 ∧ minf s = κ • (minf s0).map (A s) := by
    intro s hs
    have hd : IsUnit (g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))).det := by
      rw [Matrix.det_mul]
      exact hgid.mul (hdetO s hs)
    obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.local_gram_fibration_unique F E σ hCM M J hJ (Ainf F) hloc n μ ν minf (hW n M) (hH n) hm _ hd
    refine ⟨κ, hκ0, hκ s0 s ?_⟩
    show (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ad _ * _ * _
    have h0 : (s0 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = ad g0 * c * g0 := (hOs s0 hs0O).1.symm
    have h1 : ad g0⁻¹ * ad g0 = 1 := by rw [← hadm, hgi1, had1]
    rw [hadm, h0]
    calc (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E))
        = ad (t s) * c * t s := (hOs s hs).1.symm
      _ = ad (t s) * ((ad g0⁻¹ * ad g0) * c * (g0 * g0⁻¹)) * t s := by rw [h1, hgi1, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  choose! κ hκ0 hκ using hκ
  haveI : T2Space (Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) := inferInstanceAs (T2Space (Fin n → Fin n → Ainf F ⊗[F] E))
  have htc : t (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = 1 :=
    tendsto_nhds_unique (tendsto_pure_nhds _ c) (hT1.mono_left (pure_le_nhds c))
  have hrc : ∀ h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      Continuous fun X : Fin n → Fin M → Ainf F ⊗[F] E => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h := by
    intro h
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun Y : Fin n → Fin M → Ainf F ⊗[F] E => Y k i :=
      (continuous_apply i).comp (continuous_apply k)
    exact h1.mul continuous_const
  have hrg : ∀ X : Fin n → Fin M → Ainf F ⊗[F] E,
      Continuous fun h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) X h := by
    intro X
    refine continuous_pi fun b => continuous_pi fun i => ?_
    simp only [GlobalTheory.CompanionTheory.SW.rmul]
    refine continuous_finset_sum _ fun k _ => ?_
    have h1 : Continuous fun h : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) => h k b :=
      (continuous_apply b).comp (continuous_apply k)
    exact continuous_const.mul h1
  have hAc : ∀ s, Continuous (A s) := fun s => hrc _
  have hAt : ∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x)) := by
    intro x
    have h1 : Filter.Tendsto (fun s : HermR (Ainf F) σ n => g0⁻¹ * t (s : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)))
        (nhds c) (nhds (g0⁻¹ * t (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)))) := by
      rw [htc]
      exact hT1.const_mul g0⁻¹
    exact ((hrg x).tendsto _).comp h1
  have hAinj : Function.Injective (A c) := by
    intro x y hxy
    have h1 : GlobalTheory.CompanionTheory.SW.rmul (Ainf F) x g0⁻¹ = GlobalTheory.CompanionTheory.SW.rmul (Ainf F) y g0⁻¹ := by
      have := hxy
      simp only [A, rmulHom_apply, htc, mul_one] at this
      exact this
    have h2 := congrArg (fun Z => GlobalTheory.CompanionTheory.SW.rmul (Ainf F) Z g0) h1
    simpa only [hcomp, hgi2, hone] using h2
  have hAm : ∀ s, Measurable (A s) := fun s => (hAc s).measurable
  by_cases h0 : minf c = 0
  · have hc0 : (minf s0).map (A c) Set.univ = 0 := by
      have h1 := congrArg (fun m : Measure _ => m Set.univ) (hκ c hcO)
      simp only [h0, Measure.coe_zero, Pi.zero_apply, Measure.smul_apply] at h1
      have h2 := h1.symm
      rw [ENNReal.smul_def, smul_eq_mul, mul_eq_zero] at h2
      rcases h2 with h2 | h2
      · exact absurd (by simpa using h2) (hκ0 c hcO)
      · exact h2
    have hs00 : minf s0 = 0 := by
      have : (minf s0).map (A c) = 0 := Measure.measure_univ_eq_zero.1 hc0
      exact (Measure.map_eq_zero_iff (hAm c).aemeasurable).1 this
    have hz : ∀ s ∈ O, minf s = 0 := by
      intro s hs
      rw [hκ s hs, hs00]
      simp
    have hOn : O ∈ nhds c := hOo.mem_nhds hcO
    refine ⟨?_, ?_⟩
    · filter_upwards [hOn] with s hs
      rw [hz s hs]
      exact integrable_zero_measure
    · have : ContinuousAt (fun _ : HermR (Ainf F) σ n => (0 : ℂ)) c := continuousAt_const
      refine this.congr ?_
      filter_upwards [hOn] with s hs
      rw [hz s hs]
      simp
  · have hUo : IsOpen {X : Fin n → Fin M → Ainf F ⊗[F] E | IsUnit (gramR (Ainf F) σ J X).det} := by
      have : {X : Fin n → Fin M → Ainf F ⊗[F] E | IsUnit (gramR (Ainf F) σ J X).det} =
          (fun X => (gramR (Ainf F) σ J X).det) ⁻¹'
            Set.range (Units.val : (Ainf F ⊗[F] E)ˣ → Ainf F ⊗[F] E) := by
        ext X
        rfl
      rw [this]
      exact hKu.isOpen_range.preimage (hgc n M J).matrix_det
    have hsupp : minf c {X | IsUnit (gramR (Ainf F) σ J X).det}ᶜ = 0 :=
      measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hm'.1 c)
    obtain ⟨χ, hχc, hχs, hχU, hχ0⟩ := GlobalTheory.T.exists_bump_with_nonzero_integral _ (minf c) _ hUo hsupp h0
      (fun χ h1 h2 h3 => (hm'.2.2 χ h1 h2 h3).1 c hc)
    have hχt : ContinuousAt (fun s => ∫ x, χ x ∂(minf s)) c :=
      ((hm'.2.2 χ hχc hχs hχU).2).continuousAt (hBo.mem_nhds hc)
    have hev2 : ∀ᶠ s in nhds c, minf s = κ s • (minf s0).map (A s) := by
      filter_upwards [hOo.mem_nhds hcO] with s hs
      exact hκ s hs
    haveI : SecondCountableTopology (HermR (Ainf F) σ n) := hSH
    rw [hφe]
    exact family_core _ _ N e he hes c minf (minf s0) A κ hAc hAt hAinj hev2 hs0fin χ hχc hχs hχt hχ0 f

end GlobalTheory.CompanionTheory.SiegelND.Coef.FibN
