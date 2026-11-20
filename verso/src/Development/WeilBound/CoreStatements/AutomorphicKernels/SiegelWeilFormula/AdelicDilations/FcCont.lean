import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.DerivInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.AStep

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Take `⟨hnb, hlam, hfd, hvol⟩` from `hc`. Establish `hB` using `d.ok.good`. Establish `hσ : ∀ a, σ (σ a) = a` using `kfour.sigma_sigma_of_good hB`. Establish `hb` using `d.ok.frame`. Take `⟨iLC, iSC, iT2, iBo⟩` from `kfour.nA_top hσ hb`.

Establish `hcont` using `kfour.nb_continuous hσ hb hnb`. Establish `hψ` using `GlobalTheory.StdCharWeilDatum.isCharAF hB.std`. Take `⟨K, hK, hKc⟩` from `kfour.nF_cocompact hσ hb`. Use `set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) with hχ`. Establish `hχc : Continuous χ` using `kfour.continuous_chr hψ.1 T.1.1`.

Establish `hχn : ∀ β, ‖χ β‖ = 1` using `fun β => hψ.2.1 _`. Establish `hfin : lam 𝓖 < ⊤` using `by rw [hvol]; exact ENNReal.one_lt_top`. Establish `hcm : Continuous fun β : nA σ d.Y d.b => nb β * x` using `hcont.mul continuous_const`. Establish `hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K, f (nb β * x) = f (nb k * x)`. Introduce `f hf β`.

Take `⟨γ, hγ, hk⟩` from `hKc β`. Use `⟨γ + β, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]`. Establish `hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M`. Introduce `f M hf hM β`.

Take `⟨k, hk, e⟩` from `hper f hf β`. Rewrite using `[norm_mul, hχn β, mul_one, e]`. Conclude with `hM _ ⟨k, hk, rfl⟩`. Establish `hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam`. Introduce `f hfc hf`.

Take `⟨M, hM⟩` from `(hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn`. Use `Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_` and prove the remaining obligations. Conclude with `((hfc.comp hcm).mul hχc).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun β => hbd f M hf hM β`. Use `⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [fc]`. Establish `e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) = fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β`. Use function extensionality and compare the values at `β`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]`. Use `show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M`. Establish `h1` using `norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)`. Establish `hr : lam.real 𝓖 = 1` using `by simp [Measure.real, hvol]`. Rewrite `h1` using `[hr, mul_one]`. Then use the resulting hypothesis.
-/
theorem fcAll (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (x : d.G) :
    (∀ (a : ℂ) (f f' : d.G → ℂ), Continuous f → Continuous f' → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ γ ∈ rat2 σ d.Y, ∀ g, f' (γ * g) = f' g) →
      fc d.B.ψ d.b nb lam 𝓖 (a • f + f') T x = a * fc d.B.ψ d.b nb lam 𝓖 f T x + fc d.B.ψ d.b nb lam 𝓖 f' T x) ∧
    ∃ C : Set d.G, IsCompact C ∧ ∀ (f : d.G → ℂ) (M : ℝ), Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ C, ‖f y‖ ≤ M) → ‖fc d.B.ψ d.b nb lam 𝓖 f T x‖ ≤ M := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [kfour.nb_add hnb, mul_assoc, hf _ (kfour.nb_rat hnb γ hγ)]
  have hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M := by
    intro f M hf hM β
    obtain ⟨k, hk, e⟩ := hper f hf β
    rw [norm_mul, hχn β, mul_one, e]
    exact hM _ ⟨k, hk, rfl⟩
  have hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) →
      IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam := by
    intro f hfc hf
    obtain ⟨M, hM⟩ := (hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_
    · exact ((hfc.comp hcm).mul hχc).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun β => hbd f M hf hM β
  refine ⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩
  · simp only [fc]
    have e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) =
        fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β := by
      funext β; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]; ring
    rw [e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]
  · show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M
    have h1 := norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)
    have hr : lam.real 𝓖 = 1 := by simp [Measure.real, hvol]
    rwa [hr, mul_one] at h1

/- English proof (translation)
Take `⟨hnb, hlam, hfd, hvol⟩` from `hc`. Establish `hB` using `d.ok.good`. Establish `hσ : ∀ a, σ (σ a) = a` using `kfour.sigma_sigma_of_good hB`. Establish `hb` using `d.ok.frame`. Take `⟨iLC, iSC, iT2, iBo⟩` from `kfour.nA_top hσ hb`.

Take `⟨iTG, iLCG, -, -⟩` from `kfour.doubled_group_topological_properties σ d.Y`. Establish `hcont` using `kfour.nb_continuous hσ hb hnb`. Establish `hψ` using `GlobalTheory.StdCharWeilDatum.isCharAF hB.std`. Take `⟨K, hK, hKc⟩` from `kfour.nF_cocompact hσ hb`. Use `set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) with hχ`.

Establish `hχc : Continuous χ` using `kfour.continuous_chr hψ.1 T.1.1`. Establish `hχn : ∀ β, ‖χ β‖ = 1` using `fun β => hψ.2.1 _`. Establish `hfin : IsFiniteMeasure (lam.restrict 𝓖)` using `⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩`. Establish `hmul : Continuous fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2` using `(hcont.comp continuous_fst).mul continuous_snd`. Use `continuous_iff_continuousAt.2 fun x₀ => ?_` and prove the remaining obligations.

Take `⟨N, hN, hNx⟩` from `exists_compact_mem_nhds x₀`. Establish `hKN : IsCompact ((fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2) '' (K ×ˢ N))` using `(hK.prod hN).image hmul`. Take `⟨M, hM⟩` from `hKN.exists_bound_of_continuousOn hf.continuousOn`. Use `continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_` and prove the remaining obligations. Conclude with `Filter.Eventually.of_forall fun x => ((hf.comp (hcont.mul continuous_const)).mul hχc).aestronglyMeasurable`.

Use `filter_upwards [hNx] with x hx`. Use `Filter.Eventually.of_forall fun β => ?_` and prove the remaining obligations. Take `⟨γ, hγ, hk⟩` from `hKc β`. Rewrite using `[norm_mul, hχn β, mul_one]`. Establish `: f (nb β * x) = f (nb (γ + β) * x)`.

Rewrite using `[kfour.nb_add hnb, mul_assoc, hi _ (kfour.nb_rat hnb γ hγ)]`. Rewrite using `[this]`. Conclude with `hM _ ⟨(γ + β, x), ⟨hk, hx⟩, rfl⟩`. Conclude with `Filter.Eventually.of_forall fun β => ((hf.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt`.
-/
theorem fcCont (d : SD σ) {nb lam 𝓖} (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (T : nF σ d.Y d.b) (f : d.G → ℂ)
    (hf : Continuous f) (hi : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) : Continuous fun x => fc d.B.ψ d.b nb lam 𝓖 f T x := by
  obtain ⟨hnb, hlam, hfd, hvol⟩ := hc
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := kfour.sigma_sigma_of_good hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ hb
  obtain ⟨iTG, iLCG, -, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hcont := kfour.nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := kfour.nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := kfour.continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have hmul : Continuous fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2 := (hcont.comp continuous_fst).mul continuous_snd
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  obtain ⟨N, hN, hNx⟩ := exists_compact_mem_nhds x₀
  have hKN : IsCompact ((fun q : nA σ d.Y d.b × d.G => nb q.1 * q.2) '' (K ×ˢ N)) := (hK.prod hN).image hmul
  obtain ⟨M, hM⟩ := hKN.exists_bound_of_continuousOn hf.continuousOn
  refine continuousAt_of_dominated (bound := fun _ => M) ?_ ?_ (integrable_const M) ?_
  · exact Filter.Eventually.of_forall fun x =>
      ((hf.comp (hcont.mul continuous_const)).mul hχc).aestronglyMeasurable
  · filter_upwards [hNx] with x hx
    refine Filter.Eventually.of_forall fun β => ?_
    obtain ⟨γ, hγ, hk⟩ := hKc β
    rw [norm_mul, hχn β, mul_one]
    have : f (nb β * x) = f (nb (γ + β) * x) := by
      rw [kfour.nb_add hnb, mul_assoc, hi _ (kfour.nb_rat hnb γ hγ)]
    rw [this]
    exact hM _ ⟨(γ + β, x), ⟨hk, hx⟩, rfl⟩
  · exact Filter.Eventually.of_forall fun β =>
      ((hf.comp (continuous_const.mul continuous_id)).mul continuous_const).continuousAt

end PositivityTheory.SiegelWeilFormula.AStep

end
