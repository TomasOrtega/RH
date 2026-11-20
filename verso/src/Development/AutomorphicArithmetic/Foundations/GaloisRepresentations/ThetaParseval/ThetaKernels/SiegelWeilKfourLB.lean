import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FourierCompactness.ContinuousChr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.kfour
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d L hL`. Take `⟨nb, lam, 𝓖, T, x, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩` from `hL`. Establish `hB` using `d.ok.good`. Establish `hσ : ∀ a, σ (σ a) = a` using `_root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB`. Establish `hb` using `d.ok.frame`.

Take `⟨iLC, iSC, iT2, iBo⟩` from `nA_top hσ hb`. Establish `hcont` using `nb_continuous hσ hb hnb`. Establish `hψ` using `GlobalTheory.StdCharWeilDatum.isCharAF hB.std`. Take `⟨K, hK, hKc⟩` from `nF_cocompact hσ hb`. Use `set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) with hχ`.

Establish `hχc : Continuous χ` using `continuous_chr hψ.1 T.1.1`. Establish `hχn : ∀ β, ‖χ β‖ = 1` using `fun β => hψ.2.1 _`. Establish `hfin : lam 𝓖 < ⊤` using `by rw [hvol]; exact ENNReal.one_lt_top`. Establish `hcm : Continuous fun β : nA σ d.Y d.b => nb β * x` using `hcont.mul continuous_const`. Establish `hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K, f (nb β * x) = f (nb k * x)`.

Introduce `f hf β`. Take `⟨γ, hγ, hk⟩` from `hKc β`. Use `⟨γ + β, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]`. Establish `hbd : ∀ (f : d.G → ℂ) (M : ℝ), (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → (∀ y ∈ (fun β => nb β * x) '' K, ‖f y‖ ≤ M) → ∀ β, ‖f (nb β * x) * χ β‖ ≤ M`.

Introduce `f M hf hM β`. Take `⟨k, hk, e⟩` from `hper f hf β`. Rewrite using `[norm_mul, hχn β, mul_one, e]`. Conclude with `hM _ ⟨k, hk, rfl⟩`. Establish `hint : ∀ f : d.G → ℂ, Continuous f → (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → IntegrableOn (fun β => f (nb β * x) * χ β) 𝓖 lam`.

Introduce `f hfc hf`. Take `⟨M, hM⟩` from `(hK.image hcm).exists_bound_of_continuousOn hfc.continuousOn`. Use `Measure.integrableOn_of_bounded (M := M) hfin.ne ?_ ?_` and prove the remaining obligations. Conclude with `((hfc.comp hcm).mul hχc).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun β => hbd f M hf hM β`.

Use `⟨fun a f f' hfc hf'c hf hf' => ?_, ⟨(fun β => nb β * x) '' K, hK.image hcm, fun f M hfc hf hM => ?_⟩⟩` and prove the remaining obligations. Simplify using `only [fc]`. Establish `e : (fun β : nA σ d.Y d.b => (a • f + f') (nb β * x) * d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))) = fun β => a * (f (nb β * x) * χ β) + f' (nb β * x) * χ β`. Use function extensionality and compare the values at `β`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hχ]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, integral_add ((hint f hfc hf).const_mul a) (hint f' hf'c hf'), integral_const_mul]`. Use `show ‖∫ β in 𝓖, f (nb β * x) * χ β ∂lam‖ ≤ M`. Establish `h1` using `norm_setIntegral_le_of_norm_le_const hfin (fun β _ => hbd f M hf hM β)`. Establish `hr : lam.real 𝓖 = 1` using `by simp [Measure.real, hvol]`.

Rewrite `h1` using `[hr, mul_one]`. Then use the resulting hypothesis.
-/
theorem lamBd_k : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k := by
  intro F E _ _ _ _ _ σ d L hL
  obtain ⟨nb, lam, 𝓖, T, x, ⟨hnb, hlam, hfd, hvol⟩, -, rfl⟩ := hL
  have hB := d.ok.good
  have hσ : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k hB
  have hb := d.ok.frame
  obtain ⟨iLC, iSC, iT2, iBo⟩ := nA_top hσ hb
  have hcont := nb_continuous hσ hb hnb
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF hB.std
  obtain ⟨K, hK, hKc⟩ := nF_cocompact hσ hb
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  have hχc : Continuous χ := continuous_chr hψ.1 T.1.1
  have hχn : ∀ β, ‖χ β‖ = 1 := fun β => hψ.2.1 _
  have hfin : lam 𝓖 < ⊤ := by rw [hvol]; exact ENNReal.one_lt_top
  have hcm : Continuous fun β : nA σ d.Y d.b => nb β * x := hcont.mul continuous_const
  have hper : ∀ f : d.G → ℂ, (∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g) → ∀ β, ∃ k ∈ K,
      f (nb β * x) = f (nb k * x) := by
    intro f hf β
    obtain ⟨γ, hγ, hk⟩ := hKc β
    refine ⟨γ + β, hk, ?_⟩
    rw [nb_add hnb, mul_assoc, hf _ (nb_rat hnb γ hγ)]
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
end PositivityTheory.SiegelWeilFormula.kfour
end
end
