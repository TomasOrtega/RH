import Development.WeilBound.ThetaLifts.SmallCones.ThetaUniq

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

/- English proof (translation)
Use `⟨hf.aestronglyMeasurable, ?_⟩` and prove the remaining obligations. Rewrite using `[HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]`. Use `lt_of_le_of_lt (lintegral_mono hK) ?_` and prove the remaining obligations. Rewrite using `[lintegral_const]`. Conclude with `ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)`.
-/
theorem integrable_prod_of_bound {G N : Type} [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] (μ : Measure G) [SFinite μ] (ν : Measure N) [IsFiniteMeasure ν]
    {f : G × N → ℂ} (hf : Continuous f) {K : ℝ} (hK : ∀ u, ∫⁻ g, ‖f (g, u)‖ₑ ∂μ ≤ ENNReal.ofReal K) : Integrable f (μ.prod ν) := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod_symm _ hf.enorm.measurable.aemeasurable]
  refine lt_of_le_of_lt (lintegral_mono hK) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc`. Take `⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩` from `hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH`. Take `⟨b1, b2, -⟩` from `hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1`. Take `⟨-, -, -, -, -, -, -, b3⟩` from `hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1`. Take `⟨t1, t2, -⟩` from `(hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ`.

Establish `: BorelSpace (UA σ X.J)` using `⟨rfl⟩`. Establish `: BorelSpace (UA σ W.J)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AE F E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Establish `: IsTopologicalGroup (UA σ W.J)` using `Subgroup.instIsTopologicalGroupSubtypeMem _`. Establish `: IsTopologicalGroup (UA σ X.J)` using `Subgroup.instIsTopologicalGroupSubtypeMem _`.

Use `hp.good.haar` as an intermediate fact. Establish `: SigmaFinite M.μ` using `MeasureTheory.sigmaFinite_of_locallyFinite`. Establish `: SFinite (M.μ.restrict M.dom)` using `@MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)`. Establish `key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧ Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕))`. Introduce `ν 𝓕 h1 h`.

Establish `hf : IsFiniteMeasure (ν.restrict 𝓕)` using `⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩`. Establish `hcont : Continuous fun u : unip σ W H' => u.1 * h` using `continuous_subtype_val.mul continuous_const`. Take `⟨D, hD⟩` from `b3 _ (hΩ.image hcont)`. Use `⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k) (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hu⟩` from `hcov u`.

Establish `e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h)` using `fun g => by`. Rewrite using `[← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]`. Simplify using `only [e]`. Use `(hb _).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Establish `h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D` using `hD _ ⟨_, hu, rfl⟩`.

Conclude with `mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)`. Use `⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩` and prove the remaining obligations. Take `⟨_, hi⟩` from `key ν₀ 𝓕₀ a3 h`. Simplify using `only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]`. Conclude with `hi.integral_prod_left`.

Take `⟨_, hi⟩` from `key ν 𝓕 c3 h`. Simplify using `only [fun g => hc g ν 𝓕 c1 c2 c3 h]`. Conclude with `integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi`.
-/
theorem ctFub_of (hU : UnipEx) (hT : ThetaBasic) (hG : GrpTop) (hE : EpsOf) : CTFub := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp d₁ W₁ H' i₀ i₁ hH Φ hΦ ⟨C, k, hb⟩ c hc
  obtain ⟨⟨ν₀, 𝓕₀, a1, a2, a3⟩, ⟨Ω, hΩ, hcov⟩, -⟩ := hU F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hp.base (Or.inr hp.skew) hH
  obtain ⟨b1, b2, -⟩ := hG F E σ hp.base.cm n X.J (hE F E σ B hp.base n X r s (Or.inl hp.herm)).1
  obtain ⟨-, -, -, -, -, -, -, b3⟩ := hG F E σ hp.base.cm d W.J (hE F E σ B hp.base d W r' s' (Or.inr hp.skew)).1
  obtain ⟨t1, t2, -⟩ := (hT F E σ B n d X W M χX χW om r s r' s' hp).1 Φ hΦ
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : IsTopologicalGroup (UA σ W.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have : IsTopologicalGroup (UA σ X.J) := Subgroup.instIsTopologicalGroupSubtypeMem _
  have := hp.good.haar
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) :=
    @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  have key : ∀ (ν : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), ν 𝓕 = 1 → ∀ h, SFinite (ν.restrict 𝓕) ∧
      Integrable (fun x : UA σ X.J × unip σ W H' => theta om Φ x.1 (x.2.1 * h)) ((M.μ.restrict M.dom).prod (ν.restrict 𝓕)) := by
    intro ν 𝓕 h1 h
    have hf : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
    have hcont : Continuous fun u : unip σ W H' => u.1 * h := continuous_subtype_val.mul continuous_const
    obtain ⟨D, hD⟩ := b3 _ (hΩ.image hcont)
    refine ⟨@instSFiniteOfSigmaFinite _ _ _ (IsFiniteMeasure.toSigmaFinite _), integrable_prod_of_bound _ _ (K := |C| * (D : ℝ) ^ k)
      (t1.comp (continuous_fst.prodMk (hcont.comp continuous_snd))) fun u => ?_⟩
    obtain ⟨γ, hγ, hu⟩ := hcov u
    have e : ∀ g, theta om Φ g (u.1 * h) = theta om Φ g ((γ * u).1 * h) := fun g => by
      rw [← t2 1 (one_mem _) γ.1 hγ g, one_mul, Subgroup.coe_mul, mul_assoc]
    simp only [e]
    refine (hb _).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : (ht ((γ * u).1 * h) : ℝ) ≤ D := hD _ ⟨_, hu, rfl⟩
    exact mul_le_mul (le_abs_self C) (pow_le_pow_left₀ (NNReal.coe_nonneg _) h2 k) (by positivity) (abs_nonneg C)
  refine ⟨fun h => ?_, fun ν 𝓕 c1 c2 c3 h => ?_⟩
  · obtain ⟨_, hi⟩ := key ν₀ 𝓕₀ a3 h
    simp only [fun g => hc g ν₀ 𝓕₀ a1 a2 a3 h]
    exact hi.integral_prod_left
  · obtain ⟨_, hi⟩ := key ν 𝓕 c3 h
    simp only [fun g => hc g ν 𝓕 c1 c2 c3 h]
    exact integral_integral_swap (f := fun (g : UA σ X.J) (u : unip σ W H') => theta om Φ g (u.1 * h)) hi

end PositivityTheory.ThKCT
