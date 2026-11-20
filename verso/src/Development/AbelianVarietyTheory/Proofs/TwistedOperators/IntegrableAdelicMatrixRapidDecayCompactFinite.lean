import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HermitianSymplecticScalars
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsCompactLatticeStabilizerBoundedReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInverseChart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdelicIntegrable

/- English proof (translation)
Introduce `D a b μ hμ θ hθ f hf K hK hKf hdec`. Take `⟨i1, i2, i3, i4, -, -⟩` from `GlobalTheory.MixModel.lattice_Mx D a b`. Use `haveI : BorelSpace (Mx D a b) := ⟨rfl⟩`. Take `⟨σ, hσ⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Set `π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ)` to `fun y i j τ => θ τ (infPart D (y i j))`.

Establish `hπc : Continuous π` using `continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ => (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))`. Establish `hπm : Measurable π` using `hπc.measurable`. Set `s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b` to `fun c => Matrix.of fun i j => σ (c i j)`. Establish `hπs : ∀ c y, π (s c + y) = c + π y`. Introduce `c y`.

Use function extensionality and compare the values at `i j τ`. Use `show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))`. Rewrite using `[RingHom.map_add, RingHom.map_add, hσ.comp]`. Establish `hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D)`. Introduce `c y`.

Use extensionality with `i j`. Use `show finPart D (σ (c i j) + y i j) = finPart D (y i j)`. Rewrite using `[RingHom.map_add, hσ.fin, zero_add]`. Set `S : Set (Mx D a b)` to `{y | y.map (finPart D) ∈ K}`. Set `ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)` to `(μ.restrict S).map π`.

Establish `hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S)` using `fun A hA => by`. Rewrite using `[Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]`. Use `haveI : ν.IsAddLeftInvariant := by`. Use `⟨fun c => Measure.ext fun A hA => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]`.

Establish `e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S)`. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]`. Rewrite using `[e, measure_preimage_add]`. Use `haveI : IsFiniteMeasureOnCompacts ν := by`.

Use `⟨fun A hA => ?_⟩` and prove the remaining obligations. Take `⟨R, hR⟩` from `hA.isBounded.exists_norm_le`. Use `choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K) (hK.image ((continuous_apply j).comp (continuous_apply i)))`. Establish `hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b))` using `isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j`. Rewrite using `[hνA _ hA.isClosed.measurableSet]`.

Use `haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts`. Use `lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)` and prove the remaining obligations. Introduce and unpack `y ⟨hyA, hyS⟩ i - j -`. Use `hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)` and prove the remaining obligations. Conclude with `(norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))`.

Establish `hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ))` using `Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar`. Use `set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN`. Take `⟨C, hC⟩` from `hdec N`. Set `G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ` to `fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))`. Establish `hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ))` using `(integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C`.

Establish `hGν : Integrable G ν`. Rewrite using `[hνe]`. Conclude with `hGv.smul_measure ENNReal.coe_ne_top`. Establish `hGπ : Integrable (G ∘ π) (μ.restrict S)` using `(integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν`. Establish `hbound : ∀ y, ‖f y‖ ≤ G (π y)`.

Introduce `y`. Establish `hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖`. Use `(pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity) (Finset.mem_univ τ))` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity) (Finset.mem_univ i))` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity) (Finset.mem_univ j)`. Establish `h1 : 0 < 1 + ‖π y‖` using `by positivity`. Establish `h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N` using `pow_le_pow_left₀ h1.le (by linarith) N`. Establish `h3` using `hC y`. Establish `h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C` using `le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3`.

Use `show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))`. Rewrite using `[Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]`. Conclude with `h4`. Establish `hfS : IntegrableOn f S μ` using `hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)`. Conclude with `hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy`.
-/
theorem integrable_of_rapid_decay : ∀ (D : D7) (a b : ℕ) (μ : Measure (Mx D a b)), μ.IsAddHaarMeasure → ∀ θ : InfFam D, IsInfFam θ → ∀ f : Mx D a b → ℂ, Continuous f → ∀ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K → (∀ y : Mx D a b, y.map (finPart D) ∉ K → f y = 0) → (∀ N : ℕ, ∃ C : ℝ, ∀ y : Mx D a b, (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N * ‖f y‖ ≤ C) → Integrable f μ := by
  intro D a b μ hμ θ hθ f hf K hK hKf hdec
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  haveI : BorelSpace (Mx D a b) := ⟨rfl⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ

  let π : Mx D a b → (Fin a → Fin b → D.what₂.Tau → ℂ) := fun y i j τ => θ τ (infPart D (y i j))
  have hπc : Continuous π := continuous_pi fun i => continuous_pi fun j => continuous_pi fun τ =>
    (GlobalTheory.FockCompare.continuous_comp hθ τ).comp ((continuous_apply j).comp (continuous_apply i))
  have hπm : Measurable π := hπc.measurable

  let s : (Fin a → Fin b → D.what₂.Tau → ℂ) → Mx D a b := fun c => Matrix.of fun i j => σ (c i j)
  have hπs : ∀ c y, π (s c + y) = c + π y := by
    intro c y; funext i j τ
    show θ τ (infPart D (σ (c i j) + y i j)) = c i j τ + θ τ (infPart D (y i j))
    rw [RingHom.map_add, RingHom.map_add, hσ.comp]
  have hfs : ∀ c (y : Mx D a b), (s c + y).map (finPart D) = y.map (finPart D) := by
    intro c y; ext i j
    show finPart D (σ (c i j) + y i j) = finPart D (y i j)
    rw [RingHom.map_add, hσ.fin, zero_add]
  let S : Set (Mx D a b) := {y | y.map (finPart D) ∈ K}
  let ν : Measure (Fin a → Fin b → D.what₂.Tau → ℂ) := (μ.restrict S).map π
  have hνA : ∀ A, MeasurableSet A → ν A = μ (π ⁻¹' A ∩ S) := fun A hA => by
    rw [Measure.map_apply hπm hA, Measure.restrict_apply (hπm hA)]
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => Measure.ext fun A hA => ?_⟩
    rw [Measure.map_apply (measurable_const_add c) hA, hνA _ (measurable_const_add c hA), hνA _ hA]
    have e : π ⁻¹' ((fun x => c + x) ⁻¹' A) ∩ S = (fun y => s c + y) ⁻¹' (π ⁻¹' A ∩ S) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_preimage, S, Set.mem_setOf_eq, hπs, hfs]
    rw [e, measure_preimage_add]
  haveI : IsFiniteMeasureOnCompacts ν := by
    refine ⟨fun A hA => ?_⟩
    obtain ⟨R, hR⟩ := hA.isBounded.exists_norm_le
    choose C hC hCK using fun i j => GlobalTheory.StabCompact.exists_compact_adele D θ hθ R
      ((fun M : Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) => M i j) '' K)
      (hK.image ((continuous_apply j).comp (continuous_apply i)))
    have hc : IsCompact (Set.pi Set.univ fun i => Set.pi Set.univ fun j => C i j : Set (Mx D a b)) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => hC i j
    rw [hνA _ hA.isClosed.measurableSet]
    haveI : IsFiniteMeasureOnCompacts μ := hμ.toIsFiniteMeasureOnCompacts
    refine lt_of_le_of_lt (measure_mono ?_) (IsFiniteMeasureOnCompacts.lt_top_of_isCompact (μ := μ) hc)
    rintro y ⟨hyA, hyS⟩ i - j -
    refine hCK i j _ ⟨_, hyS, rfl⟩ fun ρ => le_trans ?_ (hR _ hyA)
    exact (norm_le_pi_norm (π y i j) ρ).trans ((norm_le_pi_norm (π y i) j).trans (norm_le_pi_norm (π y) i))
  have hνe : ν = ν.addHaarScalarFactor Measure.addHaar • (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    Measure.isAddLeftInvariant_eq_smul ν Measure.addHaar

  set N : ℕ := Module.finrank ℝ (Fin a → Fin b → D.what₂.Tau → ℂ) + 1 with hN
  obtain ⟨C, hC⟩ := hdec N
  let G : (Fin a → Fin b → D.what₂.Tau → ℂ) → ℝ := fun x => C * (1 + ‖x‖) ^ (-(N : ℝ))
  have hGv : Integrable G (Measure.addHaar : Measure (Fin a → Fin b → D.what₂.Tau → ℂ)) :=
    (integrable_one_add_norm (by rw [hN]; push_cast; linarith)).const_mul C
  have hGν : Integrable G ν := by
    rw [hνe]; exact hGv.smul_measure ENNReal.coe_ne_top
  have hGπ : Integrable (G ∘ π) (μ.restrict S) :=
    (integrable_map_measure hGν.aestronglyMeasurable hπm.aemeasurable).1 hGν
  have hbound : ∀ y, ‖f y‖ ≤ G (π y) := by
    intro y
    have hsum : ‖π y‖ ≤ ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖ := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => (pi_norm_le_iff_of_nonneg (by positivity)).2
        fun j => (pi_norm_le_iff_of_nonneg (by positivity)).2 fun τ => ?_
      refine le_trans ?_ (Finset.single_le_sum (f := fun τ => ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ τ))
      refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j, ‖θ τ (infPart D (y i j))‖)
        (fun _ _ => by positivity) (Finset.mem_univ i))
      exact Finset.single_le_sum (f := fun j => ‖θ τ (infPart D (y i j))‖) (fun _ _ => by positivity)
        (Finset.mem_univ j)
    have h1 : 0 < 1 + ‖π y‖ := by positivity
    have h2 : (1 + ‖π y‖) ^ N ≤ (1 + ∑ τ, ∑ i, ∑ j, ‖θ τ (infPart D (y i j))‖) ^ N :=
      pow_le_pow_left₀ h1.le (by linarith) N
    have h3 := hC y
    have h4 : (1 + ‖π y‖) ^ N * ‖f y‖ ≤ C := le_trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)) h3
    show ‖f y‖ ≤ C * (1 + ‖π y‖) ^ (-(N : ℝ))
    rw [Real.rpow_neg h1.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1 N), mul_comm]
    exact h4
  have hfS : IntegrableOn f S μ :=
    hGπ.mono' hf.aestronglyMeasurable.restrict (Filter.Eventually.of_forall hbound)
  exact hfS.integrable_of_forall_notMem_eq_zero fun y hy => hKf y hy

end GlobalTheory.AdelicIntegrable

end
