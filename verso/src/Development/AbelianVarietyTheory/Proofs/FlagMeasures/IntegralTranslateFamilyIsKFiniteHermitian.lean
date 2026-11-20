import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace GlobalTheory.KFinAvg

/- English proof (translation)
Use `haveI := hμ.1`. Establish `hK` using `isCompact_KH k r`. Establish `hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)` using `fun g hg => hg.1`. Establish `hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r)` using `hf.continuousOn.smul ((hσ.2.2 v).mono hsub)`. Establish `hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ` using `hc.integrableOn_compact hK`.

Establish `hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ` using `Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)`. Rewrite `hI` using `[IntegrableOn, hr]`. Conclude with `hI`.
-/
theorem integrable_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hf : Continuous f) (v : H) :
    Integrable (fun g => f g • σ g v) μ := by
  haveI := hμ.1
  have hK := isCompact_KH k r
  have hsub : GlobalTheory.ThA.KH k r ⊆ Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r) := fun g hg => hg.1
  have hc : ContinuousOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) :=
    hf.continuousOn.smul ((hσ.2.2 v).mono hsub)
  have hI : IntegrableOn (fun g => f g • σ g v) (GlobalTheory.ThA.KH k r) μ := hc.integrableOn_compact hK
  have hr : μ.restrict (GlobalTheory.ThA.KH k r) = μ :=
    Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hμ.2.1)
  rw [IntegrableOn, hr] at hI
  exact hI

/- English proof (translation)
Repeatedly rewrite using `[Finset.sum_smul, mul_smul]`. Rewrite using `[integral_finset_sum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) : Integrable (fun g => c j • (b j g • σ g v)) μ))]`. Repeatedly rewrite using `[integral_smul]`.
-/
theorem integral_sum_smul_orbit {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)}
    {μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ) (hμ : IsHaarKH k r μ)
    {N : ℕ} {b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ} (hb : ∀ j, Continuous (b j))
    (c : Fin N → ℂ) (v : H) :
    ∫ g, (∑ j, c j * b j g) • σ g v ∂μ = ∑ j, c j • ∫ g, b j g • σ g v ∂μ := by
  simp_rw [Finset.sum_smul, mul_smul]
  rw [integral_finset_sum Finset.univ (f := fun j g => c j • (b j g • σ g v)) (fun j _ => (Integrable.smul (c j) (integrable_smul_orbit hσ hμ (hb j) v) :
      Integrable (fun g => c j • (b j g • σ g v)) μ))]
  simp_rw [integral_smul]

end GlobalTheory.KFinAvg

namespace GlobalTheory.KFinAvg

/- English proof (translation)
Introduce `k r H _ _ _ σ μ hσ hμ N b hb hinv c v`. Take `⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ` from `⟨_, fun _ => rfl⟩`. Establish `key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j`. Introduce `c'`. Rewrite using `[integral_sum_smul_orbit hσ hμ hb c' v]`.

Repeatedly rewrite using `[hw]`. Establish `hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w)` using `fun c' => Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))`. Use `⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[key]`. Conclude with `hmem c`.

Introduce `a ha x hx`. Establish `hu : star a * a = 1` using `ha.2.1`. Establish `haa : a⁻¹ * a = 1` using `by rw [Matrix.inv_eq_left_inv hu]; exact hu`. Establish `hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r` using `by rw [ae_iff]; exact hμ.2.1`. Establish `hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w)`.

Introduce `j`. Take `⟨d, hd⟩` from `hinv a⁻¹ j`. Establish `h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ`. Rewrite using `[hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]`. Use `integral_congr_ae ?_` and prove the remaining obligations.

Use `filter_upwards [hae] with g hg`. Rewrite using `[map_smul, hσ.1.2 a ha.1 g hg.1]`. Both sides reduce to the same expression. Establish `hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g)` using `continuous_const.matrix_mul continuous_id`. Establish `h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ` using `by conv_rhs => rw [← hμ.2.2.1 a ha]`.

Rewrite using `[integral_map hcm.aemeasurable]`. Simplify using `only [← Matrix.mul_assoc, haa, Matrix.one_mul]`. Rewrite using `[hμ.2.2.1 a ha]`. Conclude with `(integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable`. Rewrite using `[h1, h2]`.

Repeatedly rewrite using `[hd]`. Rewrite using `[key]`. Conclude with `hmem d`. Establish `hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `hgen j`. Conclude with `hle hx`.
-/
theorem isKFinHpk_integral_translates : ∀ (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)), Formalism.MainNotions.S.IsURepOn (Formalism.QuantumDeterminants.UH (PI.UpqRep.Hpk k r)) σ → GlobalTheory.KFinAvg.IsHaarKH k r μ → ∀ (N : ℕ) (b : Fin N → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℂ), (∀ j, Continuous (b j)) → (∀ (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (j : Fin N), ∃ d : Fin N → ℂ, ∀ g, b j (a * g) = ∑ i, d i * b i g) → ∀ (c : Fin N → ℂ) (v : H), PI.UpqRep.IsKFinHpk (k := k) (r := r) σ (∫ g, (∑ j, c j * b j g) • σ g v ∂μ) := by
  intro k r H _ _ _ σ μ hσ hμ N b hb hinv c v
  obtain ⟨w, hw⟩ : ∃ w : Fin N → H, ∀ j, w j = ∫ g, b j g • σ g v ∂μ := ⟨_, fun _ => rfl⟩
  have key : ∀ c' : Fin N → ℂ, ∫ g, (∑ j, c' j * b j g) • σ g v ∂μ = ∑ j, c' j • w j := by
    intro c'
    rw [integral_sum_smul_orbit hσ hμ hb c' v]
    simp_rw [hw]
  have hmem : ∀ c' : Fin N → ℂ, ∑ j, c' j • w j ∈ Submodule.span ℂ (Set.range w) := fun c' =>
    Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  refine ⟨Submodule.span ℂ (Set.range w), FiniteDimensional.span_of_finite ℂ (Set.finite_range w), ?_, ?_⟩
  · rw [key]; exact hmem c
  · intro a ha x hx
    have hu : star a * a = 1 := ha.2.1
    have haa : a⁻¹ * a = 1 := by rw [Matrix.inv_eq_left_inv hu]; exact hu
    have hae : ∀ᵐ g ∂μ, g ∈ GlobalTheory.ThA.KH k r := by rw [ae_iff]; exact hμ.2.1
    have hgen : ∀ j, σ a (w j) ∈ Submodule.span ℂ (Set.range w) := by
      intro j
      obtain ⟨d, hd⟩ := hinv a⁻¹ j
      have h1 : σ a (w j) = ∫ g, b j g • σ (a * g) v ∂μ := by
        rw [hw, ← (σ a).integral_comp_comm (integrable_smul_orbit hσ hμ (hb j) v)]
        refine integral_congr_ae ?_
        filter_upwards [hae] with g hg
        rw [map_smul, hσ.1.2 a ha.1 g hg.1]
        rfl
      have hcm : Continuous (fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => a * g) :=
        continuous_const.matrix_mul continuous_id
      have h2 : ∫ g, b j g • σ (a * g) v ∂μ = ∫ g, b j (a⁻¹ * g) • σ g v ∂μ := by
        conv_rhs => rw [← hμ.2.2.1 a ha]
        rw [integral_map hcm.aemeasurable]
        · simp only [← Matrix.mul_assoc, haa, Matrix.one_mul]
        · rw [hμ.2.2.1 a ha]
          exact (integrable_smul_orbit hσ hμ ((hb j).comp (continuous_const.matrix_mul continuous_id)) v).aestronglyMeasurable
      rw [h1, h2]
      simp_rw [hd]
      rw [key]
      exact hmem d
    have hle : Submodule.span ℂ (Set.range w) ≤ (Submodule.span ℂ (Set.range w)).comap (σ a).toLinearMap := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact hgen j
    exact hle hx

end GlobalTheory.KFinAvg
