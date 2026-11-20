import Mathlib
open SchwartzMap
open scoped FourierTransform SchwartzMap
open MeasureTheory

namespace GlobalTheory.ExpTypeDense

/- English proof (translation)
Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Simplify using the standard rewrite rules. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Chain the equalities or inequalities of the calculation. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. Simplify to obtain the desired conclusion from the available facts. Rewrite the hypotheses and the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem norm_iteratedFDeriv_fourier_le {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (h : 𝓢(E, ℂ)) {R : ℝ} (hR : 1 ≤ R) (hs : tsupport h ⊆ Metric.closedBall 0 R) (j : ℕ) (w : E) :
    ‖iteratedFDeriv ℝ j (𝓕 (h : E → ℂ)) w‖ ≤ (∫ v, ‖h v‖) * (4 * Real.pi * R) ^ j := by
  have key := Real.pow_mul_norm_iteratedFDeriv_fourier_le (f := (h : E → ℂ)) (K := (j : ℕ∞)) (N := 0)
    (h.smooth 0) (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume h k n) le_rfl le_rfl w
  simp only [pow_zero, one_mul, mul_one] at key
  have hI : ∀ p ∈ Finset.range (j + 1) ×ˢ Finset.range (0 + 1),
      ∫ v, ‖v‖ ^ p.1 * ‖iteratedFDeriv ℝ p.2 h v‖ ≤ R ^ j * ∫ v, ‖h v‖ := by
    intro p hp
    simp only [Finset.mem_product, Finset.mem_range, zero_add, Nat.lt_one_iff] at hp
    obtain ⟨a, b⟩ := p
    obtain ⟨hp1, hp2⟩ := hp
    simp only at hp1 hp2 ⊢
    subst hp2
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun v => by positivity)
      (h.integrable.norm.const_mul _) (Filter.Eventually.of_forall fun v => ?_)
    simp only [norm_iteratedFDeriv_zero]
    by_cases hv : h v = 0
    · simp [hv]
    · have hb : v ∈ Metric.closedBall (0 : E) R := hs (subset_tsupport _ hv)
      rw [Metric.mem_closedBall, dist_zero_right] at hb
      gcongr
      calc ‖v‖ ^ a ≤ R ^ a := by gcongr
        _ ≤ R ^ j := pow_le_pow_right₀ hR (by omega)
  have hsum := Finset.sum_le_sum hI
  rw [Finset.sum_const, Finset.card_product, Finset.card_range, Finset.card_range, nsmul_eq_mul] at hsum
  have hI0 : 0 ≤ ∫ v, ‖h v‖ := integral_nonneg fun v => norm_nonneg _
  have hj : ((j + 1 : ℕ) : ℝ) ≤ 2 ^ j := by exact_mod_cast (Nat.lt_two_pow_self : j < 2 ^ j)
  have hR0 : 0 ≤ R := by linarith
  calc ‖iteratedFDeriv ℝ j (𝓕 (h : E → ℂ)) w‖ ≤ _ := key
    _ ≤ (2 * Real.pi) ^ j * (((j + 1) * (0 + 1) : ℕ) * (R ^ j * ∫ v, ‖h v‖)) := by
        gcongr
    _ ≤ (2 * Real.pi) ^ j * (2 ^ j * (R ^ j * ∫ v, ‖h v‖)) := by
        gcongr
        simpa using hj
    _ = (∫ v, ‖h v‖) * (4 * Real.pi * R) ^ j := by
        rw [show (4 : ℝ) * Real.pi * R = 2 * (2 * Real.pi * R) by ring, mul_pow 2 (2 * Real.pi * R), mul_pow (2 * Real.pi)]; ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.
-/
theorem norm_iteratedFDeriv_comp_le {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (T : V →L[ℝ] E) {f : E → ℂ} {j : ℕ}
    (hf : ContDiff ℝ j f) (y : V) :
    ‖iteratedFDeriv ℝ j (f ∘ T) y‖ ≤ ‖iteratedFDeriv ℝ j f (T y)‖ * ‖T‖ ^ j := by
  rw [T.iteratedFDeriv_comp_right hf y le_rfl]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp

end GlobalTheory.ExpTypeDense

namespace GlobalTheory.ExpTypeDense

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem dense_expType :
    (∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W],
      Dense {φ : SchwartzMap W ℂ | HasCompactSupport (⇑φ)}) →
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V],
    Dense {ψ : SchwartzMap V ℂ | ∃ A ρ : ℝ, ∀ (j : ℕ) (y : V), ‖iteratedFDeriv ℝ j ψ y‖ ≤ A * ρ ^ j} := by
  intro hc V _ _ _
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let C := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T
  let Ci := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (F := ℂ) T.symm
  let Fe := SchwartzMap.fourierTransformCLE ℂ (E := 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ))
  let Φ : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] 𝓢(V, ℂ) :=
    C.comp (Fe : 𝓢(EuclideanSpace ℝ (Fin (Module.finrank ℝ V)), ℂ) →L[ℂ] _)
  have hsurj : Function.Surjective Φ := by
    intro ψ
    refine ⟨Fe.symm (Ci ψ), ?_⟩
    ext y
    simp [Φ, C, Ci]
  refine (hsurj.denseRange.dense_image Φ.continuous (hc _)).mono ?_
  rintro _ ⟨h, hh, rfl⟩
  obtain ⟨R, hR⟩ := hh.isCompact.isBounded.subset_closedBall 0
  refine ⟨∫ v, ‖h v‖, 4 * Real.pi * max R 1 * ‖(T : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))‖,
    fun j y => ?_⟩
  have e : ⇑(Φ h) = (𝓕 (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ)) ∘
      (T : V →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := by
    funext y
    simp only [Φ, C, ContinuousLinearMap.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rfl
  have hsm : ContDiff ℝ j (𝓕 (h : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ)) := (𝓕 h).smooth j
  have hI0 : 0 ≤ ∫ v, ‖h v‖ := integral_nonneg fun v => norm_nonneg _
  rw [e]
  refine (norm_iteratedFDeriv_comp_le _ hsm y).trans ?_
  rw [mul_pow, ← mul_assoc]
  gcongr
  exact norm_iteratedFDeriv_fourier_le h (le_max_right R 1)
    (hR.trans (Metric.closedBall_subset_closedBall (le_max_left R 1))) j _

end GlobalTheory.ExpTypeDense
