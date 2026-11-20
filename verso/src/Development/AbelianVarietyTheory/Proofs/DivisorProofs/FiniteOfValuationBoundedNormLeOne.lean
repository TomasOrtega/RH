import Mathlib
open NumberField IsDedekindDomain Filter

namespace GlobalTheory.BCT.SuppFin

/- English proof (translation)
Establish `hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥`. Rewrite using `[← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]`. Conclude with `fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)`. Take `⟨d, hd, hd0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hJ`. Conclude with `⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩`.
-/
theorem exists_ne_zero_intValuation_le_of_finset {E : Type} [Field E] [NumberField E]
    (T : Finset (HeightOneSpectrum (𝓞 E))) (n : HeightOneSpectrum (𝓞 E) → ℕ) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ∀ v ∈ T, v.intValuation d ≤ WithZero.exp (-(n v : ℤ)) := by
  classical
  have hJ : (∏ v ∈ T, v.asIdeal ^ n v) ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
    exact fun v _ => pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact v.ne_bot)
  obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  exact ⟨d, hd0, fun v hv => (v.intValuation_le_pow_iff_mem d (n v)).mpr
    ((Ideal.prod_le_inf.trans (Finset.inf_le hv)) hd)⟩

/- English proof (translation)
Introduce `E _ _ X hN hcof hτ`. Use `choose N hN using hN`. Establish `hTf` using `Filter.eventually_cofinite.1 hcof`. Take `⟨d, hd0, hd⟩` from `exists_ne_zero_intValuation_le_of_finset (E := E) hTf.toFinset (fun w => (N w).toNat)`. Use `set d' : E := algebraMap (𝓞 E) E d with hd'`.

Establish `hd'0 : d' ≠ 0`. Rewrite using `[hd']`. Conclude with `(map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hd0`. Use `set B : ℝ := ∑ τ : E →+* ℂ, ‖τ d'‖ with hB`. Establish `hval : ∀ a ∈ X, ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (d' * a) ≤ 1`.

Introduce `a ha w`. Rewrite using `[map_mul, hd', HeightOneSpectrum.valuation_of_algebraMap]`. Distinguish the cases in `hw : w ∈ hTf.toFinset`. Establish `h1` using `hd w hw`. Establish `h2` using `hN w a ha`.

Establish `h3 : w.intValuation d ≤ WithZero.exp (-(N w))` using `h1.trans (WithZero.exp_le_exp.2 (by omega))`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : ∀ a ∈ X, w.valuation E a ≤ 1`. Simplify `hw` using `[Set.Finite.mem_toFinset]`. Conclude with `mul_le_one' (w.intValuation_le_one d) (h2 a ha)`.

Establish `himg : (fun x => d' * x) '' X ⊆ {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B}`. Introduce and unpack `_ ⟨a, ha, rfl⟩`. Use `⟨?_, fun φ => ?_⟩` and prove the remaining obligations. Take `⟨r, hr⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one E (d' * a) (hval a ha) show IsIntegral ℤ (d' * a)`. Rewrite using `[← hr]`.

Conclude with `RingOfIntegers.isIntegral_coe r`. Use `show ‖φ (d' * a)‖ ≤ B`. Rewrite using `[map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `Set.Finite.of_finite_image ((NumberField.Embeddings.finite_of_norm_le E ℂ B).subset himg) (fun x _ y _ hxy => mul_left_cancel₀ hd'0 hxy)`.
-/
theorem finite_of_valuation_bounded_of_norm_le_one :
    ∀ (E : Type) [Field E] [NumberField E] (X : Set E),
      (∀ w : HeightOneSpectrum (𝓞 E), ∃ N : ℤ, ∀ a ∈ X, w.valuation E a ≤ WithZero.exp N) →
      (∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∀ a ∈ X, w.valuation E a ≤ 1) →
      (∀ a ∈ X, ∀ τ : E →+* ℂ, ‖τ a‖ ≤ 1) → X.Finite := by
  intro E _ _ X hN hcof hτ
  classical
  choose N hN using hN
  have hTf := Filter.eventually_cofinite.1 hcof
  obtain ⟨d, hd0, hd⟩ := exists_ne_zero_intValuation_le_of_finset (E := E) hTf.toFinset
    (fun w => (N w).toNat)
  set d' : E := algebraMap (𝓞 E) E d with hd'
  have hd'0 : d' ≠ 0 := by
    rw [hd']; exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).2 hd0
  set B : ℝ := ∑ τ : E →+* ℂ, ‖τ d'‖ with hB
  have hval : ∀ a ∈ X, ∀ w : HeightOneSpectrum (𝓞 E), w.valuation E (d' * a) ≤ 1 := by
    intro a ha w
    rw [map_mul, hd', HeightOneSpectrum.valuation_of_algebraMap]
    by_cases hw : w ∈ hTf.toFinset
    · have h1 := hd w hw
      have h2 := hN w a ha
      have h3 : w.intValuation d ≤ WithZero.exp (-(N w)) :=
        h1.trans (WithZero.exp_le_exp.2 (by omega))
      calc w.intValuation d * w.valuation E a ≤ WithZero.exp (-(N w)) * WithZero.exp (N w) :=
            mul_le_mul' h3 h2
        _ = 1 := by rw [← WithZero.exp_add]; simp
    · have h2 : ∀ a ∈ X, w.valuation E a ≤ 1 := by
        simpa [Set.Finite.mem_toFinset] using hw
      exact mul_le_one' (w.intValuation_le_one d) (h2 a ha)
  have himg : (fun x => d' * x) '' X ⊆
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ B} := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨?_, fun φ => ?_⟩
    · obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (d' * a) (hval a ha)
      show IsIntegral ℤ (d' * a)
      rw [← hr]
      exact RingOfIntegers.isIntegral_coe r
    · show ‖φ (d' * a)‖ ≤ B
      rw [map_mul, norm_mul]
      calc ‖φ d'‖ * ‖φ a‖ ≤ ‖φ d'‖ * 1 :=
            mul_le_mul_of_nonneg_left (hτ a ha φ) (norm_nonneg _)
        _ = ‖φ d'‖ := mul_one _
        _ ≤ B := Finset.single_le_sum (f := fun τ : E →+* ℂ => ‖τ d'‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ φ)
  exact Set.Finite.of_finite_image ((NumberField.Embeddings.finite_of_norm_le E ℂ B).subset himg)
    (fun x _ y _ hxy => mul_left_cancel₀ hd'0 hxy)

end GlobalTheory.BCT.SuppFin
