import Development.WeilBound.ThetaLifts.FrameEstimates.IntMvPolynomialCoeffAbsSumMulLe

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Introduce `hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m`. Take `⟨N, hN⟩` from `hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'`. Use `⟨N + m * (n + 1), fun C hC => ?_⟩` and prove the remaining obligations. Take `⟨K, hK⟩` from `hN C hC`. Take `⟨c, hc, h⟩` from `hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC`.

Use `⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩` and prove the remaining obligations. Set `i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E))` to `fun x => ⟨x.1, trivial⟩`. Establish `hi : Function.Injective i` using `fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)`. Set `g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞` to `fun x => ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))`. Combine the equalities or inequalities in the displayed calculation.

Use `ENNReal.tsum_le_tsum fun x => ?_` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (by positivity)]`. Use `ENNReal.ofReal_le_ofReal ?_` and prove the remaining obligations. Establish `h1` using `h s hs t ht x.1 x.2`. Establish `hz` using `sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)`.

Unfold `maj`. Use `split_ifs with hx`. Establish `h2` using `pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))`. Rewrite `h2` using `[mul_pow, ← Real.exp_nat_mul, show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp]`. Rewrite using `[pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]`.

Conclude with `mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)`. Simplify using the standard rewrite rules. Use `_ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by`. Rewrite using `[ENNReal.tsum_mul_left]`. Use `gcongr`.

Conclude with `(ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)`. Use `_ = _ := by`. Rewrite using `[ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.coe_mul]`. Express the relevant statement in the definitionally equal form `_ = ENNReal.ofReal _ * _ * _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem latFull_of : LatTor → Minor → LatFull := by
  intro hT hM F E _ _ _ _ _ σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' m
  obtain ⟨N, hN⟩ := hT F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr'
  refine ⟨N + m * (n + 1), fun C hC => ?_⟩
  obtain ⟨K, hK⟩ := hN C hC
  obtain ⟨c, hc, h⟩ := hM F E σ hσ τ n d J J' hJ hJ' fr fr' hfr hfr' C hC
  refine ⟨((c ^ (m * (n + 1)))⁻¹).toNNReal * K, fun s hs t ht => ?_⟩
  let i : fullRank E n d → (Set.univ : Set (Matrix (Fin n) (Fin d) E)) := fun x => ⟨x.1, trivial⟩
  have hi : Function.Injective i := fun x y hxy => Subtype.ext (Subtype.mk.inj hxy)
  let g : ↥(Set.univ : Set (Matrix (Fin n) (Fin d) E)) → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (maj τ C N (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ))
  calc _ ≤ ∑' x, ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) * g (i x) := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 := h s hs t ht x.1 x.2
        have hz := sz_nonneg τ (mat (fr.a s)⁻¹ * incM F x.1 * (mat (fr'.a t)⁻¹)ᵀ)
        unfold maj
        split_ifs with hx
        · have h2 := pow_le_pow_left₀ (by positivity) (h1 hx) (m * (n + 1))
          rw [mul_pow, ← Real.exp_nat_mul,
            show ((m * (n + 1) : ℕ) : ℝ) * (viol s t / (n + 1)) = m * viol s t by push_cast; field_simp] at h2
          rw [pow_add, mul_inv, mul_comm, Real.exp_neg, ← mul_inv (c ^ _)]
          exact mul_le_mul_of_nonneg_right (inv_anti₀ (by positivity) h2) (by positivity)
        · simp
    _ ≤ ENNReal.ofReal ((c ^ (m * (n + 1)))⁻¹ * Real.exp (-(m * viol s t))) *
          (K * ENNReal.ofReal (Real.exp (Module.finrank ℚ E * posWt n d s t))) := by
        rw [ENNReal.tsum_mul_left]
        gcongr
        exact (ENNReal.tsum_comp_le_tsum_of_injective hi g).trans (hK s hs t ht)
    _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le,
          ENNReal.coe_mul]
        change _ = ENNReal.ofReal _ * _ * _
        ring

end PositivityTheory.ThKEst

end
