import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

/- English proof (translation)
Establish `h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : (∫ x, g x ∂μ) * (1 - z) = 0` using `by rw [mul_sub, mul_one, ← h1, sub_self]`. Break down `mul_eq_zero.1 h2 with h3 | h3` into its components or cases. Conclude with `h3`.

Conclude with `absurd (sub_eq_zero.1 h3).symm hz`.
-/
theorem integral_eq_zero_of_shift_mul {V : Type} [AddGroup V] [MeasurableSpace V] [MeasurableAdd V]
    (μ : Measure V) [μ.IsAddRightInvariant] (g : V → ℂ) (t : V) (z : ℂ) (hz : z ≠ 1)
    (h : ∀ x, g (x + t) = g x * z) : ∫ x, g x ∂μ = 0 := by
  have h1 : ∫ x, g x ∂μ = (∫ x, g x ∂μ) * z := by
    calc ∫ x, g x ∂μ = ∫ x, g (x + t) ∂μ := (integral_add_right_eq_self g t).symm
      _ = ∫ x, g x * z ∂μ := by simp only [h]
      _ = (∫ x, g x ∂μ) * z := integral_mul_const z g
  have h2 : (∫ x, g x ∂μ) * (1 - z) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.1 h3).symm hz

/- English proof (translation)
Establish `hR : 0 ≤ ‖x₀‖ / ε` using `div_nonneg (norm_nonneg _) hε.le`. Establish `hb' : ‖x₀‖ / ε < ‖b‖`. Simplify `hb` using `only [Metric.mem_closedBall, dist_zero_right, not_le]`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Conclude with `absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')`. Establish `hbi : b i ≠ 0`. Introduce `h0`. Rewrite `hi` using `[h0, norm_zero]`.

Conclude with `absurd hi (not_lt.2 hR)`. Use `⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Rewrite using `[Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]`.

Rewrite `hi` using `[div_lt_iff₀ hε]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Pi.single_eq_of_ne hj, norm_zero]`. Conclude with `hε`. Rewrite using `[single_dotProduct, div_mul_cancel₀ _ hbi]`.
-/
theorem exists_short_dot_eq {F : Type} [NormedField F] {r : ℕ} (x₀ : F) {ε : ℝ} (hε : 0 < ε) (b : Fin r → F)
    (hb : b ∉ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε)) :
    ∃ t : Fin r → F, ‖t‖ < ε ∧ t ⬝ᵥ b = x₀ := by
  have hR : 0 ≤ ‖x₀‖ / ε := div_nonneg (norm_nonneg _) hε.le
  have hb' : ‖x₀‖ / ε < ‖b‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hb
  obtain ⟨i, hi⟩ : ∃ i, ‖x₀‖ / ε < ‖b i‖ := by
    by_contra hcon
    push Not at hcon
    exact absurd ((pi_norm_le_iff_of_nonneg hR).2 hcon) (not_le.2 hb')
  have hbi : b i ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hi
    exact absurd hi (not_lt.2 hR)
  refine ⟨Pi.single i (x₀ / b i), (pi_norm_lt_iff hε).2 fun j => ?_, ?_⟩
  · by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same, norm_div, div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hε] at hi
      calc ‖x₀‖ < ‖b j‖ * ε := hi
        _ = ε * ‖b j‖ := mul_comm _ _
    · rw [Pi.single_eq_of_ne hj, norm_zero]
      exact hε
  · rw [single_dotProduct, div_mul_cancel₀ _ hbi]

/- English proof (translation)
Introduce `F E _ _ _ _ _ r M ψ hψ f' hf' hU`. Use `letI := M.mF`. Use `haveI := M.bF`. Use `haveI := M.haarF`. Use `haveI : LocallyCompactSpace F := Unram.lcF (E := E)`.

Use `haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F`. Take `⟨U, hU0, hUinv⟩` from `hU`. Take `⟨x₀, hx₀, -⟩` from `hψ.2`. Use `set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ`. Use `haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance`.

Establish `h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F)` using `rfl`. Choose the witnesses or unpack the hypotheses as in `⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε → ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by`. Establish `hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))` using `by fun_prop`. Establish `hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → F)` using `hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hm`.

Conclude with `⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩`. Choose the witnesses or unpack the hypotheses as in `⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε → ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by`. Establish `hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))` using `by fun_prop`. Establish `hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → F)` using `hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hm`.

Conclude with `⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩`. Establish `key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 → f' (A, b + t, c, l) = f' (A, b, c, l)`. Introduce `A b c l t ht`. Use `hUinv (A, b, c, l) _ (hB t ht)` as an intermediate fact. Simplify `this` using `only [Prod.mk_add_mk, add_zero]`.

Establish `key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 → f' (A, b, c + t, l) = f' (A, b, c, l)`. Introduce `A b c l t ht`. Use `hUinv (A, b, c, l) _ (hC t ht)` as an intermediate fact. Simplify `this` using `only [Prod.mk_add_mk, add_zero]`. Set `P : Set (Matrix (Fin r) (Fin r) F × F)` to `(fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'`.

Establish `hPc : IsCompact P` using `hf'.2.image (by fun_prop)`. Set `K : Set (Gl r F)` to `(fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) '' (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))`. Establish `hKc : IsCompact K` using `(hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)`. Use `HasCompactSupport.intro hKc fun Y hY => ?_` and prove the remaining obligations. Take `⟨A, b, c, l⟩` from `Y`.

Use `show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0`. Distinguish the cases in `hP : (A, l) ∈ P`. Distinguish the cases in `hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)`. Distinguish the cases in `hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)`. Conclude with `absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY`.

Take `⟨t, ht, htc⟩` from `exists_short_dot_eq x₀ hε2 c hc`. Use `integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_` and prove the remaining obligations. Rewrite using `[← integral_mul_const]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc, mul_assoc]`. Take `⟨t, ht, htb⟩` from `exists_short_dot_eq x₀ hε3 b hb`. Establish `hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0`. Introduce `b'`. Use `integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_` and prove the remaining obligations.

Rewrite using `[key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]`. Simplify using `only [hin, integral_zero]`. Establish `hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0`. Introduce `b' c'`. Assume the negation of the conclusion as `hne`.

Conclude with `hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩`. Simplify using `only [hz, zero_mul, integral_zero]`.
-/
theorem fourG_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ →
    ∀ f' : Gl r F → ℂ, IsTest f' → (∃ U ∈ 𝓝 (0 : Gl r F), ∀ Y : Gl r F, ∀ u ∈ U, f' (Y + u) = f' Y) →
    HasCompactSupport (fourG M ψ f') := by
  intro F E _ _ _ _ _ r M ψ hψ f' hf' hU
  letI := M.mF
  haveI := M.bF
  haveI := M.haarF
  haveI : LocallyCompactSpace F := Unram.lcF (E := E)
  haveI : ProperSpace F := ProperSpace.of_locallyCompactSpace F
  obtain ⟨U, hU0, hUinv⟩ := hU
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set μ : Measure (Fin r → F) := Measure.pi fun _ : Fin r => M.μF with hμ
  haveI : μ.IsAddHaarMeasure := by rw [hμ]; infer_instance
  have h00 : ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), (0 : Fin r → F), (0 : F)) = (0 : Gl r F) := rfl
  obtain ⟨ε2, hε2, hB⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), t, (0 : Fin r → F), (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  obtain ⟨ε3, hε3, hC⟩ : ∃ ε > 0, ∀ t : Fin r → F, ‖t‖ < ε →
      ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) ∈ U := by
    have hc : Continuous fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F)) := by
      fun_prop
    have hm : (fun t : Fin r → F => ((0 : Matrix (Fin r) (Fin r) F), (0 : Fin r → F), t, (0 : F))) ⁻¹' U ∈
        𝓝 (0 : Fin r → F) := hc.continuousAt.preimage_mem_nhds (by rw [h00]; exact hU0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hm
    exact ⟨ε, hε, fun t ht => hball (by simpa only [Metric.mem_ball, dist_zero_right] using ht)⟩
  have key2 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε2 →
      f' (A, b + t, c, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hB t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  have key3 : ∀ (A : Matrix (Fin r) (Fin r) F) (b c : Fin r → F) (l : F) (t : Fin r → F), ‖t‖ < ε3 →
      f' (A, b, c + t, l) = f' (A, b, c, l) := by
    intro A b c l t ht
    have := hUinv (A, b, c, l) _ (hC t ht)
    simpa only [Prod.mk_add_mk, add_zero] using this
  let P : Set (Matrix (Fin r) (Fin r) F × F) := (fun Y : Gl r F => (Y.1, Y.2.2.2)) '' tsupport f'
  have hPc : IsCompact P := hf'.2.image (by fun_prop)
  let K : Set (Gl r F) :=
    (fun p : (Matrix (Fin r) (Fin r) F × F) × (Fin r → F) × (Fin r → F) => ((p.1.1, p.2.1, p.2.2, p.1.2) : Gl r F)) ''
      (P ×ˢ (Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3) ×ˢ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)))
  have hKc : IsCompact K :=
    (hPc.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).image (by fun_prop)
  refine HasCompactSupport.intro hKc fun Y hY => ?_
  obtain ⟨A, b, c, l⟩ := Y
  show ∫ b', ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ ∂μ = 0
  by_cases hP : (A, l) ∈ P
  · by_cases hb : b ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε3)
    · by_cases hc : c ∈ Metric.closedBall (0 : Fin r → F) (‖x₀‖ / ε2)
      · exact absurd ⟨((A, l), b, c), ⟨hP, hb, hc⟩, rfl⟩ hY
      · obtain ⟨t, ht, htc⟩ := exists_short_dot_eq x₀ hε2 c hc
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun b' => ?_
        rw [← integral_mul_const]
        refine integral_congr_ae (Filter.Eventually.of_forall fun c' => ?_)
        simp only
        rw [key2 A b' c' l t ht, dotProduct_add, ← add_assoc, AddChar.map_add_eq_mul, dotProduct_comm c t, htc,
          mul_assoc]
    · obtain ⟨t, ht, htb⟩ := exists_short_dot_eq x₀ hε3 b hb
      have hin : ∀ b' : Fin r → F, ∫ c', f' (A, b', c', l) * ψ (c' ⬝ᵥ b + c ⬝ᵥ b') ∂μ = 0 := by
        intro b'
        refine integral_eq_zero_of_shift_mul μ _ t (ψ x₀) hx₀ fun c' => ?_
        rw [key3 A b' c' l t ht, add_dotProduct, add_right_comm, AddChar.map_add_eq_mul, htb, mul_assoc]
      simp only [hin, integral_zero]
  · have hz : ∀ b' c' : Fin r → F, f' (A, b', c', l) = 0 := by
      intro b' c'
      by_contra hne
      exact hP ⟨(A, b', c', l), subset_tsupport _ hne, rfl⟩
    simp only [hz, zero_mul, integral_zero]

end GlobalTheory.JR
