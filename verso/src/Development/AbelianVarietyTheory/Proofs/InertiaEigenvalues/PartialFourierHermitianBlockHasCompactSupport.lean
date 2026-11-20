import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `F E _ _ _ _ hUn r M ψ hψ htr f hf hloc`. Take `⟨U, hU, hfU⟩` from `hloc`. Use `haveI : CharZero F := hUn.charZero`. Use `haveI : LocallyCompactSpace E := hUn.lcE`. Use `haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E`.

Use `letI := M.mE`. Use `haveI := M.bE`. Use `haveI := M.haarE`. Take `⟨x₀, hx₀, -⟩` from `hψ.2`. Use `set a : E := algebraMap F E (x₀ / 2) with ha`.

Establish `htra : Algebra.trace F E a = x₀`. Apply `(algebraMap F E).injective` to reduce the goal to its premises. Rewrite using `[htr a, ha, hUn.star_fix, ← map_add, add_halves]`. Establish `hcont : Continuous (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)))` using `by fun_prop`. Establish `hpre : (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → E)` using `hcont.tendsto 0 hU`.

Take `⟨δ, hδ, hball⟩` from `Metric.mem_nhds_iff.1 hpre`. Establish `hzero : ∀ X : Hn r F E, ∀ i, ‖a‖ / δ < ‖X.2.1 i‖ → fourU M ψ f X = 0`. Introduce `X i hi`. Establish `hbi : X.2.1 i ≠ 0`. Introduce `h; rw [h, norm_zero] at hi; exact absurd hi (not_lt.2 (by positivity))`.

Use `set t : Fin r → E := Pi.single i (star (a / X.2.1 i)) with ht`. Establish `htn : ‖t‖ < δ`. Rewrite using `[ht, Pi.norm_single, hUn.norm_star, norm_div]`. Rewrite using `[div_lt_iff₀ (norm_pos_iff.2 hbi)]`. Rewrite `hi` using `[div_lt_iff₀ hδ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `htU : ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)) ∈ U` using `hball (mem_ball_zero_iff.2 htn)`. Establish `hst : star t ⬝ᵥ X.2.1 = a`. Rewrite using `[ht, ← Pi.single_star, single_dotProduct, star_star, div_mul_cancel₀ _ hbi]`. Establish `hshift : ∀ c, f (X.1, t + c, X.2.2) = f (X.1, c, X.2.2)`.

Introduce `c`. Use `hfU (X.1, c, X.2.2) _ htU` as an intermediate fact. Rewrite using `[← this]`. Use `congr 1`. Apply the tactic sequence `ext <;> simp [add_comm]`.

Establish `hchar : ∀ c : Fin r → E, ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) = ψ x₀ * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))`. Introduce `c`. Rewrite using `[star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul, hst, htra]`. Establish `key : fourU M ψ f X = ψ x₀ * fourU M ψ f X`. Simplify using `only [fourU]`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `c`. Rewrite using `[hshift, hchar]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ = _ := integral_const_mul _ _`. Establish `h1 : (1 - ψ x₀) * fourU M ψ f X = 0` using `by rw [sub_mul, one_mul, ← key, sub_self]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h).symm hx₀`. Conclude with `h`.

Establish `hzero2 : ∀ X : Hn r F E, (∀ c, f (X.1, c, X.2.2) = 0) → fourU M ψ f X = 0`. Introduce `X h`. Simplify using `[fourU, h]`. Establish `hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ (Metric.closedBall (0 : Fin r → E) (‖a‖ / δ) ×ˢ ((fun Y : Hn r F E => Y.2.2) '' tsupport f)))` using `(hf.2.image continuous_fst).prod ((isCompact_closedBall _ _).prod (hf.2.image (by fun_prop)))`. Use `HasCompactSupport.intro hK fun X hX => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Apply `hX` to reduce the goal to its premises. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h1`. Conclude with `hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h1 ⟨_, hc, rfl⟩)`.

Rewrite using `[mem_closedBall_zero_iff]`. Assume the negation of the conclusion as `h2`. Establish `hR : 0 ≤ ‖a‖ / δ` using `by positivity`. Rewrite `h2` using `[pi_norm_le_iff_of_nonneg hR]`. Use `push_neg at h2`.

Take `⟨i, hi⟩` from `h2`. Conclude with `hne (hzero X i hi)`. Assume the negation of the conclusion as `h3`. Conclude with `hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h3 ⟨_, hc, rfl⟩)`.
-/
theorem fourU_hasCompactSupport : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ), IsStdChar ψ → (∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y) → ∀ f : Hn r F E → ℂ, IsTest f → (∃ U ∈ 𝓝 (0 : Hn r F E), ∀ X : Hn r F E, ∀ u ∈ U, f (X + u) = f X) → HasCompactSupport (fourU M ψ f) := by
  intro F E _ _ _ _ hUn r M ψ hψ htr f hf hloc
  obtain ⟨U, hU, hfU⟩ := hloc
  haveI : CharZero F := hUn.charZero
  haveI : LocallyCompactSpace E := hUn.lcE
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  letI := M.mE
  haveI := M.bE
  haveI := M.haarE
  obtain ⟨x₀, hx₀, -⟩ := hψ.2
  set a : E := algebraMap F E (x₀ / 2) with ha
  have htra : Algebra.trace F E a = x₀ := by
    apply (algebraMap F E).injective
    rw [htr a, ha, hUn.star_fix, ← map_add, add_halves]

  have hcont : Continuous (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) := by
    fun_prop
  have hpre : (fun t : Fin r → E => ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F))) ⁻¹' U ∈ 𝓝 (0 : Fin r → E) :=
    hcont.tendsto 0 hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hpre

  have hzero : ∀ X : Hn r F E, ∀ i, ‖a‖ / δ < ‖X.2.1 i‖ → fourU M ψ f X = 0 := by
    intro X i hi
    have hbi : X.2.1 i ≠ 0 := by
      intro h; rw [h, norm_zero] at hi; exact absurd hi (not_lt.2 (by positivity))
    set t : Fin r → E := Pi.single i (star (a / X.2.1 i)) with ht
    have htn : ‖t‖ < δ := by
      rw [ht, Pi.norm_single, hUn.norm_star, norm_div]
      rw [div_lt_iff₀ (norm_pos_iff.2 hbi)]
      rw [div_lt_iff₀ hδ] at hi
      linarith
    have htU : ((0 : selfAdjoint (Matrix (Fin r) (Fin r) E)), t, (0 : F)) ∈ U :=
      hball (mem_ball_zero_iff.2 htn)
    have hst : star t ⬝ᵥ X.2.1 = a := by
      rw [ht, ← Pi.single_star, single_dotProduct, star_star, div_mul_cancel₀ _ hbi]
    have hshift : ∀ c, f (X.1, t + c, X.2.2) = f (X.1, c, X.2.2) := by
      intro c
      have := hfU (X.1, c, X.2.2) _ htU
      rw [← this]
      congr 1
      ext <;> simp [add_comm]
    have hchar : ∀ c : Fin r → E, ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) =
        ψ x₀ * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) := by
      intro c
      rw [star_add, add_dotProduct, map_add, AddChar.map_add_eq_mul, hst, htra]
    have key : fourU M ψ f X = ψ x₀ * fourU M ψ f X := by
      simp only [fourU]
      calc ∫ c, f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE)
          = ∫ c, f (X.1, t + c, X.2.2) * ψ (Algebra.trace F E (star (t + c) ⬝ᵥ X.2.1)) ∂(Measure.pi fun _ : Fin r => M.μE) :=
            (integral_add_left_eq_self (fun c => f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) t).symm
        _ = ∫ c, ψ x₀ * (f (X.1, c, X.2.2) * ψ (Algebra.trace F E (star c ⬝ᵥ X.2.1))) ∂(Measure.pi fun _ : Fin r => M.μE) := by
            congr 1; funext c; rw [hshift, hchar]; ring
        _ = _ := integral_const_mul _ _
    have h1 : (1 - ψ x₀) * fourU M ψ f X = 0 := by rw [sub_mul, one_mul, ← key, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hx₀
    · exact h

  have hzero2 : ∀ X : Hn r F E, (∀ c, f (X.1, c, X.2.2) = 0) → fourU M ψ f X = 0 := by
    intro X h
    simp [fourU, h]
  have hK : IsCompact ((Prod.fst '' tsupport f) ×ˢ (Metric.closedBall (0 : Fin r → E) (‖a‖ / δ) ×ˢ
      ((fun Y : Hn r F E => Y.2.2) '' tsupport f))) :=
    (hf.2.image continuous_fst).prod ((isCompact_closedBall _ _).prod (hf.2.image (by fun_prop)))
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra hne
  apply hX
  refine ⟨?_, ?_, ?_⟩
  · by_contra h1
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h1 ⟨_, hc, rfl⟩)
  · rw [mem_closedBall_zero_iff]
    by_contra h2
    have hR : 0 ≤ ‖a‖ / δ := by positivity
    rw [pi_norm_le_iff_of_nonneg hR] at h2
    push_neg at h2
    obtain ⟨i, hi⟩ := h2
    exact hne (hzero X i hi)
  · by_contra h3
    exact hne (hzero2 X fun c => image_eq_zero_of_notMem_tsupport fun hc => h3 ⟨_, hc, rfl⟩)

end GlobalTheory
