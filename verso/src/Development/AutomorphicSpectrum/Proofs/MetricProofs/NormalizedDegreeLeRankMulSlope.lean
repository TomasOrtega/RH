import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull

open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.DegSlope

/- English proof (translation)
Unfold `HermitianBundle.degreeWith`. Establish `h0 : ∀ i, ((f i : E.carrier)) = 0` using `fun i => (Submodule.mem_bot _).1 (f i).2`. Establish `hcard : Nat.card (↥(⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range f)) = 1`. Rewrite using `[Nat.card_eq_one_iff_unique]`. Use `⟨⟨fun a b => Quotient.inductionOn₂' a b (fun x y => congrArg _ (Subsingleton.elim x y))⟩, ⟨0⟩⟩` and prove the remaining obligations.

Establish `hdet : ∀ σ : K →+* ℂ, Real.log ‖E.gramDet σ (fun i => ((f i : E.carrier)))‖ = 0`. Introduce `σ`. Unfold `HermitianBundle.gramDet`. Simplify using `only [h0, TensorProduct.tmul_zero, inner_zero_left]`. Break down `Nat.eq_zero_or_pos r with rfl | hr` into its components or cases.

Simplify using the standard rewrite rules. Use `haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩`. Establish `hc : (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier)) = 0`. Establish `h : @inner ℂ _ (E.metric.form σ).toInner ((0 : Fibre σ E.carrier) + 0) 0 = @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 + @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0` using `(E.metric.form σ).add_left 0 0 0`. Rewrite `h` using `[add_zero]`.

Take the linear combination `-h`. Establish `hdet0 : (Matrix.of fun (_ : Fin r) (_ : Fin r) => (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det = 0`. Rewrite using `[show (Matrix.of fun (_ : Fin r) (_ : Fin r) => (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))) = 0 from Matrix.ext fun _ _ => hc]`. Conclude with `Matrix.det_zero`. Establish `hgoal : Real.log ‖(Matrix.of fun (_ : Fin r) (_ : Fin r) => (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det‖ = 0`.

Rewrite using `[hdet0, norm_zero, Real.log_zero]`. Conclude with `hgoal`. Rewrite using `[hcard]`. Simplify using `[hdet]`.
-/
private lemma degreeWith_bot {K : Type} [Field K] [NumberField K] (E : HermitianBundle.{0} K)
    {r : ℕ} (f : Fin r → ↥(⊥ : Submodule (𝓞 K) E.carrier)) : E.degreeWith ⊥ f = 0 := by
  unfold HermitianBundle.degreeWith
  have h0 : ∀ i, ((f i : E.carrier)) = 0 := fun i => (Submodule.mem_bot _).1 (f i).2
  have hcard : Nat.card (↥(⊥ : Submodule (𝓞 K) E.carrier) ⧸ Submodule.span (𝓞 K) (Set.range f)) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Quotient.inductionOn₂' a b (fun x y => congrArg _ (Subsingleton.elim x y))⟩, ⟨0⟩⟩
  have hdet : ∀ σ : K →+* ℂ, Real.log ‖E.gramDet σ (fun i => ((f i : E.carrier)))‖ = 0 := by
    intro σ
    unfold HermitianBundle.gramDet
    simp only [h0, TensorProduct.tmul_zero, inner_zero_left]
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · simp
    · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
      have hc : (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier)) = 0 := by
        have h : @inner ℂ _ (E.metric.form σ).toInner ((0 : Fibre σ E.carrier) + 0) 0 =
            @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 +
              @inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) 0 :=
          (E.metric.form σ).add_left 0 0 0
        rw [add_zero] at h
        linear_combination -h
      have hdet0 : (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det = 0 := by
        rw [show (Matrix.of fun (_ : Fin r) (_ : Fin r) =>
            (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))) = 0 from
          Matrix.ext fun _ _ => hc]
        exact Matrix.det_zero
      have hgoal : Real.log ‖(Matrix.of fun (_ : Fin r) (_ : Fin r) =>
          (@inner ℂ _ (E.metric.form σ).toInner (0 : Fibre σ E.carrier) (0 : Fibre σ E.carrier))).det‖ = 0 := by
        rw [hdet0, norm_zero, Real.log_zero]
      exact hgoal
  rw [hcard]
  simp [hdet]

/- English proof (translation)
Introduce `K _ _ E μ hμ F`. Distinguish the cases in `hF : F = ⊥`. Substitute `hF` using the available equality. Establish `hr : E.rank ⊥ = 0`. Simplify using `[HermitianBundle.rank]`.

Rewrite using `[hr, Nat.cast_zero, zero_mul]`. Unfold `HermitianBundle.normDegree HermitianBundle.degree`. Rewrite using `[degreeWith_bot, zero_div]`. Establish `hpos : 0 < E.rank F`. Unfold `HermitianBundle.rank`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hF`. Conclude with `Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩`. Establish `h1 : (E.slope F : EReal) ≤ E.slopeMax` using `le_iSup₂ (f := fun G (_ : G ≠ ⊥) => (E.slope G : EReal)) F hF`. Establish `h2 : E.slope F ≤ μ` using `EReal.coe_le_coe_iff.1 (h1.trans hμ)`. Unfold `HermitianBundle.slope at h2`.

Rewrite `h2` using `[div_le_iff₀ (by exact_mod_cast hpos)]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem normDegree_le_rank_mul_of_slopeMax_le : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (μ : ℝ), E.slopeMax ≤ (μ : EReal) → ∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E.rank F * μ := by
  intro K _ _ E μ hμ F
  by_cases hF : F = ⊥
  · subst hF
    have hr : E.rank ⊥ = 0 := by
      simp [HermitianBundle.rank]
    rw [hr, Nat.cast_zero, zero_mul]
    unfold HermitianBundle.normDegree HermitianBundle.degree
    rw [degreeWith_bot, zero_div]
  · have hpos : 0 < E.rank F := by
      unfold HermitianBundle.rank
      obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF
      exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨x, hx⟩, by simpa using hx0⟩
    have h1 : (E.slope F : EReal) ≤ E.slopeMax :=
      le_iSup₂ (f := fun G (_ : G ≠ ⊥) => (E.slope G : EReal)) F hF
    have h2 : E.slope F ≤ μ := EReal.coe_le_coe_iff.1 (h1.trans hμ)
    unfold HermitianBundle.slope at h2
    rw [div_le_iff₀ (by exact_mod_cast hpos)] at h2
    linarith

end GlobalTheory.CompanionTheory.Ar.DegSlope
