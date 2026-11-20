import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanFundamentalDomainOfLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AffineChangeFundamentalDomainMeanPeriodicStatement

open MeasureTheory

namespace GlobalTheory.PeriodicMean

/- English proof (translation)
Introduce `g Λ Λ' Fd Fd' h u u' p n v T hΛc hΛ'c hF hF' hp hh hu hu' hpu hpu' hm hm' hT`. Establish `hV : 0 < (volume Fd).toReal`. Break down `(ENNReal.toReal_nonneg (a := volume Fd)).lt_or_eq with h0 | h0` into its components or cases. Conclude with `h0`. Rewrite `hm` using `[← h0, div_zero]`.

Conclude with `absurd hm zero_ne_one`. Establish `hVt : volume Fd ≠ ⊤` using `fun h0 => by simp [h0] at hV`. Establish `hA1 : IntegrableOn (fun z => u' (h z) ^ 2) Fd volume ∧ (∫ z in Fd, u' (h z) ^ 2) / (volume Fd).toReal = 1`. Set `Λ₁ : AddSubgroup (Fin g → ℂ)` to `Λ'.comap (h.toLinearMap.toAddMonoidHom)`. Establish `hc : Countable Λ₁`.

Establish `: Function.Injective (fun x : Λ₁ => (⟨h x, x.2⟩ : Λ'))` using `fun x y hxy => Subtype.ext (h.injective (congrArg Subtype.val hxy))`. Conclude with `this.countable`. Take `⟨hD, hmD⟩` from `GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ' Λ₁ Fd' h 0 (fun z => u' z ^ 2) hΛ'c (fun z => Iff.rfl) hF' (fun a ha z => by simp only [hpu' a ha z]) hm'`. Conclude with `GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u' (h z) ^ 2) hc (fun a ha => hh a ha) hF hD hVt (fun a ha z => by`. Establish `: h (z + a) = h z + h a` using `map_add h z a`.

Rewrite using `[this, hpu' (h a) ha]) (by simpa using hmD)`. Establish `hA2 : ∀ m, IntegrableOn (fun z => u ((p : ℂ) • z + v m) ^ 2) Fd volume ∧ (∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2) / (volume Fd).toReal = 1`. Introduce `m`. Establish `hp0 : (p : ℂ) ≠ 0` using `by exact_mod_cast hp.ne'`. Set `L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)` to `LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0`.

Set `Λ₁ : AddSubgroup (Fin g → ℂ)` to `Λ.comap (L.toLinearMap.toAddMonoidHom)`. Establish `hc : Countable Λ₁`. Establish `: Function.Injective (fun x : Λ₁ => (⟨L x, x.2⟩ : Λ))` using `fun x y hxy => Subtype.ext (L.injective (congrArg Subtype.val hxy))`. Conclude with `this.countable`. Take `⟨hD, hmD⟩` from `GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ Λ₁ Fd L (v m) (fun z => u z ^ 2) hΛc (fun z => Iff.rfl) hF (fun a ha z => by simp only [hpu a ha z]) hm`.

Use `GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u ((p : ℂ) • z + v m) ^ 2) hc ?_ hF hD hVt ?_ hmD` and prove the remaining obligations. Introduce `a ha`. Express the relevant statement in the definitionally equal form `(p : ℂ) • a ∈ Λ`. Establish `: (p : ℂ) • a = p • a` using `by rw [Nat.cast_smul_eq_nsmul]`. Rewrite using `[this]`.

Conclude with `Λ.nsmul_mem ha p`. Introduce `a ha z`. Establish `ha' : (p : ℂ) • a ∈ Λ` using `ha`. Establish `: (p : ℂ) • (z + a) + v m = ((p : ℂ) • z + v m) + (p : ℂ) • a` using `by rw [smul_add]; abel`. Simplify using `only [this, hpu _ ha']`.

Take `⟨hI1, hM1⟩` from `hA1`. Establish `hE1 : ∫ z in Fd, u' (h z) ^ 2 = (volume Fd).toReal`. Clear denominators, using `at hM1` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hE2 : ∀ m, ∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2 = (volume Fd).toReal` using `fun m => by`.

Use `(hA2 m).2` as an intermediate fact. Clear denominators, using `at this` for the nonvanishing conditions. Combine the linear equalities and inequalities to obtain the conclusion. Break down `le_or_gt T 0 with hT0 | hT0` into its components or cases. Conclude with `hT0.trans (Nat.cast_nonneg n)`.

Establish `hpt : ∀ z, T ^ 2 * u' (h z) ^ 2 ≤ (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2`. Introduce `z`. Establish `h0 : 0 ≤ T * u' (h z)` using `mul_nonneg hT0.le (hu' _)`. Combine the equalities or inequalities in the displayed calculation. Establish `hint : ∫ z in Fd, T ^ 2 * u' (h z) ^ 2 ≤ ∫ z in Fd, (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2`.

Use `integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) ?_ (Filter.Eventually.of_forall hpt)` and prove the remaining obligations. Conclude with `(integrable_finsetSum _ fun m _ => (hA2 m).1).const_mul _`. Rewrite `hint` using `[integral_const_mul, integral_const_mul, integral_finsetSum _ fun m _ => (hA2 m).1, hE1]`. Simplify using `only [hE2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint`. Establish `hT2 : T ^ 2 ≤ (n : ℝ) ^ 2` using `by nlinarith`.

Conclude with `abs_le_of_sq_le_sq' hT2 (Nat.cast_nonneg n) |>.2 |> fun h => h`.
-/
theorem mean_factor_le : ∀ (g : ℕ) (Λ Λ' : AddSubgroup (Fin g → ℂ)) (Fd Fd' : Set (Fin g → ℂ)) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (u u' : (Fin g → ℂ) → ℝ) (p n : ℕ) (v : Fin n → (Fin g → ℂ)) (T : ℝ), Countable Λ → Countable Λ' → MeasureTheory.IsAddFundamentalDomain Λ Fd MeasureTheory.volume → MeasureTheory.IsAddFundamentalDomain Λ' Fd' MeasureTheory.volume → 0 < p → (∀ a ∈ Λ, h a ∈ Λ') → (∀ z, 0 ≤ u z) → (∀ z, 0 ≤ u' z) → (∀ a ∈ Λ, ∀ z, u (z + a) = u z) → (∀ a ∈ Λ', ∀ z, u' (z + a) = u' z) → (∫ z in Fd, u z ^ 2) / (MeasureTheory.volume Fd).toReal = 1 → (∫ z in Fd', u' z ^ 2) / (MeasureTheory.volume Fd').toReal = 1 → (∀ z, T * u' (h z) ≤ ∑ m, u ((p : ℂ) • z + v m)) → T ≤ n := by
  intro g Λ Λ' Fd Fd' h u u' p n v T hΛc hΛ'c hF hF' hp hh hu hu' hpu hpu' hm hm' hT

  have hV : 0 < (volume Fd).toReal := by
    rcases (ENNReal.toReal_nonneg (a := volume Fd)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, div_zero] at hm; exact absurd hm zero_ne_one
  have hVt : volume Fd ≠ ⊤ := fun h0 => by simp [h0] at hV

  have hA1 : IntegrableOn (fun z => u' (h z) ^ 2) Fd volume ∧
      (∫ z in Fd, u' (h z) ^ 2) / (volume Fd).toReal = 1 := by
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ'.comap (h.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨h x, x.2⟩ : Λ')) := fun x y hxy =>
        Subtype.ext (h.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ' Λ₁ Fd' h 0 (fun z => u' z ^ 2) hΛ'c (fun z => Iff.rfl) hF'
      (fun a ha z => by simp only [hpu' a ha z]) hm'
    exact GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u' (h z) ^ 2) hc (fun a ha => hh a ha) hF hD hVt
      (fun a ha z => by
        have : h (z + a) = h z + h a := map_add h z a
        rw [this, hpu' (h a) ha]) (by simpa using hmD)

  have hA2 : ∀ m, IntegrableOn (fun z => u ((p : ℂ) • z + v m) ^ 2) Fd volume ∧
      (∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2) / (volume Fd).toReal = 1 := by
    intro m
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    let L : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) := LinearEquiv.smulOfNeZero ℂ (Fin g → ℂ) (p : ℂ) hp0
    let Λ₁ : AddSubgroup (Fin g → ℂ) := Λ.comap (L.toLinearMap.toAddMonoidHom)
    have hc : Countable Λ₁ := by
      have : Function.Injective (fun x : Λ₁ => (⟨L x, x.2⟩ : Λ)) := fun x y hxy =>
        Subtype.ext (L.injective (congrArg Subtype.val hxy))
      exact this.countable
    obtain ⟨hD, hmD⟩ := GlobalTheory.T.affine_change_fundamentalDomain_mean_periodic g Λ Λ₁ Fd L (v m) (fun z => u z ^ 2) hΛc (fun z => Iff.rfl) hF
      (fun a ha z => by simp only [hpu a ha z]) hm
    refine GlobalTheory.T.mean_fundamentalDomain_eq_one_of_le g Λ Λ₁ Fd _ (fun z => u ((p : ℂ) • z + v m) ^ 2) hc ?_ hF hD hVt ?_ hmD
    · intro a ha
      change (p : ℂ) • a ∈ Λ
      have : (p : ℂ) • a = p • a := by rw [Nat.cast_smul_eq_nsmul]
      rw [this]; exact Λ.nsmul_mem ha p
    · intro a ha z
      have ha' : (p : ℂ) • a ∈ Λ := ha
      have : (p : ℂ) • (z + a) + v m = ((p : ℂ) • z + v m) + (p : ℂ) • a := by rw [smul_add]; abel
      simp only [this, hpu _ ha']
  obtain ⟨hI1, hM1⟩ := hA1
  have hE1 : ∫ z in Fd, u' (h z) ^ 2 = (volume Fd).toReal := by
    field_simp at hM1; linarith
  have hE2 : ∀ m, ∫ z in Fd, u ((p : ℂ) • z + v m) ^ 2 = (volume Fd).toReal := fun m => by
    have := (hA2 m).2; field_simp at this; linarith
  rcases le_or_gt T 0 with hT0 | hT0
  · exact hT0.trans (Nat.cast_nonneg n)

  have hpt : ∀ z, T ^ 2 * u' (h z) ^ 2 ≤ (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    intro z
    have h0 : 0 ≤ T * u' (h z) := mul_nonneg hT0.le (hu' _)
    calc T ^ 2 * u' (h z) ^ 2 = (T * u' (h z)) ^ 2 := by ring
      _ ≤ (∑ m, u ((p : ℂ) • z + v m)) ^ 2 := pow_le_pow_left₀ h0 (hT z) 2
      _ ≤ (Finset.univ : Finset (Fin n)).card * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := sq_sum_le_card_mul_sum_sq
      _ = (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by simp
  have hint : ∫ z in Fd, T ^ 2 * u' (h z) ^ 2 ≤ ∫ z in Fd, (n : ℝ) * ∑ m, u ((p : ℂ) • z + v m) ^ 2 := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => by positivity) ?_
      (Filter.Eventually.of_forall hpt)
    exact (integrable_finsetSum _ fun m _ => (hA2 m).1).const_mul _
  rw [integral_const_mul, integral_const_mul, integral_finsetSum _ fun m _ => (hA2 m).1, hE1] at hint
  simp only [hE2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hint
  have hT2 : T ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
  exact abs_le_of_sq_le_sq' hT2 (Nat.cast_nonneg n) |>.2 |> fun h => h

end GlobalTheory.PeriodicMean
