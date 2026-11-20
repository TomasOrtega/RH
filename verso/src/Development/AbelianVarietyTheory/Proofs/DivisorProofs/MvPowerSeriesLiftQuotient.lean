import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

/- English proof (translation)
Introduce `O σ _ I`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `g`. Set `s : O ⧸ I → O` to `fun x => if x = 0 then 0 else Quotient.out x`. Establish `hs : ∀ x, Ideal.Quotient.mk I (s x) = x`.

Introduce `x`. Distinguish the cases in `hx : x = 0`. Simplify using `[s, hx]`. Simplify using `only [s, if_neg hx]`. Conclude with `Ideal.Quotient.mk_out x`.

Set `f : MvPowerSeries σ O` to `fun α => s (coeff α g)`. Use `⟨f, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `α`. Rewrite using `[coeff_map]`. Conclude with `hs _`.

Introduce `h0`. Establish `: coeff (0 : σ →₀ ℕ) g = 0` using `by simpa [coeff_zero_eq_constantCoeff_apply] using h0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Use `show s (coeff 0 g) = 0`. Simplify using `[s, this]`.

Introduce `f`. Prove the components needed by the constructor for the conclusion. Introduce `h α`. Use `congrArg (coeff α) h` as an intermediate fact. Rewrite `this` using `[coeff_map, map_zero]`.

Conclude with `Ideal.Quotient.eq_zero_iff_mem.mp this`. Introduce `h`. Use extensionality with `α`. Rewrite using `[coeff_map, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.mpr (h α)`.

Introduce `a f`. Prove the components needed by the constructor for the conclusion. Introduce `h choose c hc using h`. Set `g : MvPowerSeries σ O` to `fun α => c α`. Establish `hg : ∀ α, coeff α g = c α` using `fun _ => rfl`.

Use `⟨g, ?_⟩` and prove the remaining obligations. Use extensionality with `α`. Rewrite using `[coeff_smul, hg, hc α]`. Introduce and unpack `⟨g, rfl⟩ α`. Rewrite using `[coeff_smul]`.

Conclude with `dvd_mul_right _ _`.
-/
theorem mvPowerSeries_lift_quotient :
    ∀ (O σ : Type) [CommRing O] (I : Ideal O), (∀ g : MvPowerSeries σ (O ⧸ I), ∃ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = g ∧ (constantCoeff g = 0 → constantCoeff f = 0)) ∧ (∀ f : MvPowerSeries σ O, map (Ideal.Quotient.mk I) f = 0 ↔ ∀ α, coeff α f ∈ I) ∧ ∀ (a : O) (f : MvPowerSeries σ O), (∀ α, a ∣ coeff α f) ↔ ∃ g, f = a • g := by
  classical
  intro O σ _ I
  refine ⟨?_, ?_, ?_⟩
  · intro g
    let s : O ⧸ I → O := fun x => if x = 0 then 0 else Quotient.out x
    have hs : ∀ x, Ideal.Quotient.mk I (s x) = x := by
      intro x
      by_cases hx : x = 0
      · simp [s, hx]
      · simp only [s, if_neg hx]
        exact Ideal.Quotient.mk_out x
    let f : MvPowerSeries σ O := fun α => s (coeff α g)
    refine ⟨f, ?_, ?_⟩
    · ext α
      rw [coeff_map]
      exact hs _
    · intro h0
      have : coeff (0 : σ →₀ ℕ) g = 0 := by simpa [coeff_zero_eq_constantCoeff_apply] using h0
      rw [← coeff_zero_eq_constantCoeff_apply]
      show s (coeff 0 g) = 0
      simp [s, this]
  · intro f
    constructor
    · intro h α
      have := congrArg (coeff α) h
      rw [coeff_map, map_zero] at this
      exact Ideal.Quotient.eq_zero_iff_mem.mp this
    · intro h
      ext α
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (h α)
  · intro a f
    constructor
    · intro h
      choose c hc using h
      let g : MvPowerSeries σ O := fun α => c α
      have hg : ∀ α, coeff α g = c α := fun _ => rfl
      refine ⟨g, ?_⟩
      ext α
      rw [coeff_smul, hg, hc α]
    · rintro ⟨g, rfl⟩ α
      rw [coeff_smul]
      exact dvd_mul_right _ _

end GlobalTheory
