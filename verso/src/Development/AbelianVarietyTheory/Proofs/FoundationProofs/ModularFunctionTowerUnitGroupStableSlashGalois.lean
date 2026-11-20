import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OverAffineJLineComapSlGal
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem vs_valuation_eq_one_iff {K : Type} [Field K] (V : ValuationSubring K) {x : K} (hx : x ≠ 0) :
    V.valuation x = 1 ↔ x ∈ V ∧ x⁻¹ ∈ V := by
  rw [← V.valuation_le_one_iff, ← V.valuation_le_one_iff, map_inv₀]
  have h0 : V.valuation x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  constructor
  · intro h; simp [h]
  · rintro ⟨h1, h2⟩
    refine le_antisymm h1 ?_
    by_contra hlt
    push_neg at hlt
    have := one_lt_inv₀ (pos_iff_ne_zero.2 h0) |>.2 hlt
    exact absurd h2 (not_le.2 this)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem vs_comap_valuation_eq_one_iff {K : Type} [Field K] (φ : K →+* K) (V : ValuationSubring K) {x : K}
    (hx : x ≠ 0) : (V.comap φ).valuation x = 1 ↔ V.valuation (φ x) = 1 := by
  rw [vs_valuation_eq_one_iff _ hx, vs_valuation_eq_one_iff _ ((map_ne_zero φ).2 hx),
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem Tower.Un_map {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (φ : X.K →+* X.K)
    (hφ : ∀ W : ValuationSubring X.K, X.OverY W → X.OverY (W.comap φ)) (m : ℕ) {f : X.Kˣ} (hf : f ∈ X.Un m)
    (u : X.Kˣ) (hu : (u : X.K) = φ (f : X.K)) : u ∈ X.Un m := by
  intro W hW
  obtain ⟨a, ha⟩ := hf _ (hφ W hW)
  refine ⟨Units.map φ.toMonoidHom a, ?_⟩
  have hne : (f : X.K) / (a : X.K) ^ m ≠ 0 := div_ne_zero f.ne_zero (pow_ne_zero _ a.ne_zero)
  rw [vs_comap_valuation_eq_one_iff φ W hne, map_div₀, map_pow] at ha
  rw [hu]
  exact ha

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem Tower.Un_sl_gal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
    ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m →
      (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧
        ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  intro Ω _ _ _ ε X hε hj m f hf
  refine ⟨fun g u hu => ?_, fun s u hu => ?_⟩
  · exact X.Un_map (X.sl g).toRingEquiv.toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).1 g) m hf u hu
  · exact X.Un_map (X.gal s).toRingHom
      (fun W hW => (Tower.overY_comap_sl_gal ε X hε hj W hW).2 s) m hf u hu

end GlobalTheory.KZ
