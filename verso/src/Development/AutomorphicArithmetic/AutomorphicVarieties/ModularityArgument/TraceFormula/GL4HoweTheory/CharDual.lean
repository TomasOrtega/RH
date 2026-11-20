import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective

open MeasureTheory ValuativeRel GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Introduce `E _ _ _ _ ϖ _ ψ₀ ψ d e h0 h`. Take `⟨b, hb⟩` from `GlobalTheory.LocGL.exists_eq_mulShift h0.continuous h0.ne_one h.continuous`. Establish `hb0 : b ≠ 0` using `fun e0 => h.ne_one (by rw [hb, e0, AddChar.mulShift_zero])`. Establish `hv : ∀ x, ψ x = ψ₀ (b * x)` using `fun x => by rw [hb, AddChar.mulShift_apply]`. Establish `hvb : 0 < valuation E b` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0)`.

Establish `key : ∀ x : E, valuation E x ≤ valuation E ((ϖ ^ e : Eˣ) : E) ↔ valuation E (b * x) ≤ valuation E ((ϖ ^ d : Eˣ) : E)` using `fun x => by`. Rewrite using `[← h x, ← h0 (b * x)]`. Use `⟨fun H y hy => ?_, fun H y hy => ?_⟩` and prove the remaining obligations. Use `H (b⁻¹ * y) (by` as an intermediate fact. Rewrite `hy` using `[map_mul]`.

Rewrite using `[map_mul, map_inv₀, inv_mul_le_iff₀ hvb]`. Conclude with `hy)`. Rewrite `this` using `[hv, mul_inv_cancel_left₀ hb0]`. Then use the resulting hypothesis. Rewrite using `[hv]`. Conclude with `H _ (by rw [map_mul, map_mul]; exact mul_le_mul_right hy _)`.

Establish `hve : 0 < valuation E ((ϖ ^ e : Eˣ) : E)` using `zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))`. Establish `h1` using `(key _).1 le_rfl`. Establish `h2` using `(key (b⁻¹ * ((ϖ ^ d : Eˣ) : E))).2 (by rw [mul_inv_cancel_left₀ hb0])`. Rewrite `h2` using `[map_mul, map_inv₀, inv_mul_le_iff₀ hvb]`. Rewrite `h1` using `[map_mul]`.

Use `⟨Units.mk0 b hb0, ?_, hv⟩` and prove the remaining obligations. Rewrite using `[zpow_sub, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← le_antisymm h1 h2, Units.val_mk0, mul_inv_cancel_right₀ hve.ne']`.
-/
theorem UpperTheory.V.Z.Tf.L4.charDual :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (ϖ : Eˣ), valuation E (ϖ : E) = uniformizer E → ∀ (ψ₀ ψ : AddChar E Circle) (d e : ℤ), HasConductor ψ₀ (ϖ ^ d) → HasConductor ψ (ϖ ^ e) →
  ∃ β : Eˣ, valuation E (β : E) = valuation E ((ϖ ^ (d - e) : Eˣ) : E) ∧ ∀ x, ψ x = ψ₀ (β * x) := by
  intro E _ _ _ _ ϖ _ ψ₀ ψ d e h0 h
  obtain ⟨b, hb⟩ := GlobalTheory.LocGL.exists_eq_mulShift h0.continuous h0.ne_one h.continuous
  have hb0 : b ≠ 0 := fun e0 => h.ne_one (by rw [hb, e0, AddChar.mulShift_zero])
  have hv : ∀ x, ψ x = ψ₀ (b * x) := fun x => by rw [hb, AddChar.mulShift_apply]
  have hvb : 0 < valuation E b := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hb0)
  have key : ∀ x : E, valuation E x ≤ valuation E ((ϖ ^ e : Eˣ) : E) ↔ valuation E (b * x) ≤ valuation E ((ϖ ^ d : Eˣ) : E) := fun x => by
    rw [← h x, ← h0 (b * x)]
    refine ⟨fun H y hy => ?_, fun H y hy => ?_⟩
    · have := H (b⁻¹ * y) (by
        rw [map_mul] at hy
        rw [map_mul, map_inv₀, inv_mul_le_iff₀ hvb]
        exact hy)
      rwa [hv, mul_inv_cancel_left₀ hb0] at this
    · rw [hv]
      exact H _ (by rw [map_mul, map_mul]; exact mul_le_mul_right hy _)
  have hve : 0 < valuation E ((ϖ ^ e : Eˣ) : E) := zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 (Units.ne_zero _))
  have h1 := (key _).1 le_rfl
  have h2 := (key (b⁻¹ * ((ϖ ^ d : Eˣ) : E))).2 (by rw [mul_inv_cancel_left₀ hb0])
  rw [map_mul, map_inv₀, inv_mul_le_iff₀ hvb] at h2
  rw [map_mul] at h1
  refine ⟨Units.mk0 b hb0, ?_, hv⟩
  rw [zpow_sub, Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, ← le_antisymm h1 h2, Units.val_mk0,
    mul_inv_cancel_right₀ hve.ne']
