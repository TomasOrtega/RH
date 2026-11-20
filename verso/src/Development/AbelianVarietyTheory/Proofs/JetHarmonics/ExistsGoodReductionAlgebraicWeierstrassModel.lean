import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsFieldCmCurvesUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsVariableChangeEqLatticeCurve

open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology UpperHalfPlane

namespace GlobalTheory.MomOne

/- English proof (translation)
Set `S : Subring ℂ_[q]` to `(NormedField.valuation (K := ℂ_[q])).integer`. Establish `hS` using `Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))`. Establish `h1 : IsIntegral S x` using `hx.tower_top`. Establish `h2` using `hS.mem_of_integral h1`. Establish `h3 : ‖x‖₊ ≤ 1` using `h2`.

Conclude with `h3` after adjusting the coercions.
-/
theorem model_norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  let S : Subring ℂ_[q] := (NormedField.valuation (K := ℂ_[q])).integer
  have hS := Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))
  have h1 : IsIntegral S x := hx.tower_top
  have h2 := hS.mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

/- English proof (translation)
Establish `hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d`. Express the relevant statement in the definitionally equal form `(1 + √d * Complex.I) / 2 = _`. Rewrite using `[wK]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]`.

Conclude with `GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd`. Introduce `x`. Rewrite using `[hL x, hw]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, v, rfl⟩`.

Conclude with `⟨v, u, by ring⟩`. Introduce and unpack `⟨m, n, rfl⟩`. Conclude with `⟨n, m, by ring⟩`.
-/
theorem model_isIntegral_j {d : ℕ} (hd : d ≠ 0) {L : PeriodPair} (hL : IsOK d L) :
    IsIntegral ℤ (GlobalTheory.latticeCurve L).j := by
  have hw : ((GlobalTheory.halfOneAddSqrtNeg d hd : ℍ) : ℂ) = wK d := by
    change (1 + √d * Complex.I) / 2 = _
    rw [wK]; ring
  rw [GlobalTheory.latticeCurve_j (a := 1) (τ := GlobalTheory.halfOneAddSqrtNeg d hd) one_ne_zero]
  · exact GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg d hd
  · intro x
    rw [hL x, hw]
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨v, u, by ring⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨n, m, by ring⟩

/- English proof (translation)
Introduce `d q _ ι L hd _ hL`. Take `⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩` from `GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)`. Establish `hE : E.IsElliptic` using `⟨hΔ ▸ isUnit_one⟩`. Establish `hj : (GlobalTheory.latticeCurve L).j = E.j`. Rewrite using `[← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]`.

Simplify using the standard rewrite rules. Take `⟨C, hC⟩` from `WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj`. Establish `hu : (C.u : ℂ) ≠ 0` using `C.u.ne_zero`. Establish `e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4`. Rewrite using `[← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]`.

Clear the denominators using the available nonvanishing facts. Establish `e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6`. Establish `: (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃`. Simplify using `only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]`. Clear the denominators using the available nonvanishing facts. Establish `hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x)` using `fun hx ↦ hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)`. Establish `ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x)` using `fun hx ↦ (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic`. Use `⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl, ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂), model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄), model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, h …` and prove the remaining obligations.

Simplify using `[WeierstrassCurve.map_Δ, hΔ]`. Express the relevant statement in the definitionally equal form `(E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)`. Rewrite using `[← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `(E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)`.

Rewrite using `[← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]`. Both sides reduce to the same expression.
-/
theorem exists_model : ∀ (d q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (L : PeriodPair), d.Prime → d % 16 = 7 → IsOK d L → ∃ M : Mdl q, M.ι = ι ∧ M.L = L ∧ M.Ok ∧ IsAlgebraic ℚ M.W.a₁ ∧ IsAlgebraic ℚ M.W.a₂ ∧ IsAlgebraic ℚ M.W.a₃ ∧ IsAlgebraic ℚ M.W.a₄ ∧ IsAlgebraic ℚ M.W.a₆ := by
  intro d q _ ι L hd _ hL
  obtain ⟨E, h₁, h₂, h₃, h₄, h₆, hΔ, hc⟩ :=
    GlobalTheory.CMCurves.exists_integral_curve (model_isIntegral_j hd.ne_zero hL)
  have hE : E.IsElliptic := ⟨hΔ ▸ isUnit_one⟩
  have hj : (GlobalTheory.latticeCurve L).j = E.j := by
    rw [← hc, WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', hΔ]
    simp
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq _ _ hj
  have hu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have e4 : E.c₄ / 12 = L.g₂ / (C.u : ℂ) ^ 4 := by
    rw [← hC, WeierstrassCurve.variableChange_c₄, GlobalTheory.latticeCurve_c₄, Units.val_inv_eq_inv_val]
    field_simp
  have e6 : E.c₆ / 216 = L.g₃ / (C.u : ℂ) ^ 6 := by
    have : (GlobalTheory.latticeCurve L).c₆ = 216 * L.g₃ := by
      simp only [GlobalTheory.latticeCurve, WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
        WeierstrassCurve.b₆]
      ring
    rw [← hC, WeierstrassCurve.variableChange_c₆, this, Units.val_inv_eq_inv_val]
    field_simp
  have hi : ∀ {x : ℂ}, IsIntegral ℤ x → IsIntegral ℤ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    hx.map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[q]) (RingHom.ext_int _ _)
  have ha : ∀ {x : ℂ}, IsIntegral ℤ x → IsAlgebraic ℚ ((ι : ℂ →+* ℂ_[q]) x) := fun hx ↦
    (IsIntegral.tower_top (A := ℚ) (hi hx)).isAlgebraic
  refine ⟨⟨ι, L, C.u, E.map (ι : ℂ →+* ℂ_[q])⟩, rfl, rfl,
    ⟨hu, model_norm_le_one_of_isIntegral (hi h₁), model_norm_le_one_of_isIntegral (hi h₂),
      model_norm_le_one_of_isIntegral (hi h₃), model_norm_le_one_of_isIntegral (hi h₄),
      model_norm_le_one_of_isIntegral (hi h₆), ?_, ?_, ?_⟩, ha h₁, ha h₂, ha h₃, ha h₄, ha h₆⟩
  · simp [WeierstrassCurve.map_Δ, hΔ]
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₄ / 12 = ι (L.g₂ / (C.u : ℂ) ^ 4)
    rw [← e4, WeierstrassCurve.map_c₄, map_div₀, map_ofNat]
    rfl
  · change (E.map (ι : ℂ →+* ℂ_[q])).c₆ / 216 = ι (L.g₃ / (C.u : ℂ) ^ 6)
    rw [← e6, WeierstrassCurve.map_c₆, map_div₀, map_ofNat]
    rfl

end GlobalTheory.MomOne
