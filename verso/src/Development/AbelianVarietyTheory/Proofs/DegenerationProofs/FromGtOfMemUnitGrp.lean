import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsFrameIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionIdentificationWithPairingStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTorsionMapsCompatibleInLevelStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantValuationsUnitsEveryCosetStatement

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.LN GlobalTheory.Ex GlobalTheory.OneBasis

noncomputable section
namespace GlobalTheory.OneBasis.UnitGrp
open GlobalTheory.TorusExt
attribute [local instance] gtGroup

/- English proof (translation)
Introduce `hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu x hx`. Establish `hA : AdmBase V (maximalIdeal V)` using `⟨inferInstance, inferInstance, inferInstance, hc⟩`. Establish `hB` using `D.tau_bimult`. Take `⟨f, f₁, -, f₃, f₄, -⟩` from `GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F k hk.pos`. Take `⟨f', f₁', f₂', -⟩` from `GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F (k ^ 2) (pow_pos hk.pos 2)`.

Establish `ua` using `(GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP k hk hu).1`. Establish `add : ∀ p p', f (qkAdd hB p p') = f p * f p'` using `fun p p' => f₄ _ _ _ (qkAdd_qkAdd hB p p')`. Establish `f0 : f (qkZero hB F k) = 1`. Establish `e` using `add (qkZero hB F k) (qkZero hB F k)`. Rewrite `e` using `[show qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k from qk_ext (add_zero _) (add_zero _)]`.

Conclude with `mul_eq_left.1 e.symm`. Proceed by induction on `hx using Subgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨x, t, c, hx, hT, hc0, rfl⟩` from `hy`. Take `⟨q, rfl⟩` from `f₂' x hx`.

Establish `hq` using `(f₁' q _).2 rfl`. Take `⟨z, hz⟩` from `(ua q _ t c hq hT).2 hc0`. Set `p : QkPt D.toPre F k` to `qkMk hB q.y (k • q.g) (by rw [← mul_smul, ← pow_two, qk_nsmul hB])`. Establish `hp` using `(GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F k k (k ^ 2) hk.pos hk.pos (pow_two k) p q (f' q)).2 rfl ((isNsmul_iff_eq _ _ _).2 rfl) hq`. Use `⟨qkShift hB p (-z), ?_, (f₁ _ _).2 (((f₁ _ _).1 hp).trans ((f₃ _ _).2 (equiv_qkShift hB p (-z))))⟩` and prove the remaining obligations.

Use `show q.y + k • (-z) = 0`. Rewrite using `[hz, smul_neg, add_neg_cancel]`. Consider the case `one => exact ⟨qkZero hB F k, rfl, (f₁ _ _).2 f0.symm⟩`. Consider the case `mul a b _ _ ha hb`. Take `⟨p, py, hp⟩` from `ha`.

Take `⟨p', py', hp'⟩` from `hb`. Use `⟨qkAdd hB p p', ?_, (f₁ _ _).2 ?_⟩` and prove the remaining obligations. Use `show p.y + p'.y = 0`. Rewrite using `[py, py', add_zero]`. Rewrite using `[add, (f₁ _ _).1 hp, (f₁ _ _).1 hp']`.

Consider the case `inv a _ ha`. Take `⟨p, py, hp⟩` from `ha`. Use `⟨qkNeg hB p, ?_, (f₁ _ _).2 ?_⟩` and prove the remaining obligations. Use `show -p.y = 0`. Rewrite using `[py, neg_zero]`.

Establish `e` using `add (qkNeg hB p) p`. Rewrite `e` using `[show qkAdd hB (qkNeg hB p) p = qkZero hB F k from qk_ext (neg_add_cancel _) (neg_add_cancel _), f0]`. Rewrite using `[(f₁ _ _).1 hp]`. Conclude with `(eq_inv_of_mul_eq_one_left e.symm).symm`.
-/
theorem fromGt_of_mem_unitGrp : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ w₀ ρ, NormW U.toUnifPre w₀ ρ → ∀ (th : SecA A F 1) (ϑ : Fam D.toPre F 1), U.ExpandsF F 1 w₀ th ϑ → Prim D Q v ϑ → ∀ k : ℕ, Odd k → IsUnit (k : V) → ∀ x ∈ unitGrp v ρ th k, FromGt U.toUnifPre k x := by
  intro hL h₁ h₂ h₃ h₄ V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U w₀ ρ hN th ϑ hE hP k hk hu x hx
  have hA : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  have hB := D.tau_bimult
  obtain ⟨f, f₁, -, f₃, f₄, -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F k hk.pos
  obtain ⟨f', f₁', f₂', -⟩ := GlobalTheory.T.uniformisation_torsion_identification_with_pairing hL V _ hA D A G hG U F (k ^ 2) (pow_pos hk.pos 2)
  have ua := (GlobalTheory.T.theta_constant_valuations_units_every_coset hL h₁ h₂ h₃ h₄ V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ hE hP k hk hu).1
  have add : ∀ p p', f (qkAdd hB p p') = f p * f p' := fun p p' => f₄ _ _ _ (qkAdd_qkAdd hB p p')
  have f0 : f (qkZero hB F k) = 1 := by
    have e := add (qkZero hB F k) (qkZero hB F k)
    rw [show qkAdd hB (qkZero hB F k) (qkZero hB F k) = qkZero hB F k from qk_ext (add_zero _) (add_zero _)] at e
    exact mul_eq_left.1 e.symm
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨x, t, c, hx, hT, hc0, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := f₂' x hx
    have hq := (f₁' q _).2 rfl
    obtain ⟨z, hz⟩ := (ua q _ t c hq hT).2 hc0
    let p : QkPt D.toPre F k := qkMk hB q.y (k • q.g) (by rw [← mul_smul, ← pow_two, qk_nsmul hB])
    have hp := (GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hL V _ hA D A G hG U F k k (k ^ 2) hk.pos hk.pos (pow_two k) p q (f' q)).2 rfl
      ((isNsmul_iff_eq _ _ _).2 rfl) hq
    refine ⟨qkShift hB p (-z), ?_, (f₁ _ _).2 (((f₁ _ _).1 hp).trans ((f₃ _ _).2 (equiv_qkShift hB p (-z))))⟩
    show q.y + k • (-z) = 0
    rw [hz, smul_neg, add_neg_cancel]
  | one => exact ⟨qkZero hB F k, rfl, (f₁ _ _).2 f0.symm⟩
  | mul a b _ _ ha hb =>
    obtain ⟨p, py, hp⟩ := ha
    obtain ⟨p', py', hp'⟩ := hb
    refine ⟨qkAdd hB p p', ?_, (f₁ _ _).2 ?_⟩
    · show p.y + p'.y = 0
      rw [py, py', add_zero]
    · rw [add, (f₁ _ _).1 hp, (f₁ _ _).1 hp']
  | inv a _ ha =>
    obtain ⟨p, py, hp⟩ := ha
    refine ⟨qkNeg hB p, ?_, (f₁ _ _).2 ?_⟩
    · show -p.y = 0
      rw [py, neg_zero]
    · have e := add (qkNeg hB p) p
      rw [show qkAdd hB (qkNeg hB p) p = qkZero hB F k from qk_ext (neg_add_cancel _) (neg_add_cancel _), f0] at e
      rw [(f₁ _ _).1 hp]
      exact (eq_inv_of_mul_eq_one_left e.symm).symm

end GlobalTheory.OneBasis.UnitGrp
end
