import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.IsChart
import Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsFunctionFieldAndChartCoverOfIsCurve
import Development.AutomorphicArithmetic.CommutativeAlgebra.BaseChangeCurveFunctionFieldCompOfNormal

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC GroundTheory.FunctionField UpperTheory.Et.Sel LateralTheory.E.E4
open scoped TensorProduct

/- English proof (translation)
Conclude with `Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective`.
-/
private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective {k K L : Type} [Field k] [Field K] [Algebra k K] [Field L] [Algebra k L]
    (B : Subalgebra k K) : Function.Injective (inc L B) := by
  exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := L) B.val.toLinearMap Subtype.val_injective

/- English proof (translation)
Establish `hDq : D ^ q ≠ 0` using `pow_ne_zero _ hD`. Rewrite using `[mul_pow, inv_pow]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`.
-/
private lemma UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve {E : Type*} [Field E] {f S T A D : E} {q : ℕ} (hS : S ≠ 0) (hD : D ≠ 0)
    (h : f * (S * D ^ q) = T * A ^ q) : f = T * S⁻¹ * (A * D⁻¹) ^ q := by
  have hDq : D ^ q ≠ 0 := pow_ne_zero _ hD
  rw [mul_pow, inv_pow]
  field_simp
  linear_combination h

/- English proof (translation)
Introduce `hH q _ k _ _ hq C _ c hc _ hgen`. Take `⟨hff, n, B, hB, hX⟩` from `UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen`. Use `⟨hff, n, B, hB, ?_⟩` and prove the remaining obligations. Introduce `L _ _ _ F hF hloc`. Take `⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩` from `hX L`.

Establish `hθF : θ F ≠ 0` using `(map_ne_zero_iff θ hθ).mpr hF`. Establish `key` using `UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by`. Introduce `y`. Take `⟨i, m, hm, hw⟩` from `hloc' y`. Take `⟨M, hM, hmM⟩` from `Ideal.exists_le_maximal m hm.ne_top`.

Take `⟨s, t, a, b, hs, ht, ha, hb, he⟩` from `hloc i M hM`. Take `⟨ws, hws⟩` from `hw s (fun h => hs (hmM h))`. Take `⟨wt, hwt⟩` from `hw t (fun h => ht (hmM h))`. Establish `hinc` using `UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)`. Establish `hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0` using `fun z hz => (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)`.

Establish `hs0 : s ≠ 0` using `fun h => hs (h ▸ M.zero_mem)`. Establish `hA` using `hne a ha`. Establish `hD` using `hne b hb`. Establish `hS` using `hne s hs0`. Use `⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩` and prove the remaining obligations.

Establish `h1` using `congrArg θ he`. Simplify using `only [map_mul, map_pow] at h1`. Rewrite using `[Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]`. Conclude with `UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)`. Take `⟨f, h, hfh⟩` from `key`.

Rewrite `hfh` using `[Units.val_mk0]`. Take `⟨a, b, hb, hab⟩` from `hfrac ↑h`. Establish `hθb : θ b ≠ 0` using `(map_ne_zero_iff θ hθ).mpr hb`. Use `⟨f, a, b, ?_, hb, ?_⟩` and prove the remaining obligations. Introduce `ha`.

Rewrite `hab` using `[ha, map_zero]`. Conclude with `mul_ne_zero h.ne_zero hθb hab`. Apply `hθ` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, map_pow, map_pow, ← hab, hfh]`. Simplify using `only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, Algebra.TensorProduct.includeRight_apply]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit :
    Hyps → ∀ (q : ℕ) [NeZero q], ∀ (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) → ∀ {C : Scheme.{0}} [IsIntegral C] (c : C ⟶ Sp k), IsCurve c → ∀ [Algebra k C.functionField], Spec.map (CommRingCat.ofHom (algebraMap k C.functionField)) = (C.fromSpecStalk (genericPoint C)) ≫ c → IsFunctionField k C.functionField ∧ Charts k C.functionField q := by
  intro hH q _ k _ _ hq C _ c hc _ hgen
  obtain ⟨hff, n, B, hB, hX⟩ := UpperTheory.isFunctionField_and_chart_cover_of_isCurve k c hc hgen
  refine ⟨hff, n, B, hB, ?_⟩
  intro L _ _ _ F hF hloc
  obtain ⟨X, hXi, u, x, θ, hpb, hic, hcomm, hθ, hfrac, hloc'⟩ := hX L
  have hθF : θ F ≠ 0 := (map_ne_zero_iff θ hθ).mpr hF
  have key := UpperTheory.baseChange_curve_functionField_comp_of_normal hH q k L hq c hc u x hpb hic
    (θ.comp Algebra.TensorProduct.includeRight.toRingHom) hcomm (Units.mk0 (θ F) hθF) (by
      intro y
      obtain ⟨i, m, hm, hw⟩ := hloc' y
      obtain ⟨M, hM, hmM⟩ := Ideal.exists_le_maximal m hm.ne_top
      obtain ⟨s, t, a, b, hs, ht, ha, hb, he⟩ := hloc i M hM
      obtain ⟨ws, hws⟩ := hw s (fun h => hs (hmM h))
      obtain ⟨wt, hwt⟩ := hw t (fun h => ht (hmM h))
      have hinc := UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.inc_injective (L := L) (B i)
      have hne : ∀ z : L ⊗[k] ↥(B i), z ≠ 0 → θ (inc L (B i) z) ≠ 0 := fun z hz =>
        (map_ne_zero_iff θ hθ).mpr ((map_ne_zero_iff _ hinc).mpr hz)
      have hs0 : s ≠ 0 := fun h => hs (h ▸ M.zero_mem)
      have hA := hne a ha
      have hD := hne b hb
      have hS := hne s hs0
      refine ⟨wt * ws⁻¹, Units.mk0 (θ (inc L (B i) a) * (θ (inc L (B i) b))⁻¹) (mul_ne_zero hA (inv_ne_zero hD)), ?_⟩
      have h1 := congrArg θ he
      simp only [map_mul, map_pow] at h1
      rw [Units.val_mk0, Units.val_mk0, Units.val_mul, map_mul, map_units_inv, hws, hwt]
      exact UpperTheory.isFunctionField_and_charts_of_isCurve_of_isUnit.solve hS hD h1)
  obtain ⟨f, h, hfh⟩ := key
  rw [Units.val_mk0] at hfh
  obtain ⟨a, b, hb, hab⟩ := hfrac ↑h
  have hθb : θ b ≠ 0 := (map_ne_zero_iff θ hθ).mpr hb
  refine ⟨f, a, b, ?_, hb, ?_⟩
  · intro ha
    rw [ha, map_zero] at hab
    exact mul_ne_zero h.ne_zero hθb hab
  · apply hθ
    rw [map_mul, map_mul, map_pow, map_pow, ← hab, hfh]
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      Algebra.TensorProduct.includeRight_apply]
    ring
