import Development.AbelianVarietyTheory.Definitions.Foundations.IsPrimitiveRootTopZeta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KmapSubMemOfASet

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 Polynomial
attribute [local instance] algMdl algPoly algRat

/- English proof (translation)
Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem integral_map_of_base_integral {R L : Type*} [CommRing R] [CommRing L] [Algebra R L] (t : L →+* L)
    (h : ∀ r : R, IsIntegral R (t (algebraMap R L r))) {x : L} (hx : IsIntegral R x) : IsIntegral R (t x) := by
  obtain ⟨p, hp, h0⟩ := hx
  let g : R →+* integralClosure R L :=
    (t.comp (algebraMap R L)).codRestrict (integralClosure R L).toSubring h
  have h1 : IsIntegral (integralClosure R L) (t x) := by
    refine ⟨p.map g, hp.map g, ?_⟩
    rw [Polynomial.eval₂_map]
    have e : (algebraMap (integralClosure R L) L).comp g = t.comp (algebraMap R L) := RingHom.ext fun _ => rfl
    rw [e, ← Polynomial.hom_eval₂, h0, map_zero]
  exact isIntegral_trans _ h1

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem isIntegral_map_algebraic {Ω R L : Type*} [Field Ω] [Algebra ℚ Ω] [CommRing R] [Field L] [Algebra R L]
    (i : ℚ →+* R) (s : Ω →+* L) {c : Ω} (hc : IsIntegral ℚ c) : IsIntegral R (s c) := by
  obtain ⟨p, hpm, hp⟩ := hc
  refine ⟨p.map i, hpm.map i, ?_⟩
  rw [eval₂_map, RingHom.ext_rat ((algebraMap R L).comp i) (s.comp (algebraMap ℚ Ω)), ← Polynomial.hom_eval₂, hp, map_zero]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Proceed by induction. Treat this case separately. Rewrite the conclusion using the stated equalities. Treat this case separately. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.algEquiv_mem_ringOfIntegers_modularTowerTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (τ : topL X M ≃ₐ[topF X M] topL X M) (x : topL X M), x ∈ FunctionField.ringOfIntegers Ω (topL X M) → τ x ∈ FunctionField.ringOfIntegers Ω (topL X M) := by
  intro Ω _ _ _ ε X M τ x hx
  set jL : topL X M := algebraMap (Polynomial Ω) (topL X M) Polynomial.X with hjL
  have hjτ : τ jL = jL := by
    have h0 := τ.commutes ⟨X.jK, jK_mem_mdl X _ _⟩
    have e : algebraMap (topF X M) (topL X M) ⟨X.jK, jK_mem_mdl X _ _⟩ = jL := by
      apply Subtype.ext
      change X.jK = ((jPoly X _ Polynomial.X : _) : X.K)
      rw [coe_jPoly, aeval_X]
    rwa [e] at h0
  refine integral_map_of_base_integral (R := Polynomial Ω) τ.toRingEquiv.toRingHom ?_ hx
  intro P
  induction P using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, map_add]
    exact hp.add hq
  | monomial n c =>
    have e : algebraMap (Polynomial Ω) (topL X M) (monomial n c) =
        algebraMap (Polynomial Ω) (topL X M) (C c) * jL ^ n := by
      rw [hjL, ← map_pow, ← map_mul, C_mul_X_pow_eq_monomial]
    rw [e, map_mul, map_pow]
    refine IsIntegral.mul ?_ (IsIntegral.pow ?_ n)
    · exact isIntegral_map_algebraic (algebraMap ℚ (Polynomial Ω))
        ((τ.toRingEquiv.toRingHom).comp ((algebraMap (Polynomial Ω) (topL X M)).comp Polynomial.C))
        (Algebra.IsIntegral.isIntegral c)
    · change IsIntegral _ (τ jL)
      rw [hjτ]
      exact isIntegral_algebraMap
