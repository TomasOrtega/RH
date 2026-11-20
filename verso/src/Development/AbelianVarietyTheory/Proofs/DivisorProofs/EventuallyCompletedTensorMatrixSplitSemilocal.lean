import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralTensorPointsSharpStableRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupActionRingHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralMatrixUnitsAtPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixUnitsGiveMatrixAlgebraIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyEqOfMonicAevalPowersLinearIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralLocalCenterFiniteMaximalIdealsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowersLinearIndependentOverLocalTensorCenterStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalTensorCenterInclusionInjectiveCentralFinranStatement

open Matrix NumberField IsDedekindDomain GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.OrbFinAf
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.OrbFinAf

/- English proof (translation)
Establish `h` using `Filter.eventually_all.2 fun i : Fin (f.natDegree + 1) => GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually p G (algebraMap G.F G.C (f.coeff i))`. Use `filter_upwards [h] with v hv i`. Distinguish the cases in `hi : i ≤ f.natDegree`. Conclude with `hv ⟨i, Nat.lt_succ_of_le hi⟩`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, TensorProduct.tmul_zero]`.

Conclude with `isIntV_zero G v`.
-/
theorem coeff_isIntV_eventually (p : ℕ) [Fact p.Prime] (G : HTGroup p) (f : Polynomial G.F) :
    ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)),
      ∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i)) := by
  have h := Filter.eventually_all.2 fun i : Fin (f.natDegree + 1) =>
    GlobalTheory.OrbFinAfFixed.isIntV_one_tmul_eventually p G (algebraMap G.F G.C (f.coeff i))
  filter_upwards [h] with v hv i
  by_cases hi : i ≤ f.natDegree
  · exact hv ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, TensorProduct.tmul_zero]
    exact isIntV_zero G v

/- English proof (translation)
Introduce `p _ G γ hdeg hsep`. Take `⟨a, b, hab⟩` from `hsep`. Use `filter_upwards [intV_order_eventually p G, GlobalTheory.T.eventually_integral_matrix_units_at_places p G, coeff_isIntV_eventually p G (minpoly G.F γ), coeff_isIntV_eventually p G a, coeff_isIntV_eventually p G b] with v hO hEE hP ha hb`. Take `⟨h1, hm, -⟩` from `hO`. Take `⟨E, hE, hE1, hEi⟩` from `hEE`.

Take `⟨hinj, hcen, hdim⟩` from `GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank p G v`. Take `⟨Φ, hΦ, hΦs⟩` from `GlobalTheory.T.matrix_units_give_matrix_algebra_iso (Qv v) (Qv v ⊗[ℚ] G.F) (Qv v ⊗[ℚ] G.C) G.n (iotaF G v) hinj hcen hdim E hE hE1`. Set `φ0 : G.F →+* Qv v ⊗[ℚ] G.F` to `(Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] Qv v ⊗[ℚ] G.F).toRingHom`. Establish `hφ : ∀ x, iotaF G v (φ0 x) = (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C x` using `fun x => rfl`. Establish `hsub : ∀ f : Polynomial G.F, (∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i))) → (↑(f.map φ0).coeffs : Set (Qv v ⊗[ℚ] G.F)) ⊆ (intF G v h1 hm : Set (Qv v ⊗[ℚ] G.F))`.

Introduce `f hf c hc`. Take `⟨i, -, rfl⟩` from `Polynomial.mem_coeffs_iff.1 hc`. Rewrite using `[Polynomial.coeff_map]`. Use `show IsIntV G v (iotaF G v (φ0 (f.coeff i)))`. Rewrite using `[hφ]`.

Conclude with `hf i`. Establish `hsc : ∀ z : Qv v ⊗[ℚ] G.F, Φ (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)) z) = iotaF G v z`. Introduce `z`. Rewrite using `[hΦ, ← mul_one (iotaF G v z), ← hE1, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[Matrix.algebraMap_matrix_apply]`. Introduce `j _ hj`. Simplify using `[Matrix.algebraMap_matrix_apply, Ne.symm hj]`. Simplify using the standard rewrite rules.

Use `⟨Qv v ⊗[ℚ] G.F, inferInstance, intF G v h1 hm, Φ, GlobalTheory.T.integralLocalCenter_finite_maximal_ideals p G v h1 hm, fun x => ⟨fun hx i j => ?_, fun hx => ?_⟩, ?_⟩` and prove the remaining obligations. Use `show IsIntV G v (iotaF G v (Φ.symm x i j))`. Rewrite using `[hΦs]`. Conclude with `isIntV_sum G v _ _ fun c _ => hm _ _ (hm _ _ (hEi c i) hx) (hEi j c)`. Rewrite using `[← Φ.apply_symm_apply x, hΦ]`.

Conclude with `isIntV_sum G v _ _ fun i _ => isIntV_sum G v _ _ fun j _ => hm _ _ (hx i j) (hEi i j)`. Use `⟨((minpoly G.F γ).map φ0).toSubring _ (hsub _ hP), ?_, ?_⟩` and prove the remaining obligations. Use `⟨(a.map φ0).toSubring _ (hsub _ ha), (b.map φ0).toSubring _ (hsub _ hb), ?_⟩` and prove the remaining obligations. Apply `Polynomial.map_injective (intF G v h1 hm).subtype Subtype.val_injective` to reduce the goal to its premises. Rewrite using `[Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one, ← Polynomial.derivative_map, Polynomial.map_toSubring, Polynomial.map_toSubring, Polynomial.map_toSubring, Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, …`.

Rewrite using `[Polynomial.map_toSubring]`. Establish `hmon : (minpoly G.F γ).Monic` using `minpoly.monic (Algebra.IsIntegral.isIntegral γ)`. Establish `hX : Φ (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)) = (1 : Qv v) ⊗ₜ[ℚ] γ` using `Φ.apply_symm_apply _`. Use `symm`. Apply `GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent` to reduce the goal to its premises.

Conclude with `hmon.map φ0`. Rewrite using `[hmon.natDegree_map, hdeg]`. Apply `Φ.injective` to reduce the goal to its premises. Rewrite using `[map_zero, Polynomial.aeval_def]`. Establish `h3` using `Polynomial.hom_eval₂ ((minpoly G.F γ).map φ0) (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F))) (Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C) (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ))`.

Rewrite `h3` using `[RingEquiv.coe_toRingHom]`. Rewrite using `[h3, hX, Polynomial.eval₂_map]`. Establish `e : ((Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C).comp (algebraMap (Qv v ⊗[ℚ] G.F) _)).comp φ0 = (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom.comp (algebraMap G.F G.C)`. Use extensionality with `x`. Simplify using `only [RingHom.comp_apply, RingEquiv.coe_toRingHom]`.

Rewrite using `[hsc, hφ]`. Both sides reduce to the same expression. Rewrite using `[e]`. Establish `h4` using `Polynomial.hom_eval₂ (minpoly G.F γ) (algebraMap G.F G.C) (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom γ`. Establish `e2 : Polynomial.eval₂ (algebraMap G.F G.C) γ (minpoly G.F γ) = 0` using `minpoly.aeval G.F γ`.

Rewrite `h4` using `[e2, map_zero]`. Conclude with `h4.symm`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Use `GlobalTheory.T.powers_linearIndependent_over_localTensorCenter p G γ hdeg v g (by` as an intermediate fact.

Establish `h2` using `congrArg Φ hg`. Rewrite `h2` using `[map_sum, map_zero]`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, map_mul, map_pow, hsc, hX, Algebra.TensorProduct.tmul_pow, one_pow])`.

Introduce `i`. Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem split_eventually : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (γ : G.C), (minpoly G.F γ).natDegree = G.n → (minpoly G.F γ).Separable → ∀ᶠ v in (Filter.cofinite : Filter (AwayP p)), ∃ (K : Type) (_ : CommRing K) (R : Subring K) (Φ : Matrix (Fin G.n) (Fin G.n) K ≃+* Qv v ⊗[ℚ] G.C), Set.Finite {I : Ideal R | I.IsMaximal} ∧ (∀ a : Qv v ⊗[ℚ] G.C, IsIntV G v a ↔ ∀ i j, Φ.symm a i j ∈ R) ∧ ∃ Q : Polynomial R, Q.Separable ∧ Q.map R.subtype = (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)).charpoly := by
  intro p _ G γ hdeg hsep
  obtain ⟨a, b, hab⟩ := hsep
  filter_upwards [intV_order_eventually p G, GlobalTheory.T.eventually_integral_matrix_units_at_places p G, coeff_isIntV_eventually p G (minpoly G.F γ),
    coeff_isIntV_eventually p G a, coeff_isIntV_eventually p G b] with v hO hEE hP ha hb
  obtain ⟨h1, hm, -⟩ := hO
  obtain ⟨E, hE, hE1, hEi⟩ := hEE
  obtain ⟨hinj, hcen, hdim⟩ := GlobalTheory.T.localTensorCenterInclusion_injective_central_finrank p G v
  obtain ⟨Φ, hΦ, hΦs⟩ := GlobalTheory.T.matrix_units_give_matrix_algebra_iso (Qv v) (Qv v ⊗[ℚ] G.F) (Qv v ⊗[ℚ] G.C) G.n (iotaF G v) hinj hcen hdim E hE hE1
  let φ0 : G.F →+* Qv v ⊗[ℚ] G.F :=
    (Algebra.TensorProduct.includeRight : G.F →ₐ[ℚ] Qv v ⊗[ℚ] G.F).toRingHom
  have hφ : ∀ x, iotaF G v (φ0 x) = (1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C x := fun x => rfl
  have hsub : ∀ f : Polynomial G.F, (∀ i, IsIntV G v ((1 : Qv v) ⊗ₜ[ℚ] algebraMap G.F G.C (f.coeff i))) →
      (↑(f.map φ0).coeffs : Set (Qv v ⊗[ℚ] G.F)) ⊆ (intF G v h1 hm : Set (Qv v ⊗[ℚ] G.F)) := by
    intro f hf c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    rw [Polynomial.coeff_map]
    show IsIntV G v (iotaF G v (φ0 (f.coeff i)))
    rw [hφ]; exact hf i
  have hsc : ∀ z : Qv v ⊗[ℚ] G.F,
      Φ (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)) z) = iotaF G v z := by
    intro z
    rw [hΦ, ← mul_one (iotaF G v z), ← hE1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.algebraMap_matrix_apply]
    · intro j _ hj; simp [Matrix.algebraMap_matrix_apply, Ne.symm hj]
    · simp
  refine ⟨Qv v ⊗[ℚ] G.F, inferInstance, intF G v h1 hm, Φ, GlobalTheory.T.integralLocalCenter_finite_maximal_ideals p G v h1 hm,
    fun x => ⟨fun hx i j => ?_, fun hx => ?_⟩, ?_⟩
  · show IsIntV G v (iotaF G v (Φ.symm x i j))
    rw [hΦs]
    exact isIntV_sum G v _ _ fun c _ => hm _ _ (hm _ _ (hEi c i) hx) (hEi j c)
  · rw [← Φ.apply_symm_apply x, hΦ]
    exact isIntV_sum G v _ _ fun i _ => isIntV_sum G v _ _ fun j _ => hm _ _ (hx i j) (hEi i j)
  · refine ⟨((minpoly G.F γ).map φ0).toSubring _ (hsub _ hP), ?_, ?_⟩
    · refine ⟨(a.map φ0).toSubring _ (hsub _ ha), (b.map φ0).toSubring _ (hsub _ hb), ?_⟩
      apply Polynomial.map_injective (intF G v h1 hm).subtype Subtype.val_injective
      rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_one,
        ← Polynomial.derivative_map, Polynomial.map_toSubring, Polynomial.map_toSubring, Polynomial.map_toSubring,
        Polynomial.derivative_map, ← Polynomial.map_mul, ← Polynomial.map_mul, ← Polynomial.map_add, hab,
        Polynomial.map_one]
    · rw [Polynomial.map_toSubring]
      have hmon : (minpoly G.F γ).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral γ)
      have hX : Φ (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ)) = (1 : Qv v) ⊗ₜ[ℚ] γ := Φ.apply_symm_apply _
      symm
      apply GlobalTheory.T.charpoly_eq_of_monic_aeval_powers_linearIndependent
      · exact hmon.map φ0
      · rw [hmon.natDegree_map, hdeg]
      · apply Φ.injective
        rw [map_zero, Polynomial.aeval_def]
        have h3 := Polynomial.hom_eval₂ ((minpoly G.F γ).map φ0)
          (algebraMap (Qv v ⊗[ℚ] G.F) (Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F)))
          (Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C) (Φ.symm ((1 : Qv v) ⊗ₜ[ℚ] γ))
        rw [RingEquiv.coe_toRingHom] at h3
        rw [h3, hX, Polynomial.eval₂_map]
        have e : ((Φ : Matrix (Fin G.n) (Fin G.n) (Qv v ⊗[ℚ] G.F) →+* Qv v ⊗[ℚ] G.C).comp
            (algebraMap (Qv v ⊗[ℚ] G.F) _)).comp φ0 =
            (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom.comp (algebraMap G.F G.C) := by
          ext x
          simp only [RingHom.comp_apply, RingEquiv.coe_toRingHom]
          rw [hsc, hφ]; rfl
        rw [e]
        have h4 := Polynomial.hom_eval₂ (minpoly G.F γ) (algebraMap G.F G.C)
          (Algebra.TensorProduct.includeRight : G.C →ₐ[ℚ] Qv v ⊗[ℚ] G.C).toRingHom γ
        have e2 : Polynomial.eval₂ (algebraMap G.F G.C) γ (minpoly G.F γ) = 0 := minpoly.aeval G.F γ
        rw [e2, map_zero] at h4
        exact h4.symm
      · rw [Fintype.linearIndependent_iff]
        intro g hg
        have := GlobalTheory.T.powers_linearIndependent_over_localTensorCenter p G γ hdeg v g (by
          have h2 := congrArg Φ hg
          rw [map_sum, map_zero] at h2
          rw [← h2]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.smul_def, map_mul, map_pow, hsc, hX, Algebra.TensorProduct.tmul_pow, one_pow])
        intro i; rw [this]; rfl

end GlobalTheory.OrbFinAf
