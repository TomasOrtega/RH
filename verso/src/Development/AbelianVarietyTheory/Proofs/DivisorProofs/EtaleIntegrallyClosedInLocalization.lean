import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
open IsLocalRing Polynomial
open scoped TensorProduct
open GlobalTheory.LocAcyc GlobalTheory.KeyOriginNoeth GlobalTheory.KeyOriginBC

namespace GlobalTheory.EtaleNormalLoc

/- English proof (translation)
Introduce a local definition for the expression. Equip the data with the indicated structure. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem isIntegrallyClosedIn_localization (S : Type) [CommRing S] [IsDomain S]
    [IsIntegrallyClosed S] (M : Submonoid S) (hM : M ≤ nonZeroDivisors S) :
    IsIntegrallyClosedIn S (Localization M) := by
  let K := FractionRing S
  letI : Algebra (Localization M) K :=
    IsLocalization.localizationAlgebraOfSubmonoidLe (Localization M) K M _ hM
  haveI : IsScalarTower S (Localization M) K :=
    IsLocalization.localization_isScalarTower_of_submonoid_le (Localization M) K M _ hM
  haveI : IsFractionRing (Localization M) K :=
    IsFractionRing.isFractionRing_of_isLocalization M (Localization M) K hM
  haveI : IsDomain (Localization M) := IsLocalization.isDomain_localization hM
  have hK : Function.Injective (algebraMap (Localization M) K) := IsFractionRing.injective _ _
  refine isIntegrallyClosedIn_iff.mpr ⟨fun x y hxy ↦ ?_, fun {x} hx ↦ ?_⟩
  · apply IsFractionRing.injective S K
    rw [IsScalarTower.algebraMap_apply S (Localization M) K, hxy, ← IsScalarTower.algebraMap_apply]
  · obtain ⟨y, hy⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral (hx.algebraMap (B := K))
    exact ⟨y, hK (by rw [← hy, IsScalarTower.algebraMap_apply S (Localization M) K])⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Introduce a local definition for the expression. Introduce a local definition for the expression.

Equip the data with the indicated structure. Introduce a local definition for the expression. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Treat this case separately. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem etale_integrallyClosed_localization : ∀ (S E : Type) [CommRing S] [IsDomain S] [IsIntegrallyClosed S]
    [CommRing E] [Algebra S E] [Algebra.Etale S E] (M : Submonoid S), M ≤ nonZeroDivisors S →
    Function.Injective (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))) ∧
    ∀ x : Localization (Algebra.algebraMapSubmonoid E M), IsIntegral S x →
      x ∈ (algebraMap E (Localization (Algebra.algebraMapSubmonoid E M))).range := by
  intro S E _ _ _ _ _ _ M hM
  have hle : Algebra.algebraMapSubmonoid E M ≤ nonZeroDivisors E := by
    rintro _ ⟨m, hm, rfl⟩
    have hreg : IsSMulRegular E m := Module.Flat.isSMulRegular_of_nonZeroDivisors (hM hm)
    refine mem_nonZeroDivisors_iff.mpr ⟨fun x hx ↦ hreg ?_, fun x hx ↦ hreg ?_⟩
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def]
      exact hx
    · show m • x = m • (0 : E)
      rw [smul_zero, Algebra.smul_def, mul_comm]
      exact hx
  refine ⟨IsLocalization.injective _ hle, fun x hx ↦ ?_⟩
  let SM := Localization M
  let T := E ⊗[S] SM
  letI : Algebra SM T := Algebra.TensorProduct.rightAlgebra
  haveI : IsScalarTower S SM T := inferInstance
  haveI : Algebra.IsPushout S E SM T := inferInstance
  haveI : IsLocalization (Algebra.algebraMapSubmonoid E M) T :=
    (Algebra.isLocalization_iff_isPushout M SM).2 (Algebra.IsPushout.symm inferInstance)
  let e : T ≃ₐ[E] Localization (Algebra.algebraMapSubmonoid E M) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid E M) T _
  have hic := isIntegrallyClosedIn_localization S M hM
  have htS : IsIntegral S (e.symm x) := hx.map (e.symm.toAlgHom.restrictScalars S)
  have htE : IsIntegral E (e.symm x) := htS.tower_top
  obtain ⟨y, hy⟩ := (TensorProduct.toIntegralClosure_bijective_of_smooth
    (R := S) (S := E) (B := SM)).2 ⟨e.symm x, htE⟩
  have hy' : (TensorProduct.toIntegralClosure S E SM y : T) = e.symm x := congrArg Subtype.val hy
  have key : ∀ y : E ⊗[S] integralClosure S SM, ∃ b : E,
      (TensorProduct.toIntegralClosure S E SM y : T) = b ⊗ₜ[S] (1 : SM) := by
    intro y
    induction y with
    | zero => exact ⟨0, by simp⟩
    | tmul b c =>
      obtain ⟨r, hr⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 c.2
      refine ⟨r • b, ?_⟩
      rw [TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, hr]
      rfl
    | add u v hu hv =>
      obtain ⟨a, ha⟩ := hu
      obtain ⟨b, hb⟩ := hv
      exact ⟨a + b, by rw [map_add, Subalgebra.coe_add, ha, hb, TensorProduct.add_tmul]⟩
  obtain ⟨b, hb⟩ := key y
  refine ⟨b, ?_⟩
  have : e.symm x = algebraMap E T b := by
    rw [← hy', hb]; rfl
  rw [← e.apply_symm_apply x, this, AlgEquiv.commutes]

end GlobalTheory.EtaleNormalLoc
