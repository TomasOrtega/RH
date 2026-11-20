import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootXPowSubUniformizerIsDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjoinRootUniformiserIsDVRStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisationDvrTensorSeparableFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarRamificationIdxEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarResidueFieldIsSeparableStatement
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

/- English proof (translation)
Rewrite `h` using `[Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one, Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]`. Set `Rp` to `Localization.AtPrime p`. Set `Sq` to `Localization.AtPrime q`. Set `` to `Localization.AtPrime.algebraOfLiesOver p q`. Use `Algebra.EssFiniteType.of_comp R Rp Sq` as an intermediate fact.

It suffices to establish `Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq`. Rewrite using `[Algebra.FormallyUnramified.iff_map_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]`. Establish `: Algebra.IsSeparable p.ResidueField q.ResidueField` using `inferInstance`. Conclude with `⟨this, h⟩`.
-/
theorem isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (p : Ideal R) [p.IsMaximal] (q : Ideal S) [q.IsMaximal]
    [q.LiesOver p] [Algebra.EssFiniteType R S] (h : q.ramificationIdx R = 1)
    (hs : Algebra.IsSeparable (R ⧸ p) (S ⧸ q)) :
    Algebra.IsUnramifiedAt R q := by
  rw [Ideal.ramificationIdx_eq p q, ENat.toNat_eq_iff_eq_natCast, Nat.cast_one,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom, ← Ideal.isMaximal_def,
    IsLocalRing.isMaximal_iff] at h
  let Rp := Localization.AtPrime p
  let Sq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have := Algebra.EssFiniteType.of_comp R Rp Sq
  suffices Algebra.FormallyUnramified Rp Sq from Algebra.FormallyUnramified.comp R Rp Sq
  rw [Algebra.FormallyUnramified.iff_map_maximalIdeal_eq,
    ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have : Algebra.IsSeparable p.ResidueField q.ResidueField := inferInstance
  exact ⟨this, h⟩

/- English proof (translation)
Introduce `S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep`. Take `⟨φ⟩` from `hD`. Establish `he0 : 0 < e`. Break down `Nat.eq_zero_or_pos e with h | h` into its components or cases. Substitute `h` using the available equality.

Simplify using `at he`. Conclude with `h`. Use `haveI hAd := GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain S π e hπ he0`. Use `haveI hAv := GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible S π e hπ he0`. Use `haveI : IsDomain D := φ.toMulEquiv.isDomain`.

Use `haveI : IsPrincipalIdealRing D := IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective`. Use `haveI : IsLocalRing D := IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective`. Use `haveI : IsDiscreteValuationRing D := { not_a_field' := by`. Introduce `h`. Apply `IsDiscreteValuationRing.not_isField (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))` to reduce the goal to its premises.

Use `MulEquiv.isField ?_ φ.symm.toMulEquiv` and prove the remaining obligations. Conclude with `(IsLocalRing.isField_iff_maximalIdeal_eq).2 h }`. Use `haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) := (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite`. Use `haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv`. Use `haveI : FaithfulSMul S D := by`.

Rewrite using `[faithfulSMul_iff_algebraMap_injective]`. Introduce `a b hab`. Establish `h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a = algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b`. Rewrite using `[← φ.commutes, ← φ.commutes, hab]`. Use `set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb`.

Establish `hd : 0 < pb.dim`. Rewrite using `[hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]`. Conclude with `he0`. Establish `h0 : pb.basis ⟨0, hd⟩ = 1` using `by rw [PowerBasis.coe_basis]; simp`. Establish `key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s) ⟨0, hd⟩ = s`.

Introduce `s`. Rewrite using `[Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]`. Simplify using the standard rewrite rules. Rewrite using `[← key a, ← key b, h1]`. Use `haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := GlobalTheory.T.normalisation_dvr_tensor_separable_finite S K L D`.

Use `haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)`. Use `haveI : Module.Flat S L := Module.Flat.trans S K L`. Use `haveI : Module.Flat D (integralClosure D (TensorProduct S D L)) := by`. Rewrite using `[Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]`. Introduce `x hx`.

Take `⟨a, hax⟩` from `(Submodule.mem_torsion_iff x).1 hx`. Establish `hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S (a : D)))` using `Module.Flat.rTensor_preserves_injective_linearMap _ (fun y z h => (mul_right_injective₀ (nonZeroDivisors.ne_zero a.2)) h)`. Establish `hsmul : ∀ z : TensorProduct S D L, (a : D) • z = LinearMap.rTensor L (LinearMap.mulLeft S (a : D)) z`. Introduce `z`. Proceed by induction on `z using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul y l => simp [TensorProduct.smul_tmul']`. Consider the case `add u v hu hv => rw [smul_add, map_add, hu, hv]`. Establish `h1 : (a : D) • (x : TensorProduct S D L) = 0` using `congrArg Subtype.val hax`. Rewrite `h1` using `[hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S (a : D)))]`.

Simplify using `only [Submodule.mem_bot]`. Conclude with `Subtype.ext (hinj h1)`. Use `haveI : Algebra.FinitePresentation D (integralClosure D (TensorProduct S D L)) := Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `hmax : ∀ (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal], Algebra.IsUnramifiedAt D Q`. Introduce `Q hQ`.

Establish `hQu : Q.under D = maximalIdeal D` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)`. Use `haveI : Q.LiesOver (maximalIdeal D) := ⟨hQu.symm⟩`. Conclude with `isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable (maximalIdeal D) Q (GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q) (GlobalTheory.T.abhyankar_residueField_isSeparable_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q)`. Use `haveI : Algebra.FormallyUnramified D (integralClosure D (TensorProduct S D L)) := by`. Rewrite using `[Algebra.formallyUnramified_iff_forall]`.

Introduce `q`. Take `⟨Q, hQ, hqQ⟩` from `Ideal.exists_le_maximal q.1 q.2.ne_top`. Use `haveI := hQ`. Establish `hU` using `hmax Q`. Establish `hopen` using `Algebra.isOpen_unramifiedLocus (R := D) (A := integralClosure D (TensorProduct S D L))`.

Conclude with `hopen.stableUnderGeneralization ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU`. Conclude with `Algebra.Etale.of_formallyUnramified_of_flat`.
-/
theorem abhyankar_dvr_of_isSeparable : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    Algebra.Etale D (integralClosure D (TensorProduct S D L)) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI hAd := GlobalTheory.T.adjoinRoot_X_pow_sub_uniformizer_isDomain S π e hπ he0
  haveI hAv := GlobalTheory.T.isDVR_adjoinRoot_X_pow_sub_C_of_irreducible S π e hπ he0
  haveI : IsDomain D := φ.toMulEquiv.isDomain
  haveI : IsPrincipalIdealRing D :=
    IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective
  haveI : IsLocalRing D := IsLocalRing.of_surjective' φ.symm.toRingHom φ.symm.surjective
  haveI : IsDiscreteValuationRing D :=
    { not_a_field' := by
        intro h
        apply IsDiscreteValuationRing.not_isField (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π))
        refine MulEquiv.isField ?_ φ.symm.toMulEquiv
        exact (IsLocalRing.isField_iff_maximalIdeal_eq).2 h }
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : FaithfulSMul S D := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    have h1 : algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) a =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) b := by
      rw [← φ.commutes, ← φ.commutes, hab]
    set pb := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne') with hpb
    have hd : 0 < pb.dim := by
      rw [hpb, AdjoinRoot.powerBasis'_dim, Polynomial.natDegree_X_pow_sub_C]; exact he0
    have h0 : pb.basis ⟨0, hd⟩ = 1 := by rw [PowerBasis.coe_basis]; simp
    have key : ∀ s : S, pb.basis.repr (algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) s)
        ⟨0, hd⟩ = s := by
      intro s
      rw [Algebra.algebraMap_eq_smul_one, ← h0, map_smul, Module.Basis.repr_self]
      simp
    rw [← key a, ← key b, h1]
  haveI : Module.Finite D (integralClosure D (TensorProduct S D L)) := GlobalTheory.T.normalisation_dvr_tensor_separable_finite S K L D
  haveI : Module.Flat S K := IsLocalization.flat K (nonZeroDivisors S)
  haveI : Module.Flat S L := Module.Flat.trans S K L
  haveI : Module.Flat D (integralClosure D (TensorProduct S D L)) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    intro x hx
    obtain ⟨a, hax⟩ := (Submodule.mem_torsion_iff x).1 hx
    have hinj : Function.Injective (LinearMap.rTensor L (LinearMap.mulLeft S (a : D))) :=
      Module.Flat.rTensor_preserves_injective_linearMap _
        (fun y z h => (mul_right_injective₀ (nonZeroDivisors.ne_zero a.2)) h)
    have hsmul : ∀ z : TensorProduct S D L,
        (a : D) • z = LinearMap.rTensor L (LinearMap.mulLeft S (a : D)) z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul y l => simp [TensorProduct.smul_tmul']
      | add u v hu hv => rw [smul_add, map_add, hu, hv]
    have h1 : (a : D) • (x : TensorProduct S D L) = 0 := congrArg Subtype.val hax
    rw [hsmul, ← map_zero (LinearMap.rTensor L (LinearMap.mulLeft S (a : D)))] at h1
    simp only [Submodule.mem_bot]
    exact Subtype.ext (hinj h1)
  haveI : Algebra.FinitePresentation D (integralClosure D (TensorProduct S D L)) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hmax : ∀ (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
      Algebra.IsUnramifiedAt D Q := by
    intro Q hQ
    have hQu : Q.under D = maximalIdeal D :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
    haveI : Q.LiesOver (maximalIdeal D) := ⟨hQu.symm⟩
    exact isUnramifiedAt_of_ramificationIdx_eq_one_of_isSeparable (maximalIdeal D) Q
      (GlobalTheory.T.abhyankar_ramificationIdx_eq_one_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q) (GlobalTheory.T.abhyankar_residueField_isSeparable_alt S K L π e D ⟨φ⟩ hπ he hram hsep Q)
  haveI : Algebra.FormallyUnramified D (integralClosure D (TensorProduct S D L)) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.1 q.2.ne_top
    haveI := hQ
    have hU := hmax Q
    have hopen := Algebra.isOpen_unramifiedLocus (R := D)
      (A := integralClosure D (TensorProduct S D L))
    exact hopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GlobalTheory
