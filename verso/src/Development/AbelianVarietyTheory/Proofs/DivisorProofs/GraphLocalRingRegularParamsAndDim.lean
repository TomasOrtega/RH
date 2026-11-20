import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulKerMemSpanTrBasisDiff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegComplexBaseChangeEqStatement

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagLoc

/- English proof (translation)
Proceed by induction on `d using WithBot.recBotCoe with`. Consider the case `bot`. It suffices to derive a contradiction. Simplify using `at hd`. Conclude with `absurd hd.symm (by simp [WithBot.add_eq_bot])`.

Consider the case `coe e`. Establish `h1 : e + (m : ℕ∞) = (n : ℕ∞) + (m : ℕ∞)` using `by exact_mod_cast hd`. Establish `h2 : e = n` using `WithTop.add_right_cancel (ENat.natCast_ne_top m) h1`. Substitute `h2` using the available equality. Both sides reduce to the same expression.
-/
theorem ennreal_volume_ratio_step_cancel (d : WithBot ℕ∞) (m n : ℕ) (hd : d + m = ((n + m : ℕ) : WithBot ℕ∞)) : d = n := by
  induction d using WithBot.recBotCoe with
  | bot =>
    exfalso
    simp at hd
    exact absurd hd.symm (by simp [WithBot.add_eq_bot])
  | coe e =>
    have h1 : e + (m : ℕ∞) = (n : ℕ∞) + (m : ℕ∞) := by exact_mod_cast hd
    have h2 : e = n := WithTop.add_right_cancel (ENat.natCast_ne_top m) h1
    subst h2
    rfl

/- English proof (translation)
The claim follows from `Subring.mem_top _ isLocalRing := IsLocalRing.of_surjective' (Subring.topEquiv (R := K)).symm.toRingHom (Subring.topEquiv (R := K)).symm.surjective essFiniteType := by letI : Algebra ℂ (⊤ : Subring K) := ((algebraMap ℂ K).codRestrict (⊤ : Subring K) fun _ => Subring.mem_top _).toA …`.
-/
theorem isLocModel_top {K : Type} [Field K] [Algebra ℂ K] [Algebra.EssFiniteType ℂ K] :
    IsLocModel (algebraMap ℂ K) (⊤ : Subring K) where
  const_mem _ := Subring.mem_top _
  isLocalRing := IsLocalRing.of_surjective' (Subring.topEquiv (R := K)).symm.toRingHom
    (Subring.topEquiv (R := K)).symm.surjective
  essFiniteType := by
    letI : Algebra ℂ (⊤ : Subring K) :=
      ((algebraMap ℂ K).codRestrict (⊤ : Subring K) fun _ => Subring.mem_top _).toAlgebra
    show Algebra.EssFiniteType ℂ (⊤ : Subring K)
    exact Algebra.EssFiniteType.of_surjective
      { (Subring.topEquiv (R := K)).symm.toRingHom with commutes' := fun _ => rfl }
      (Subring.topEquiv (R := K)).symm.surjective
  frac f := ⟨f, Subring.mem_top _, 1, Subring.mem_top _, one_ne_zero, mul_one f⟩

variable {K κ' : Type} [Field K] [Field κ'] [Algebra ℂ K] [Algebra ℂ κ']
  (L : Type) [Field L] [Algebra (K ⊗[ℂ] κ') L] [IsFractionRing (K ⊗[ℂ] κ') L]

/- English proof (translation)
Take `⟨e, he1, he⟩` from `GlobalTheory.FieldPair.exists_mul_ker_mem_span_trBasis_diff n x σ (⊤ : Subring K) hx isLocModel_top`. Use `haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime := RingHom.ker_isPrime _`. Establish `heP : e ∈ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl`. Rewrite using `[Ideal.mem_primeCompl_iff]`. Introduce `h`.

Rewrite `h` using `[RingHom.mem_ker]`. Rewrite `he1` using `[h]`. Conclude with `zero_ne_one he1`. Use `haveI : IsDomain (K ⊗[ℂ] κ') := Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)`. Use `letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _))`.

Use `haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl ↥(loc L σ) := by`. Conclude with `Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))) ↥(loc L σ)]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Introduce `a ha`. Rewrite using `[Ideal.mem_comap]`. Take `⟨u, hu⟩` from `IsLocalization.map_units (M := (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl) (S := ↥(loc L σ)) ⟨e, heP⟩`. Establish `h1` using `Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) (he a ha)`. Rewrite `h1` using `[Ideal.map_span, ← Set.range_comp]`.

Establish `h2 : algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) a = ((u⁻¹ : (↥(loc L σ))ˣ) : ↥(loc L σ)) * algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (e * a)`. Rewrite using `[map_mul, show algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) e = (u : ↥(loc L σ)) from hu.symm, ← mul_assoc, Units.inv_mul, one_mul]`. Rewrite using `[h2]`. Conclude with `Ideal.mul_mem_left _ _ h1`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) ?_` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker]`. Simplify using the standard rewrite rules.
-/
theorem maximalIdeal_eq_span (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] (hx : TrBasis (algebraMap ℂ K) x) :
    IsLocalRing.maximalIdeal (loc L σ) =
      Ideal.span (Set.range fun i => toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) := by
  obtain ⟨e, he1, he⟩ := GlobalTheory.FieldPair.exists_mul_ker_mem_span_trBasis_diff n x σ (⊤ : Subring K) hx
    isLocModel_top
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime :=
    RingHom.ker_isPrime _
  have heP : e ∈ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl := by
    rw [Ideal.mem_primeCompl_iff]
    intro h
    rw [RingHom.mem_ker] at h
    rw [h] at he1
    exact zero_ne_one he1
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
    (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
      ↥(loc L σ) := by
    exact Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))) ↥(loc L σ)]
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    obtain ⟨u, hu⟩ := IsLocalization.map_units
      (M := (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl)
      (S := ↥(loc L σ)) ⟨e, heP⟩
    have h1 := Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) (he a ha)
    rw [Ideal.map_span, ← Set.range_comp] at h1
    have h2 : algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) a =
        ((u⁻¹ : (↥(loc L σ))ˣ) : ↥(loc L σ)) * algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (e * a) := by
      rw [map_mul, show algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) e = (u : ↥(loc L σ)) from hu.symm,
        ← mul_assoc, Units.inv_mul, one_mul]
    rw [h2]
    exact Ideal.mul_mem_left _ _ h1
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    refine Ideal.mem_map_of_mem (algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)) ?_
    rw [RingHom.mem_ker]
    simp

/- English proof (translation)
Use `haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime := RingHom.ker_isPrime _`. Use `haveI : IsDomain (K ⊗[ℂ] κ') := Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)`. Use `letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _))`. Use `haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl ↥(loc L σ) := Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _`. Use `letI : Algebra ℂ ↥(loc L σ) := ((algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra`.

Use `haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') ↥(loc L σ) := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')`. Use `haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') ↥(loc L σ) := Algebra.EssFiniteType.of_isLocalization _ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl`. Use `haveI : Algebra.EssFiniteType ℂ ↥(loc L σ) := Algebra.EssFiniteType.comp ℂ (K ⊗[ℂ] κ') ↥(loc L σ)`. Establish `hg : ∀ y : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl, IsUnit ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).toRingHom (y : K ⊗[ℂ] κ'))`.

Introduce `y`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h`. Conclude with `y.2 (RingHom.mem_ker.mpr h)`. Use `letI : Algebra ↥(loc L σ) κ' := (IsLocalization.lift hg).toAlgebra`.

Use `haveI : IsScalarTower ℂ ↥(loc L σ) κ' := IsScalarTower.of_algebraMap_eq fun c => ((IsLocalization.lift_eq hg (algebraMap ℂ (K ⊗[ℂ] κ') c)).trans ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).commutes c)).symm`. Establish `hsurj : Function.Surjective (algebraMap ↥(loc L σ) κ')` using `fun b => ⟨algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (1 ⊗ₜ b), by show IsLocalization.lift hg _ = b`. Rewrite using `[IsLocalization.lift_eq]`. Use the proof step `simp⟩`. Establish `hx' : IsTranscendenceBasis ℂ x`.

Unfold `TrBasis at hx`. Rewrite `hx` using `[toAlgebra_algebraMap]`. Then use the resulting hypothesis. Establish `hK : Algebra.trdeg ℂ K = n`. Rewrite using `[← hx'.cardinalMk_eq_trdeg, Cardinal.mk_fin]`. Establish `hfin : Algebra.trdeg ℂ κ' < Cardinal.aleph0`.

Conclude with `trdeg_lt_aleph0 ℂ κ'`. Establish `hm : Algebra.trdeg ℂ κ' = ((Algebra.trdeg ℂ κ').toNat : Cardinal)` using `(Cardinal.cast_toNat_of_lt_aleph0 hfin).symm`. Use `haveI : FaithfulSMul ℂ K := (faithfulSMul_iff_algebraMap_injective ℂ K).mpr (algebraMap ℂ K).injective`. Use `haveI : FaithfulSMul K (K ⊗[ℂ] κ') := (faithfulSMul_iff_algebraMap_injective K (K ⊗[ℂ] κ')).mpr (algebraMap K (K ⊗[ℂ] κ')).injective`. Use `haveI : FaithfulSMul ℂ (K ⊗[ℂ] κ') := (faithfulSMul_iff_algebraMap_injective ℂ (K ⊗[ℂ] κ')).mpr (algebraMap ℂ (K ⊗[ℂ] κ')).injective`.

Use `haveI : FaithfulSMul (K ⊗[ℂ] κ') ↥(loc L σ) := (faithfulSMul_iff_algebraMap_injective (K ⊗[ℂ] κ') ↥(loc L σ)).mpr (IsLocalization.injective ↥(loc L σ) (Ideal.primeCompl_le_nonZeroDivisors (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')))))`. Use `haveI : Algebra.IsAlgebraic (K ⊗[ℂ] κ') ↥(loc L σ) := IsLocalization.isAlgebraic ↥(loc L σ) (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl`. Establish `hR : Algebra.trdeg ℂ ↥(loc L σ) = ((n + (Algebra.trdeg ℂ κ').toNat : ℕ) : Cardinal)`. Establish `h0 : Algebra.trdeg (K ⊗[ℂ] κ') ↥(loc L σ) = 0` using `trdeg_eq_zero`. Rewrite using `[← trdeg_add_eq ℂ (K ⊗[ℂ] κ') (A := ↥(loc L σ)), h0, add_zero, ← trdeg_add_eq ℂ K (A := K ⊗[ℂ] κ'), GlobalTheory.T.trdeg_tensor_complex_eq, hK, hm]`.

Use `push_cast`. Both sides reduce to the same expression. Conclude with `ennreal_volume_ratio_step_cancel _ _ _ (GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := ℂ) (R := ↥(loc L σ)) (Ω := κ') hsurj hm hR)`.
-/
theorem ringKrullDim_loc (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K)
    [Algebra.EssFiniteType ℂ K] [Algebra.EssFiniteType ℂ κ'] (hx : TrBasis (algebraMap ℂ K) x) :
    ringKrullDim (loc L σ) = n := by
  haveI hP : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).IsPrime := RingHom.ker_isPrime _
  haveI : IsDomain (K ⊗[ℂ] κ') :=
    Function.Injective.isDomain (algebraMap (K ⊗[ℂ] κ') L) (IsFractionRing.injective (K ⊗[ℂ] κ') L)
  letI : Algebra (K ⊗[ℂ] κ') ↥(loc L σ) := Subalgebra.algebra (Localization.subalgebra.ofField L
    (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl (Ideal.primeCompl_le_nonZeroDivisors _))
  haveI hloc : IsLocalization (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl ↥(loc L σ) :=
    Localization.subalgebra.isLocalization_ofField (A := K ⊗[ℂ] κ') L _ _
  letI : Algebra ℂ ↥(loc L σ) :=
    ((algebraMap (K ⊗[ℂ] κ') ↥(loc L σ)).comp (algebraMap ℂ (K ⊗[ℂ] κ'))).toAlgebra
  haveI : IsScalarTower ℂ (K ⊗[ℂ] κ') ↥(loc L σ) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : Algebra.EssFiniteType ℂ (K ⊗[ℂ] κ') := Algebra.EssFiniteType.comp ℂ K (K ⊗[ℂ] κ')
  haveI : Algebra.EssFiniteType (K ⊗[ℂ] κ') ↥(loc L σ) :=
    Algebra.EssFiniteType.of_isLocalization _ (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  haveI : Algebra.EssFiniteType ℂ ↥(loc L σ) := Algebra.EssFiniteType.comp ℂ (K ⊗[ℂ] κ') ↥(loc L σ)
  have hg : ∀ y : (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl,
      IsUnit ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).toRingHom (y : K ⊗[ℂ] κ')) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h
    exact y.2 (RingHom.mem_ker.mpr h)
  letI : Algebra ↥(loc L σ) κ' := (IsLocalization.lift hg).toAlgebra
  haveI : IsScalarTower ℂ ↥(loc L σ) κ' := IsScalarTower.of_algebraMap_eq fun c =>
    ((IsLocalization.lift_eq hg (algebraMap ℂ (K ⊗[ℂ] κ') c)).trans
      ((Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')).commutes c)).symm
  have hsurj : Function.Surjective (algebraMap ↥(loc L σ) κ') := fun b =>
    ⟨algebraMap (K ⊗[ℂ] κ') ↥(loc L σ) (1 ⊗ₜ b), by
      show IsLocalization.lift hg _ = b
      rw [IsLocalization.lift_eq]
      simp⟩
  have hx' : IsTranscendenceBasis ℂ x := by
    unfold TrBasis at hx
    rwa [toAlgebra_algebraMap] at hx
  have hK : Algebra.trdeg ℂ K = n := by
    rw [← hx'.cardinalMk_eq_trdeg, Cardinal.mk_fin]
  have hfin : Algebra.trdeg ℂ κ' < Cardinal.aleph0 := by
    exact trdeg_lt_aleph0 ℂ κ'
  have hm : Algebra.trdeg ℂ κ' = ((Algebra.trdeg ℂ κ').toNat : Cardinal) :=
    (Cardinal.cast_toNat_of_lt_aleph0 hfin).symm
  haveI : FaithfulSMul ℂ K :=
    (faithfulSMul_iff_algebraMap_injective ℂ K).mpr (algebraMap ℂ K).injective
  haveI : FaithfulSMul K (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective K (K ⊗[ℂ] κ')).mpr (algebraMap K (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul ℂ (K ⊗[ℂ] κ') :=
    (faithfulSMul_iff_algebraMap_injective ℂ (K ⊗[ℂ] κ')).mpr (algebraMap ℂ (K ⊗[ℂ] κ')).injective
  haveI : FaithfulSMul (K ⊗[ℂ] κ') ↥(loc L σ) :=
    (faithfulSMul_iff_algebraMap_injective (K ⊗[ℂ] κ') ↥(loc L σ)).mpr
      (IsLocalization.injective ↥(loc L σ) (Ideal.primeCompl_le_nonZeroDivisors (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ')))))
  haveI : Algebra.IsAlgebraic (K ⊗[ℂ] κ') ↥(loc L σ) :=
    IsLocalization.isAlgebraic ↥(loc L σ) (RingHom.ker (Algebra.TensorProduct.productMap σ (AlgHom.id ℂ κ'))).primeCompl
  have hR : Algebra.trdeg ℂ ↥(loc L σ) = ((n + (Algebra.trdeg ℂ κ').toNat : ℕ) : Cardinal) := by
    have h0 : Algebra.trdeg (K ⊗[ℂ] κ') ↥(loc L σ) = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq ℂ (K ⊗[ℂ] κ') (A := ↥(loc L σ)), h0, add_zero,
      ← trdeg_add_eq ℂ K (A := K ⊗[ℂ] κ'), GlobalTheory.T.trdeg_tensor_complex_eq, hK, hm]
    push_cast
    rfl
  exact ennreal_volume_ratio_step_cancel _ _ _
    (GlobalTheory.LocModelDim.ringKrullDim_add_trdeg (k := ℂ) (R := ↥(loc L σ)) (Ω := κ') hsurj hm hR)

/- English proof (translation)
Introduce `K κ' L _ _ _ _ _ _ _ _ _ σ n x hK hκ hx`. Conclude with `⟨maximalIdeal_eq_span L σ n x hx, ringKrullDim_loc L σ n x hx⟩`.
-/
theorem maximalIdeal_eq_span_and_ringKrullDim : ∀ {K κ' L : Type} [Field K] [Field κ'] [Field L] [Algebra ℂ K]
  [Algebra ℂ κ'] [Algebra ℂ L] [Algebra (K ⊗[ℂ] κ') L] [IsScalarTower ℂ (K ⊗[ℂ] κ') L]
  [IsFractionRing (K ⊗[ℂ] κ') L] (σ : K →ₐ[ℂ] κ') (n : ℕ) (x : Fin n → K),
  Algebra.EssFiniteType ℂ K → Algebra.EssFiniteType ℂ κ' → TrBasis (algebraMap ℂ K) x →
  IsLocalRing.maximalIdeal (GlobalTheory.DiagLoc.loc L σ) =
      Ideal.span (Set.range fun i => GlobalTheory.DiagLoc.toLoc L σ (x i ⊗ₜ[ℂ] 1 - 1 ⊗ₜ[ℂ] σ (x i))) ∧
    ringKrullDim (GlobalTheory.DiagLoc.loc L σ) = n := by
  intro K κ' L _ _ _ _ _ _ _ _ _ σ n x hK hκ hx
  exact ⟨maximalIdeal_eq_span L σ n x hx, ringKrullDim_loc L σ n x hx⟩

end GlobalTheory.DiagLoc
