import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIntegralClosureOfIsArtinianRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationIntegralClosureEquiv
open IsLocalRing Polynomial

namespace GlobalTheory.PurityLoc

noncomputable def integralClosureEquiv (R C : Type) [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (M : Submonoid R)
    (h : IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C M))) :
    C ≃ₐ[R] integralClosure R (Localization (Algebra.algebraMapSubmonoid C M)) :=
  AlgEquiv.ofBijective
    ((IsScalarTower.toAlgHom R C _).codRestrict _ fun c =>
      (Algebra.IsIntegral.isIntegral (R := R) c).map (IsScalarTower.toAlgHom R C _))
    (by
      obtain ⟨hinj, hcl⟩ := isIntegrallyClosedIn_iff.mp h
      refine ⟨fun x y hxy => hinj (congrArg Subtype.val hxy), fun ⟨x, hx⟩ => ?_⟩
      obtain ⟨c, hc⟩ := hcl (hx.tower_top (A := C))
      exact ⟨c, Subtype.ext hc⟩)

/- English proof (translation)
Use `haveI := h`. Use `haveI hKfr : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by`. Conclude with `(congrArg (fun M : Submonoid R => IsLocalization M (Localization.AtPrime (⊥ : Ideal R))) (Ideal.primeCompl_bot (α := R))).mp inferInstance`. Use `letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R`. Use `haveI : IsReduced (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := Algebra.FormallyUnramified.isReduced_of_field (Localization.AtPrime (⊥ : Ideal R)) _`.

Use `haveI : IsArtinianRing (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := IsArtinianRing.of_finite (Localization.AtPrime (⊥ : Ideal R)) _`. Use `letI : Algebra C (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)) (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := by`. Conclude with `(congrArg (fun M : Submonoid R => IsLocalization (Algebra.algebraMapSubmonoid C M) (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) (Ideal.primeCompl_bot (α := R))).mp (IsLocalization.tensorRight (S := C) (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl)`. Set `e` to `IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)`.

Conclude with `⟨isReduced_of_injective e.toRingHom e.injective, e.toRingEquiv.symm.isArtinianRing⟩`.
-/
theorem isReduced_isArtinianRing_localization (R C : Type) [CommRing R] [IsDomain R] [CommRing C]
    [Algebra R C] [Module.Finite R C]
    (h : Algebra.Etale (Localization.AtPrime (⊥ : Ideal R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) :
    IsReduced (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) ∧
      IsArtinianRing (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) := by
  haveI := h
  haveI hKfr : IsFractionRing R (Localization.AtPrime (⊥ : Ideal R)) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization M (Localization.AtPrime (⊥ : Ideal R)))
      (Ideal.primeCompl_bot (α := R))).mp inferInstance
  letI : Field (Localization.AtPrime (⊥ : Ideal R)) := IsFractionRing.toField R
  haveI : IsReduced (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.FormallyUnramified.isReduced_of_field (Localization.AtPrime (⊥ : Ideal R)) _
  haveI : IsArtinianRing (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    IsArtinianRing.of_finite (Localization.AtPrime (⊥ : Ideal R)) _
  letI : Algebra C (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) :=
    Algebra.TensorProduct.rightAlgebra
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C) := by
    exact (congrArg (fun M : Submonoid R => IsLocalization (Algebra.algebraMapSubmonoid C M)
      (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)) (Ideal.primeCompl_bot (α := R))).mp
      (IsLocalization.tensorRight (S := C) (Localization.AtPrime (⊥ : Ideal R)) (⊥ : Ideal R).primeCompl)
  let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
    (TensorProduct R (Localization.AtPrime (⊥ : Ideal R)) C)
  exact ⟨isReduced_of_injective e.toRingHom e.injective, e.toRingEquiv.symm.isArtinianRing⟩

/- English proof (translation)
Introduce `R C _ _ _ _ _ hC P _ hreg hP`. Use `haveI := hreg`. Take `⟨hred, hart⟩` from `isReduced_isArtinianRing_localization R C (hP ⊥ bot_le (by simp))`. Set `iC` to `integralClosureEquiv R C (nonZeroDivisors R) hC`. Establish `hb` using `TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R) (S := Localization.AtPrime P) (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl`.

Set `Φ : TensorProduct R (Localization.AtPrime P) C ≃ₐ[Localization.AtPrime P] integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))` to `(Algebra.TensorProduct.congr AlgEquiv.refl iC).trans (AlgEquiv.ofBijective _ hb)`. Establish `hRE : IsReduced (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) ∧ IsArtinianRing (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))`. Use `letI : Algebra (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := Algebra.TensorProduct.rightAlgebra`. Use `haveI : IsLocalization (Algebra.algebraMapSubmonoid (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := IsLocalization.tensorRight (Locali …`. Use `haveI := hred`.

Use `haveI := hart`. Set `e` to `IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (Localization (Algebra.algebraMapSub …`. Conclude with `⟨isReduced_of_injective e.toRingHom e.injective, IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) _⟩`. Establish `hunit : ∀ s : Localization.AtPrime P, s ≠ 0 → IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) s)`. Introduce `s hs`.

Take `⟨⟨r, u⟩, rfl⟩` from `IsLocalization.mk'_surjective P.primeCompl s`. Establish `hr : r ≠ 0` using `by rintro rfl; exact hs (by simp)`. Establish `h0 : IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) r)`. Rewrite using `[IsScalarTower.algebraMap_apply R C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))]`. Conclude with `IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) (⟨algebraMap R C r, Algebra.mem_algebraMapSubmonoid_of_mem (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R)⟩ : Algebra.algebraMapSubmonoid C (nonZeroDivisors R))`.

Establish `h1 : IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (algebraMap R _ r))`. Rewrite using `[← IsScalarTower.algebraMap_apply R (Localization.AtPrime P), ← (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime P) (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))).commutes r]`. Conclude with `h0.map _`. Establish `h2 : algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (IsLocalization.mk' (Localization.AtPrime P) r u) * algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) …`. Rewrite using `[← map_mul, IsLocalization.mk'_spec]`.

Rewrite `h1` using `[← h2]`. Conclude with `isUnit_of_mul_isUnit_left h1`. Establish `hnz : NoZeroSMulDivisors (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))` using `⟨fun {s x} h => by`. Distinguish the cases in `hs : s = 0`. Conclude with `Or.inl hs`.

Use `right`. Rewrite `h` using `[Algebra.smul_def]`. Conclude with `(hunit s hs).mul_right_eq_zero.mp h⟩`. Use `haveI hfin : Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))) := Module.Finite.equiv Φ.toLinearEquiv`. Establish `hq : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime], q.height ≤ 1 → Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P) (Localization.AtPrime q) (integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) (Localization (Algeb …`.

Introduce `q _ hq1`. Establish `hle : q.comap (algebraMap R (Localization.AtPrime P)) ≤ P`. Use `Ideal.comap_mono (f := algebraMap R (Localization.AtPrime P)) (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›))` as an intermediate fact. Conclude with `this.trans (Localization.AtPrime.comap_maximalIdeal (I := P)).le`. Establish `hh : (q.comap (algebraMap R (Localization.AtPrime P))).height ≤ 1` using `(le_of_eq (IsLocalization.height_comap P.primeCompl q)).trans hq1`.

Use `haveI h1 := GlobalTheory.OffDivisor.etale_localization_of_comap R (Localization.AtPrime P) C _ q rfl (hP _ hle hh)`. Conclude with `Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P) (Localization.AtPrime q) (Localization.AtPrime q) C).symm.trans (Algebra.TensorProduct.congr AlgEquiv.refl Φ))`. Use `haveI := GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing (Localization.AtPrime P) _ hRE.1 hRE.2 hnz hfin hq`. Conclude with `Algebra.Etale.of_equiv Φ.symm`.
-/
theorem etale_atPrime_of_isIntegrallyClosedIn : ∀ (R C : Type) [CommRing R] [IsDomain R] [CommRing C] [Algebra R C] [Module.Finite R C],
    IsIntegrallyClosedIn C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) →
    ∀ (P : Ideal R) [P.IsPrime], IsRegularLocalRing (Localization.AtPrime P) →
    (∀ (P' : Ideal R) [P'.IsPrime], P' ≤ P → P'.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime P') (TensorProduct R (Localization.AtPrime P') C)) →
    Algebra.Etale (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P) C) := by
  intro R C _ _ _ _ _ hC P _ hreg hP
  haveI := hreg
  obtain ⟨hred, hart⟩ := isReduced_isArtinianRing_localization R C (hP ⊥ bot_le (by simp))
  let iC := integralClosureEquiv R C (nonZeroDivisors R) hC
  have hb := TensorProduct.toIntegralClosure_bijective_of_isLocalization (R := R)
    (S := Localization.AtPrime P)
    (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl
  let Φ : TensorProduct R (Localization.AtPrime P) C ≃ₐ[Localization.AtPrime P]
      integralClosure (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
    (Algebra.TensorProduct.congr AlgEquiv.refl iC).trans (AlgEquiv.ofBijective _ hb)
  have hRE : IsReduced (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) ∧
      IsArtinianRing (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := by
    letI : Algebra (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      Algebra.TensorProduct.rightAlgebra
    haveI : IsLocalization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
        (TensorProduct R (Localization.AtPrime P)
          (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) :=
      IsLocalization.tensorRight (Localization.AtPrime P) P.primeCompl
    haveI := hred
    haveI := hart
    let e := IsLocalization.algEquiv (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
      (Localization (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl))
    exact ⟨isReduced_of_injective e.toRingHom e.injective,
      IsArtinianRing.localization_artinian (Algebra.algebraMapSubmonoid
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) P.primeCompl) _⟩
  have hunit : ∀ s : Localization.AtPrime P, s ≠ 0 → IsUnit (algebraMap (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) s) := by
    intro s hs
    obtain ⟨⟨r, u⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl s
    have hr : r ≠ 0 := by rintro rfl; exact hs (by simp)
    have h0 : IsUnit (algebraMap R (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))) r) := by
      rw [IsScalarTower.algebraMap_apply R C (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))]
      exact IsLocalization.map_units (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))
        (⟨algebraMap R C r, Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨r, mem_nonZeroDivisors_of_ne_zero hr⟩ : nonZeroDivisors R)⟩ :
            Algebra.algebraMapSubmonoid C (nonZeroDivisors R))
    have h1 : IsUnit (algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) (algebraMap R _ r)) := by
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime P),
        ← (Algebra.TensorProduct.includeRight (R := R) (A := Localization.AtPrime P)
          (B := Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))).commutes r]
      exact h0.map _
    have h2 : algebraMap (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))
          (IsLocalization.mk' (Localization.AtPrime P) r u) *
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) u) =
        algebraMap (Localization.AtPrime P) _ (algebraMap R (Localization.AtPrime P) r) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [← h2] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hnz : NoZeroSMulDivisors (Localization.AtPrime P) (TensorProduct R (Localization.AtPrime P)
      (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))) := ⟨fun {s x} h => by
    by_cases hs : s = 0
    · exact Or.inl hs
    · right
      rw [Algebra.smul_def] at h
      exact (hunit s hs).mul_right_eq_zero.mp h⟩
  haveI hfin : Module.Finite (Localization.AtPrime P) (integralClosure (Localization.AtPrime P)
      (TensorProduct R (Localization.AtPrime P)
        (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R))))) :=
    Module.Finite.equiv Φ.toLinearEquiv
  have hq : ∀ (q : Ideal (Localization.AtPrime P)) [q.IsPrime], q.height ≤ 1 →
      Algebra.Etale (Localization.AtPrime q) (TensorProduct (Localization.AtPrime P)
        (Localization.AtPrime q) (integralClosure (Localization.AtPrime P)
          (TensorProduct R (Localization.AtPrime P)
            (Localization (Algebra.algebraMapSubmonoid C (nonZeroDivisors R)))))) := by
    intro q _ hq1
    have hle : q.comap (algebraMap R (Localization.AtPrime P)) ≤ P := by
      have := Ideal.comap_mono (f := algebraMap R (Localization.AtPrime P))
        (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top ‹q.IsPrime›))
      exact this.trans (Localization.AtPrime.comap_maximalIdeal (I := P)).le
    have hh : (q.comap (algebraMap R (Localization.AtPrime P))).height ≤ 1 :=
      (le_of_eq (IsLocalization.height_comap P.primeCompl q)).trans hq1
    haveI h1 := GlobalTheory.OffDivisor.etale_localization_of_comap R (Localization.AtPrime P) C _ q rfl
      (hP _ hle hh)
    exact Algebra.Etale.of_equiv ((Algebra.TensorProduct.cancelBaseChange R (Localization.AtPrime P)
      (Localization.AtPrime q) (Localization.AtPrime q) C).symm.trans
        (Algebra.TensorProduct.congr AlgEquiv.refl Φ))
  haveI := GlobalTheory.PurityProd.etale_integralClosure_of_isArtinianRing (Localization.AtPrime P) _
    hRE.1 hRE.2 hnz hfin hq
  exact Algebra.Etale.of_equiv Φ.symm

end GlobalTheory.PurityLoc
