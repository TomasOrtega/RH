import Mathlib
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
open TensorProduct

namespace GlobalTheory.PointSupport

open TensorProduct in
open TensorProduct in

/- English proof (translation)
Use `letI : Field (R ⧸ M) := Ideal.Quotient.field M`. Use `haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)`. Set `e : K ≃ₐ[K] R ⧸ M` to `AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral`. Use `⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`.
-/
theorem _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

open TensorProduct in
open TensorProduct in

/- English proof (translation)
Introduce `K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp`. Use `haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)`. Establish `hχ₀ : Function.Surjective χ₀` using `fun k => ⟨algebraMap K R k, χ₀.commutes k⟩`. Use `haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀`. Establish `hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀`.

Introduce `M hM hle`. Take `⟨χ, hχ⟩` from `_root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M`. Distinguish the cases in `h : χ = χ₀`. Rewrite using `[← hχ, h]`. Take `⟨r, hr, hrz⟩` from `hsupp χ h`.

Establish `hrM : r ∈ M` using `hle (Module.mem_annihilator.mpr hrz)`. Rewrite `hrM` using `[← hχ]`. Conclude with `absurd (RingHom.mem_ker.mp hrM) hr`. Establish `hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀`. Introduce `Q hQ hle`.

Rewrite using `[← IsJacobsonRing.out' Q hQ.isRadical]`. Apply `le_antisymm` to reduce the goal to its premises. Take `⟨J, hJ, hQJ⟩` from `Ideal.exists_le_maximal Q hQ.ne_top`. Rewrite using `[← hmax J hJ (hle.trans hQJ)]`. Conclude with `sInf_le ⟨hQJ, hJ⟩`.

Conclude with `le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge`. Use `letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator`. Establish `hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z` using `fun _ _ => rfl`. Use `haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H := ⟨fun r a z => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`.

Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩`. Use `haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H := ⟨fun k a z => by`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Rewrite using `[Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def, smul_assoc]⟩`. Use `haveI : Module.Finite (R ⧸ Module.annihilator R H) H := Module.Finite.of_restrictScalars_finite R _ H`.

Establish `hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime → Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀` using `fun Q hQ => hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]`. Conclude with `Q.zero_mem`. Use `haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by`. Rewrite using `[← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]`.

Use `Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_` and prove the remaining obligations. Rewrite using `[Ideal.mk_ker, ← hprimeq Q hQ]`. Introduce `r hr`. Rewrite using `[Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]`. Conclude with `Q.zero_mem`.

Use `haveI : Module.Finite K (R ⧸ Module.annihilator R H) := (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance`. Use `haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H`. Establish `hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s)`. Introduce `s`. Establish `ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R))`.

Assume the negation of the conclusion as `h`. Take `⟨I, hI, hsI⟩` from `exists_max_ideal_of_mem_nonunits h`. Establish `hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I` using `hsI`. Rewrite `hsI'` using `[hprimeq I hI.isPrime]`. Conclude with `s.2 hsI'`.

Rewrite using `[Module.End.isUnit_iff]`. Take `⟨b, hb⟩` from `ha.exists_right_inv`. Use `⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩` and prove the remaining obligations. Rewrite `hxy` using `[Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk]`. Conclude with `ha.smul_left_cancel.mp hxy`.

Rewrite using `[Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]`. Use `haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) := IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩) (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)`. Set `e : H ≃ₗ[R] O ⊗[R] H` to `IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl LinearMap.id (TensorProduct.mk R O H 1)`. Use `letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra`. Use `haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl`.

Set `eK : H ≃ₗ[K] O ⊗[R] H` to `e.restrictScalars K`. Use `haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)`. Use `haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by`. Distinguish the cases in `h0 : k = 0`. Rewrite `hk` using `[h0, map_zero]`.

Conclude with `absurd hk not_isUnit_zero`. Conclude with `isUnit_iff_ne_zero.mpr h0⟩`. Use `haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK`. Establish `hsurj : Function.Surjective (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))`. Establish `hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈ (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange`.

Introduce `r`. Use `⟨IsLocalRing.residue K (χ₀ r), ?_⟩` and prove the remaining obligations. Establish `hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]`. Rewrite `hmem` using `[← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero]`.

Rewrite using `[hmem]`. Conclude with `IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)`. Introduce `x`. Take `⟨o, rfl⟩` from `IsLocalRing.residue_surjective x`. Take `⟨r, s, rfl⟩` from `IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o`.

Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, map_mul]`. Establish `hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) = (IsLocalRing.residue O (algebraMap R O s))⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← map_mul, IsLocalization.mk'_spec, map_one, map_one]`. Rewrite using `[hs]`.

Conclude with `Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))`. Establish `hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1`. Set `f` to `LinearEquiv.ofBijective (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩`. Rewrite using `[← f.length_eq, Module.length_eq_one_iff]`. Use `infer_instance`.

Establish `hlen` using `IsLocalRing.length_restrictScalars K O (O ⊗[R] H)`. Rewrite `hlen` using `[hres, mul_one, Module.length_eq_finrank K]`. Establish `hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H)` using `eK.finrank_eq`. Use `⟨?_, hfin, ?_⟩` and prove the remaining obligations. Rewrite using `[← Module.length_ne_top_iff, ← hlen]`.

Conclude with `ENat.coe_ne_top _`. Rewrite using `[hfr]`. Conclude with `hlen`.
-/
theorem _root_.GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  intro K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hχ₀ : Function.Surjective χ₀ := fun k => ⟨algebraMap K R k, χ₀.commutes k⟩
  haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀

  have hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀ := by
    intro M hM hle
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
    by_cases h : χ = χ₀
    · rw [← hχ, h]
    · obtain ⟨r, hr, hrz⟩ := hsupp χ h
      have hrM : r ∈ M := hle (Module.mem_annihilator.mpr hrz)
      rw [← hχ] at hrM
      exact absurd (RingHom.mem_ker.mp hrM) hr

  have hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀ := by
    intro Q hQ hle
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge

  letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator
  have hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z :=
    fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H :=
    ⟨fun r a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H :=
    ⟨fun k a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
        smul_assoc]⟩
  haveI : Module.Finite (R ⧸ Module.annihilator R H) H :=
    Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀ := fun Q hQ =>
    hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact Q.zero_mem
  haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  haveI : Module.Finite K (R ⧸ Module.annihilator R H) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H

  have hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s) := by
    intro s
    have ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R)) := by
      by_contra h
      obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits h
      have hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I := hsI
      rw [hprimeq I hI.isPrime] at hsI'
      exact s.2 hsI'
    rw [Module.End.isUnit_iff]
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    refine ⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at hxy
      exact ha.smul_left_cancel.mp hxy
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]
  haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩)
      (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)

  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK : H ≃ₗ[K] O ⊗[R] H := e.restrictScalars K
  haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)
  haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h0 : k = 0
    · rw [h0, map_zero] at hk
      exact absurd hk not_isUnit_zero
    · exact isUnit_iff_ne_zero.mpr h0⟩
  haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK

  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    have hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange := by
      intro r
      refine ⟨IsLocalRing.residue K (χ₀ r), ?_⟩
      have hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker,
          map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
      rw [hmem]
      exact IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    have hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) =
        (IsLocalRing.residue O (algebraMap R O s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [hs]
    exact Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  have hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H) := eK.finrank_eq
  refine ⟨?_, hfin, ?_⟩
  · rw [← Module.length_ne_top_iff, ← hlen]
    exact ENat.coe_ne_top _
  · rw [hfr]
    exact hlen

end GlobalTheory.PointSupport
