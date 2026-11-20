import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap

noncomputable section
namespace GlobalTheory.UnitLemma.Unr
open Polynomial

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `by rintro rfl; simp at hN`. Establish `hzR : IsIntegral R z`. Use `⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩` and prove the remaining obligations. Simplify using `[eval₂_sub, hz]`. Establish `hzF : IsIntegral F z` using `hzR.tower_top`.

Set `pb` to `PowerBasis.ofAdjoinEqTop hzF hadj`. Establish `hgen : pb.gen = z` using `PowerBasis.ofAdjoinEqTop_gen hzF hadj`. Establish `hmem` using `Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)`. Rewrite `hmem` using `[hgen]`. Use `haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by`.

Rewrite `hx` using `[Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L, map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff]`. Conclude with `hx`. Establish `hIntAe : ∀ p : R[X], IsIntegral R (aeval z p)` using `fun p => adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)`. Use `set m := minpoly R z with hm`. Take `⟨h, hmh⟩ : m ∣ X ^ N - C 1` from `minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])`.

Establish `hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h`. Use `congrArg (fun p => aeval z (derivative p)) hmh` as an intermediate fact. Simplify using `only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add, map_mul] at this`. Establish `h0 : aeval z m = 0` using `minpoly.aeval R z`. Simplify `this` using `[h0]`.

Establish `hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x` using `fun x hx => IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)`. Take `⟨ra, hra⟩` from `hint _ (hIntAe (derivative m))`. Take `⟨rb, hrb⟩` from `hint _ (hIntAe h)`. Take `⟨rz, hrz⟩` from `hint _ hzR`. Establish `hinj` using `IsFractionRing.injective R F`.

Establish `hrzN : rz ^ N = 1` using `hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])`. Establish `hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1)`. Apply `hinj` to reduce the goal to its premises. Establish `hNL : ((N : L)) = algebraMap F L (N : F)` using `(map_natCast _ _).symm`. Rewrite using `[map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL, Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]`.

Establish `hra_unit : IsUnit ra`. Establish `: IsUnit (ra * rb)`. Rewrite using `[hprod]`. Establish `hrzu : IsUnit rz` using `isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by`. Rewrite using `[← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩`.

Conclude with `(hN.pow _).mul (hrzu.pow _)`. Conclude with `isUnit_of_mul_isUnit_left this`. Establish `hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra)`. Rewrite using `[Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen, minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]`. Take `⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra)` from `((isUnit_one.neg).pow _).mul hra_unit`.

Rewrite `hmem` using `[hdisc, ← hv, algebraMap_smul]`. Establish `: y = (↑v⁻¹ : R) • ((v : R) • y)` using `by rw [smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[this]`. Conclude with `Subalgebra.smul_mem _ hmem _`.
-/
theorem mem_adjoin_of_pow_eq_one_of_isUnit {R F L : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Field L] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L] [FiniteDimensional F L] [Algebra.IsSeparable F L]
    {z : L} {N : ℕ} (hN : IsUnit (N : R)) (hz : z ^ N = 1) (hadj : Algebra.adjoin F {z} = ⊤)
    {y : L} (hy : IsIntegral R y) : y ∈ Algebra.adjoin R {z} := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hzR : IsIntegral R z := by
    refine ⟨X ^ N - C 1, monic_X_pow_sub_C 1 hN0, ?_⟩
    simp [eval₂_sub, hz]
  have hzF : IsIntegral F z := hzR.tower_top
  let pb := PowerBasis.ofAdjoinEqTop hzF hadj
  have hgen : pb.gen = z := PowerBasis.ofAdjoinEqTop_gen hzF hadj
  have hmem := Algebra.discr_mul_isIntegral_mem_adjoin F (R := R) (B := pb) (hint := by rw [hgen]; exact hzR) (hz := hy)
  rw [hgen] at hmem
  haveI : Module.IsTorsionFree R L := .of_smul_eq_zero fun r x hx => by
    rw [Algebra.smul_def, mul_eq_zero, IsScalarTower.algebraMap_apply R F L,
      map_eq_zero_iff _ (algebraMap F L).injective, IsFractionRing.to_map_eq_zero_iff] at hx
    exact hx
  have hIntAe : ∀ p : R[X], IsIntegral R (aeval z p) := fun p =>
    adjoin_le_integralClosure hzR (aeval_mem_adjoin_singleton R z)
  set m := minpoly R z with hm
  obtain ⟨h, hmh⟩ : m ∣ X ^ N - C 1 :=
    minpoly.isIntegrallyClosed_dvd hzR (by simp [hz])
  have hder : (N : L) * z ^ (N - 1) = aeval z (derivative m) * aeval z h := by
    have := congrArg (fun p => aeval z (derivative p)) hmh
    simp only [derivative_mul, derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_add, map_mul] at this
    have h0 : aeval z m = 0 := minpoly.aeval R z
    simpa [h0] using this
  have hint : ∀ x : L, IsIntegral R x → ∃ r : R, algebraMap R F r = Algebra.norm F x := fun x hx =>
    IsIntegrallyClosed.isIntegral_iff.1 (Algebra.isIntegral_norm F hx)
  obtain ⟨ra, hra⟩ := hint _ (hIntAe (derivative m))
  obtain ⟨rb, hrb⟩ := hint _ (hIntAe h)
  obtain ⟨rz, hrz⟩ := hint _ hzR
  have hinj := IsFractionRing.injective R F
  have hrzN : rz ^ N = 1 := hinj (by rw [map_pow, hrz, ← map_pow, hz, map_one, map_one])
  have hprod : ra * rb = (N : R) ^ Module.finrank F L * rz ^ (N - 1) := by
    apply hinj
    have hNL : ((N : L)) = algebraMap F L (N : F) := (map_natCast _ _).symm
    rw [map_mul, hra, hrb, ← map_mul, ← hder, map_mul, map_pow (Algebra.norm F), hNL,
      Algebra.norm_algebraMap, map_mul, map_pow, map_pow, hrz, map_natCast]
  have hra_unit : IsUnit ra := by
    have : IsUnit (ra * rb) := by
      rw [hprod]
      have hrzu : IsUnit rz := isUnit_iff_exists_inv.2 ⟨rz ^ (N - 1), by
        rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hN0), hrzN]⟩
      exact (hN.pow _).mul (hrzu.pow _)
    exact isUnit_of_mul_isUnit_left this
  have hdisc : Algebra.discr F pb.basis = algebraMap R F ((-1) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) := by
    rw [Algebra.discr_powerBasis_eq_norm, map_mul, hra, map_pow, map_neg, map_one, hgen,
      minpoly.isIntegrallyClosed_eq_field_fractions' F hzR, derivative_map, aeval_map_algebraMap]
  obtain ⟨v, hv⟩ : IsUnit ((-1 : R) ^ (Module.finrank F L * (Module.finrank F L - 1) / 2) * ra) :=
    ((isUnit_one.neg).pow _).mul hra_unit
  rw [hdisc, ← hv, algebraMap_smul] at hmem
  have : y = (↑v⁻¹ : R) • ((v : R) • y) := by rw [smul_smul, Units.inv_mul, one_smul]
  rw [this]
  exact Subalgebra.smul_mem _ hmem _

end GlobalTheory.UnitLemma.Unr

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

/- English proof (translation)
Introduce `K K' d φ hφ hd z hz hadj y hy`. Use `letI : Algebra K.E K'.E := φ.toAlgebra`. Use `letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra`. Use `haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl`. Use `haveI : FiniteDimensional K.E K'.E := Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)`.

Establish `hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O)`. Rewrite using `[← residue_ne_zero_iff_isUnit, map_natCast]`. Use `haveI := Fintype.ofFinite (ResidueField K.O)`. Establish `hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0`. Rewrite using `[← K.card_res, Nat.card_eq_fintype_card]`.

Conclude with `Nat.cast_card_eq_zero _`. Establish `hq : 1 ≤ K'.q ^ 2`. Rewrite using `[hφ.1, ← pow_mul, mul_comm, pow_mul]`. Apply `Nat.one_le_pow` to reduce the goal to its premises. Rewrite using `[← K.card_res]`.

Conclude with `Nat.card_pos`. Rewrite using `[Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one, zero_sub]`. Conclude with `neg_ne_zero.2 one_ne_zero`. Conclude with `mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy`.
-/
theorem GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by
  intro K K' d φ hφ hd z hz hadj y hy
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K.O K'.E := (φ.comp (algebraMap K.O K.E)).toAlgebra
  haveI : IsScalarTower K.O K.E K'.E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K.E K'.E :=
    Module.finite_of_finrank_pos (by rw [hφ.2.2.2.2]; exact Nat.pos_of_ne_zero hd)
  have hN : IsUnit (((K'.q ^ 2 - 1 : ℕ)) : K.O) := by
    rw [← residue_ne_zero_iff_isUnit, map_natCast]
    haveI := Fintype.ofFinite (ResidueField K.O)
    have hcard : ((K.q ^ 2 : ℕ) : ResidueField K.O) = 0 := by
      rw [← K.card_res, Nat.card_eq_fintype_card]; exact Nat.cast_card_eq_zero _
    have hq : 1 ≤ K'.q ^ 2 := by
      rw [hφ.1, ← pow_mul, mul_comm, pow_mul]
      apply Nat.one_le_pow
      rw [← K.card_res]; exact Nat.card_pos
    rw [Nat.cast_sub hq, hφ.1, ← pow_mul, mul_comm, pow_mul, Nat.cast_pow, hcard, zero_pow hd, Nat.cast_one,
      zero_sub]
    exact neg_ne_zero.2 one_ne_zero
  exact mem_adjoin_of_pow_eq_one_of_isUnit hN hz.pow_eq_one hadj hy
