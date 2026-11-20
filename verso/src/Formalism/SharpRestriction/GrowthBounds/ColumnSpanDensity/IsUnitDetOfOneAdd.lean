import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatticeCountPrimeMonoLevel

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

/- English proof (translation)
Unfold `vLEO at h`. Take `⟨q, hq, hqD⟩` from `h`. Unfold `vO vK ordW at hq`. Establish `hx0 : algebraMap O (KK O) z ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz`. Rewrite `hq` using `[if_neg hx0]`.

Simplify using `only at hq`. Establish `hspec` using `Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))`. Generalize the expression as in `Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab at hq hspec`. Establish `h1 : ab.1 = z * (ab.2 : O)`. Apply `IsFractionRing.injective O (KK O)` to reduce the goal to its premises.

Rewrite using `[map_mul]`. Conclude with `hspec.symm`. Establish `hs0 : (ab.2 : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero ab.2`. Establish `hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis.

Establish `hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Establish `hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤`. Rewrite using `[Ne, IsDiscreteValuationRing.addVal_eq_top_iff]` and apply the resulting hypothesis. Rewrite `hq` using `[h1, AddValuation.map_mul, ENat.toNat_add hzt hst]`.

Simplify using `only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq`. Establish `he1 : 1 ≤ ramE p O`. Unfold `ramE`. Assume the negation of the conclusion as `hlt`. Establish `h0 : (IsDiscreteValuationRing.addVal O (p : O)).toNat = 0` using `by omega`.

Establish `h0' : IsDiscreteValuationRing.addVal O (p : O) = 0`. Break down `ENat.toNat_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hpt`. Apply `hpm` to reduce the goal to its premises.

Apply `isUnit_of_dvd_one` to reduce the goal to its premises. Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, h0']`. Conclude with `zero_le`. Establish `hepos : (0 : ℝ) < (ramE p O : ℝ)` using `by exact_mod_cast he1`. Establish `hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) ≤ (D : ℝ) * (ramE p O : ℝ)`.

Rewrite `hqD` using `[← hq]`. Move the coercions through the operations in `at hqD`. Rewrite `hqD` using `[div_le_iff₀ hepos]`. Then use the resulting hypothesis. Establish `hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ D * ramE p O` using `by exact_mod_cast hreal`. Unfold `ramE at hnat`.

Rewrite using `[← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, ← ENat.coe_toNat hzt, ← ENat.coe_toNat hpt, nsmul_eq_mul]`. Conclude with `hnat` after adjusting the coercions.
-/
theorem dvd_pow_of_vLEO {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {p : ℕ}
    (hp0 : (p : O) ≠ 0) (hpm : ¬ IsUnit (p : O)) {z : O} (hz : z ≠ 0) {D : ℕ} (h : vLEO p z D) :
    z ∣ (p : O) ^ D := by
  classical
  unfold vLEO at h
  obtain ⟨q, hq, hqD⟩ := h
  unfold vO vK ordW at hq
  have hx0 : algebraMap O (KK O) z ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).mpr hz
  rw [if_neg hx0] at hq
  dsimp only at hq
  have hspec := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z))
  generalize Classical.choose (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (KK O) z)) = ab
    at hq hspec
  have h1 : ab.1 = z * (ab.2 : O) := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul]
    exact hspec.symm
  have hs0 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero ab.2
  have hzt : IsDiscreteValuationRing.addVal O z ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hst : IsDiscreteValuationRing.addVal O (ab.2 : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  have hpt : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  rw [h1, AddValuation.map_mul, ENat.toNat_add hzt hst] at hq
  simp only [Nat.cast_add, add_sub_cancel_right, WithTop.map_coe, WithTop.coe_inj] at hq
  have he1 : 1 ≤ ramE p O := by
    unfold ramE
    by_contra hlt
    have h0 : (IsDiscreteValuationRing.addVal O (p : O)).toNat = 0 := by omega
    have h0' : IsDiscreteValuationRing.addVal O (p : O) = 0 := by
      rcases ENat.toNat_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hpt
    apply hpm
    apply isUnit_of_dvd_one
    rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, h0']
    exact zero_le
  have hepos : (0 : ℝ) < (ramE p O : ℝ) := by exact_mod_cast he1
  have hreal : ((IsDiscreteValuationRing.addVal O z).toNat : ℝ) ≤ (D : ℝ) * (ramE p O : ℝ) := by
    rw [← hq] at hqD
    push_cast at hqD
    rwa [div_le_iff₀ hepos] at hqD
  have hnat : (IsDiscreteValuationRing.addVal O z).toNat ≤ D * ramE p O := by exact_mod_cast hreal
  unfold ramE at hnat
  rw [← IsDiscreteValuationRing.addVal_le_iff_dvd, AddValuation.map_pow, ← ENat.coe_toNat hzt,
    ← ENat.coe_toNat hpt, nsmul_eq_mul]
  exact_mod_cast hnat

/- English proof (translation)
Establish `hmap : P.map (IsLocalRing.residue O) = 1`. Use extensionality with `i l`. Establish `h2 : IsLocalRing.residue O (P i l) = IsLocalRing.residue O ((1 : Matrix (Fin M) (Fin M) O) i l)`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]`. Conclude with `h i l`.

Rewrite using `[Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap, Matrix.det_one]`. Conclude with `one_ne_zero`.
-/
theorem isUnit_det_of_one_add {O : Type*} [CommRing O] [IsLocalRing O] {M : ℕ} (P : Matrix (Fin M) (Fin M) O)
    (h : ∀ i l, P i l - (1 : Matrix (Fin M) (Fin M) O) i l ∈ IsLocalRing.maximalIdeal O) : IsUnit P.det := by
  have hmap : P.map (IsLocalRing.residue O) = 1 := by
    ext i l
    have h2 : IsLocalRing.residue O (P i l) =
        IsLocalRing.residue O ((1 : Matrix (Fin M) (Fin M) O) i l) := by
      rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact h i l
    rw [Matrix.map_apply, h2, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det, RingHom.mapMatrix_apply, hmap,
    Matrix.det_one]
  exact one_ne_zero

/- English proof (translation)
Establish `hsum : ∀ i (G : Fin M → X), φ i (∑ l, G l) = ∑ l, φ i (G l)` using `fun i G => map_sum (AddMonoidHom.mk' (φ i) (hadd i)) G Finset.univ`. Set `v : (Fin M → O) →ₗ[O] X` to `{ toFun := fun x => ∑ l, (zc' l * x l) • Y l map_add' := by`. Introduce `x y`. Simplify using `only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]`. Use the proof step `map_smul' := by`.

Introduce `c x`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]`. Use `congr 1`.

Use `ring }`. Establish `hv : ∀ x, v x ∈ A` using `fun x => by show (∑ l, (zc' l * x l) • Y l) ∈ A`. Conclude with `A.sum_mem fun l _ => A.smul_mem _ (hY l)`. Establish `key : ∀ x i, φ i (v x) = algebraMap O Kf (π ^ D * (P.mulVec x) i)`. Introduce `x i`.

Use `show φ i (∑ l, (zc' l * x l) • Y l) = _`. Rewrite using `[hsum]`. Simplify using `only [hsmul, hφ]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.mul_sum, map_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← map_mul]`. Use `congr 1`. Rewrite using `[← hz l]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨LinearMap.codRestrict A v hv, P⁻¹, fun x j => ?_⟩` and prove the remaining obligations. Establish `hx : x j = ∑ i, P⁻¹ j i * (P.mulVec x) i`. Establish `h2 : P⁻¹.mulVec (P.mulVec x) = x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]`. Use `conv_lhs => rw [← h2]`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[hx, Finset.mul_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.codRestrict_apply, key x i, ← map_mul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem goodRank_core {O Kf X : Type*} [CommRing O] [Field Kf] [Algebra O Kf] [AddCommGroup X] [Module O X]
    (π : O) (A : Submodule O X) {M : ℕ} (φ : Fin M → X → Kf) (D : ℕ)
    (hadd : ∀ i G G', φ i (G + G') = φ i G + φ i G') (hsmul : ∀ i (c : O) G, φ i (c • G) = algebraMap O Kf c * φ i G)
    (Y : Fin M → X) (hY : ∀ l, Y l ∈ A) (P : Matrix (Fin M) (Fin M) O) (zc zc' : Fin M → O)
    (hz : ∀ l, zc' l * zc l = π ^ D) (hφ : ∀ i l, φ i (Y l) = algebraMap O Kf (P i l * zc l))
    (hP : IsUnit P.det) : GoodRankK π A φ M D := by
  classical
  have hsum : ∀ i (G : Fin M → X), φ i (∑ l, G l) = ∑ l, φ i (G l) := fun i G =>
    map_sum (AddMonoidHom.mk' (φ i) (hadd i)) G Finset.univ
  let v : (Fin M → O) →ₗ[O] X :=
    { toFun := fun x => ∑ l, (zc' l * x l) • Y l
      map_add' := by
        intro x y
        simp only [Pi.add_apply, mul_add, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_smul]
        congr 1
        ring }
  have hv : ∀ x, v x ∈ A := fun x => by
    show (∑ l, (zc' l * x l) • Y l) ∈ A
    exact A.sum_mem fun l _ => A.smul_mem _ (hY l)
  have key : ∀ x i, φ i (v x) = algebraMap O Kf (π ^ D * (P.mulVec x) i) := by
    intro x i
    show φ i (∑ l, (zc' l * x l) • Y l) = _
    rw [hsum]
    simp only [hsmul, hφ]
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← map_mul]
    congr 1
    rw [← hz l]
    ring
  refine ⟨LinearMap.codRestrict A v hv, P⁻¹, fun x j => ?_⟩
  have hx : x j = ∑ i, P⁻¹ j i * (P.mulVec x) i := by
    have h2 : P⁻¹.mulVec (P.mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hP, Matrix.one_mulVec]
    conv_lhs => rw [← h2]
    simp only [Matrix.mulVec, dotProduct]
  rw [hx, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.codRestrict_apply, key x i, ← map_mul]
  congr 1
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
