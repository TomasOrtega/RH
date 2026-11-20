import Mathlib
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonomialParamAsLogSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LowCoefficientsOfParameterCoefficientsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.TwU.LowGen

/- English proof (translation)
Use `le_trans ?_ (MvPowerSeries.le_order_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f)` and prove the remaining obligations. Establish `h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order` using `le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha i)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem le_order_subst' {σ τ K : Type} [Finite σ] [Field K] {a : σ → MvPowerSeries τ K}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ K) :
    f.order ≤ (MvPowerSeries.subst a f).order := by
  refine le_trans ?_ (MvPowerSeries.le_order_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha) f)
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (ha i)
  calc f.order = 1 * f.order := (one_mul _).symm
    _ ≤ _ := by gcongr

/- English proof (translation)
Unfold `applyD`. Use `Finset.sum_eq_zero fun n hn => ?_` and prove the remaining obligations. Establish `h1 : n.degree ≤ P.totalDegree` using `MvPolynomial.le_totalDegree hn`. Establish `h2 : MvPowerSeries.coeff n f = 0`. Apply `MvPowerSeries.coeff_of_lt_order` to reduce the goal to its premises.

Use `lt_of_lt_of_le ?_ h` and prove the remaining obligations. Conclude with `Nat.lt_succ_of_le h1` after adjusting the coercions. Rewrite using `[h2, mul_zero, zero_smul]`.
-/
theorem applyD_eq_zero {σ τ K : Type} [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ K)
    (h : ((P.totalDegree + 1 : ℕ) : ℕ∞) ≤ f.order) : applyD P f = 0 := by
  unfold applyD
  refine Finset.sum_eq_zero fun n hn => ?_
  have h1 : n.degree ≤ P.totalDegree := MvPolynomial.le_totalDegree hn
  have h2 : MvPowerSeries.coeff n f = 0 := by
    apply MvPowerSeries.coeff_of_lt_order
    refine lt_of_lt_of_le ?_ h
    exact_mod_cast Nat.lt_succ_of_le h1
  rw [h2, mul_zero, zero_smul]

noncomputable def applyDL {σ τ : Type} (K : Type) [Field K] (P : MvPolynomial σ (MvPolynomial τ ℤ)) :
    MvPowerSeries σ K →ₗ[K] MvPolynomial τ K where
  toFun := applyD P
  map_add' f g := by
    simp only [applyD, map_add, mul_add, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [applyD, RingHom.id_apply, Finset.smul_sum, smul_smul, MvPowerSeries.coeff_smul]
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    ring

/- English proof (translation)
Unfold `applyD`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C, MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)]`. Simplify using the standard rewrite rules.
-/
theorem applyD_map {σ τ K L : Type} [Field K] [Field L] (φ : K →+* L) (P : MvPolynomial σ (MvPolynomial τ ℤ))
    (f : MvPowerSeries σ K) :
    applyD P (MvPowerSeries.map φ f) = MvPolynomial.map φ (applyD P f) := by
  unfold applyD
  rw [map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul (MvPolynomial.map φ), MvPolynomial.map_C,
    MvPolynomial.map_map, RingHom.ext_int (φ.comp (Int.castRingHom K)) (Int.castRingHom L)]
  simp

variable {p : ℕ} [Fact p.Prime]

/- English proof (translation)
Apply the tactic sequence `rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]`.
-/
theorem constantCoeff_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.constantCoeff (X.coordZA K j s) = 0 := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

/- English proof (translation)
Apply the tactic sequence `rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]`.
-/
theorem map_coordZA (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ) (s : X.EA j ⊕ X.EA j) :
    MvPowerSeries.map (algebraMap (K0 p) K) (X.coordZA (K0 p) j s) = X.coordZA K j s := by
  rcases s with ⟨v, r, a, b⟩ | ⟨v, r, a, b⟩ <;> simp [Sys.coordZA, map_sum]

/- English proof (translation)
Unfold `Sys.ThZA`. Rewrite using `[MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X _ j))]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Conclude with `(map_coordZA X K j s).symm`.
-/
theorem ThZA_map (X : Sys p) (K : Type) [Field K] [Algebra (K0 p) K] (j : ℕ)
    (f : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    X.ThZA K j (MvPowerSeries.map (algebraMap (K0 p) K) f) =
      MvPowerSeries.map (algebraMap (K0 p) K) (X.ThZA (K0 p) j f) := by
  unfold Sys.ThZA
  rw [MvPowerSeries.map_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X _ j))]
  congr 1
  funext s
  exact (map_coordZA X K j s).symm

/- English proof (translation)
Establish `h : (p : WW p) ≠ 0` using `WittVector.p_nonzero p (kb p)`. Establish `h2` using `(map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).mpr h`. Establish `h3` using `(map_ne_zero (algebraMap (K0 p) K)).mpr h2`. Simplify using `using h3`.
-/
theorem p_ne_zero (K : Type) [Field K] [Algebra (K0 p) K] : (p : K) ≠ 0 := by
  have h : (p : WW p) ≠ 0 := WittVector.p_nonzero p (kb p)
  have h2 := (map_ne_zero_iff _ (IsFractionRing.injective (WW p) (K0 p))).mpr h
  have h3 := (map_ne_zero (algebraMap (K0 p) K)).mpr h2
  simpa using h3

/- English proof (translation)
Introduce `a b hb hab`. Establish `hp` using `p_ne_zero (p := p) Y.Kc`. Establish `h1 : a ≤ ⌈g⌉ * b`. Establish `: (a : ℝ) ≤ (⌈g⌉ : ℝ) * b` using `hab.trans (mul_le_mul_of_nonneg_right (Int.le_ceil g) (Nat.cast_nonneg b))`. Conclude with `this` after adjusting the coercions.

Take `⟨k, hk⟩` from `Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h1)`. Establish `: ((p : Y.Kc) ^ ⌈g⌉ * y) ^ b * (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ k * y ^ b`. Rewrite using `[mul_pow, ← zpow_natCast ((p : Y.Kc) ^ ⌈g⌉), ← zpow_mul, mul_right_comm, ← zpow_add₀ hp, ← sub_eq_add_neg, hk, zpow_natCast]`. Rewrite using `[this]`. Conclude with `Y.Oc.mul_mem (Y.Oc.pow_mem (natCast_mem Y.Oc p) _) (Y.Oc.pow_mem hy _)`.
-/
theorem geC_of_mem {X : Sys p} (Y : Pend X) (g : ℝ) (y : Y.Kc) (hy : y ∈ Y.Oc) :
    Y.geC ((p : Y.Kc) ^ ⌈g⌉ * y) g := by
  intro a b hb hab
  have hp := p_ne_zero (p := p) Y.Kc
  have h1 : a ≤ ⌈g⌉ * b := by
    have : (a : ℝ) ≤ (⌈g⌉ : ℝ) * b := hab.trans (mul_le_mul_of_nonneg_right (Int.le_ceil g) (Nat.cast_nonneg b))
    exact_mod_cast this
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.mpr h1)
  have : ((p : Y.Kc) ^ ⌈g⌉ * y) ^ b * (p : Y.Kc) ^ (-a) = (p : Y.Kc) ^ k * y ^ b := by
    rw [mul_pow, ← zpow_natCast ((p : Y.Kc) ^ ⌈g⌉), ← zpow_mul, mul_right_comm, ← zpow_add₀ hp, ← sub_eq_add_neg, hk,
      zpow_natCast]
  rw [this]
  exact Y.Oc.mul_mem (Y.Oc.pow_mem (natCast_mem Y.Oc p) _) (Y.Oc.pow_mem hy _)

/- English proof (translation)
Introduce `p _ X Y j v g _ hL U hU I m`. Use `choose Un hUn using GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero p (X.EA j ⊕ X.EA j)`. Use `set P := X.PIv j I v with hP`. Use `set d := P.totalDegree with hd`. Establish `hfin : {n : (X.EA j ⊕ X.EA j) →₀ ℕ | n.degree ≤ d}.Finite` using `Finsupp.finite_of_degree_le d`.

Use `set S := hfin.toFinset with hS`. Establish `hspan` using `GlobalTheory.T.lowCoefficients_of_parameterCoefficients p (X.EA j ⊕ X.EA j) Y.Kc Un hUn U d S (fun n hn => hfin.mem_toFinset.mpr hn)`. Establish `hint : ∀ n, IntS p (inParam p (Un n))` using `fun n => ⟨MvPowerSeries.monomial n 1, by rw [(hUn n).1, MvPowerSeries.map_monomial, RingHom.map_one]⟩`. Use `choose a ha using fun n => hL (Un n) (hint n) I m`. Establish `hE : Y.PhAt j v = phAt X Y.be j v` using `rfl`.

Rewrite using `[hE]`. Use `set E := expS p (-phAt X Y.be j v) with hEdef`. Use `set φ := algebraMap (K0 p) Y.Kc with hφ`. Use `set c : _ → Y.Kc := fun n => MvPowerSeries.coeff n (inParamK p Y.Kc U) with hc`. Establish `hsub` using `MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X Y.Kc j)`.

Use `set A := U - ∑ n ∈ S, c n • MvPowerSeries.map φ (Un n) with hA`. Establish `hAo : ((d + 1 : ℕ) : ℕ∞) ≤ A.order`. Apply `MvPowerSeries.nat_le_order` to reduce the goal to its premises. Introduce `k hk`. Rewrite using `[hA, map_sub, hspan k (Nat.le_of_lt_succ hk), map_sum, sub_eq_zero]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]`. Establish `hz : applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * A)) = 0`. Apply `applyD_eq_zero` to reduce the goal to its premises. Use `le_trans ?_ (le_order_subst' (constantCoeff_coordZA X Y.Kc j) _)` and prove the remaining obligations.

Conclude with `hAo.trans (le_trans le_add_self MvPowerSeries.le_order_mul)`. Establish `hU' : MvPowerSeries.map φ E * U = MvPowerSeries.map φ E * A + ∑ n ∈ S, c n • MvPowerSeries.map φ (E * Un n)`. Rewrite using `[hA, mul_sub, Finset.mul_sum]`. Simplify using `only [mul_smul_comm, map_mul, sub_add_cancel]`. Establish `hTh : ∀ f, applyD P (X.ThZA Y.Kc j f) = ((applyDL Y.Kc P) ∘ₗ (MvPowerSeries.substAlgHom (R` using `Y.Kc) hsub).toLinearMap) f := by`.

Introduce `f`. Rewrite using `[Sys.ThZA, ← MvPowerSeries.coe_substAlgHom hsub]`. Both sides reduce to the same expression. Establish `hval : MvPolynomial.coeff m (applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * U))) = (p : Y.Kc) ^ ⌈g⌉ * ∑ n ∈ S, c n * φ (algebraMap (WW p) (K0 p) (a n))`. Rewrite using `[hU', hTh, map_add, ← hTh, hz, zero_add, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, ← hTh, hφ, ThZA_map, applyD_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, ha n, map_mul, map_zpow₀, map_natCast, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hval]`. Conclude with `geC_of_mem Y g _ (Y.Oc.sum_mem fun n _ => Y.Oc.mul_mem (hU n) (Y.witt_mem_integers_Cp _))`.
-/
theorem cofactor_lower_bound_of_place_bound_witt : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (Y : Pend X) (j : ℕ) (v : X.Pl) (g : ℝ),
    MvPowerSeries.constantCoeff Y.be = 0 → IsPlaceCofactorValuationLowerBound X Y.be j v g → Y.LowAt j v g := by
  intro p _ X Y j v g _ hL U hU I m
  choose Un hUn using GlobalTheory.T.exists_inParam_eq_monomial_low_coeff_zero p (X.EA j ⊕ X.EA j)
  set P := X.PIv j I v with hP
  set d := P.totalDegree with hd
  have hfin : {n : (X.EA j ⊕ X.EA j) →₀ ℕ | n.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  set S := hfin.toFinset with hS
  have hspan := GlobalTheory.T.lowCoefficients_of_parameterCoefficients p (X.EA j ⊕ X.EA j) Y.Kc Un hUn U d S (fun n hn => hfin.mem_toFinset.mpr hn)
  have hint : ∀ n, IntS p (inParam p (Un n)) := fun n =>
    ⟨MvPowerSeries.monomial n 1, by rw [(hUn n).1, MvPowerSeries.map_monomial, RingHom.map_one]⟩
  choose a ha using fun n => hL (Un n) (hint n) I m
  have hE : Y.PhAt j v = phAt X Y.be j v := rfl
  rw [hE]
  set E := expS p (-phAt X Y.be j v) with hEdef
  set φ := algebraMap (K0 p) Y.Kc with hφ
  set c : _ → Y.Kc := fun n => MvPowerSeries.coeff n (inParamK p Y.Kc U) with hc
  have hsub := MvPowerSeries.hasSubst_of_constantCoeff_zero (constantCoeff_coordZA X Y.Kc j)
  set A := U - ∑ n ∈ S, c n • MvPowerSeries.map φ (Un n) with hA
  have hAo : ((d + 1 : ℕ) : ℕ∞) ≤ A.order := by
    apply MvPowerSeries.nat_le_order
    intro k hk
    rw [hA, map_sub, hspan k (Nat.le_of_lt_succ hk), map_sum, sub_eq_zero]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPowerSeries.coeff_smul, MvPowerSeries.coeff_map]
  have hz : applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * A)) = 0 := by
    apply applyD_eq_zero
    refine le_trans ?_ (le_order_subst' (constantCoeff_coordZA X Y.Kc j) _)
    exact hAo.trans (le_trans le_add_self MvPowerSeries.le_order_mul)
  have hU' : MvPowerSeries.map φ E * U =
      MvPowerSeries.map φ E * A + ∑ n ∈ S, c n • MvPowerSeries.map φ (E * Un n) := by
    rw [hA, mul_sub, Finset.mul_sum]
    simp only [mul_smul_comm, map_mul, sub_add_cancel]
  have hTh : ∀ f, applyD P (X.ThZA Y.Kc j f) =
      ((applyDL Y.Kc P) ∘ₗ (MvPowerSeries.substAlgHom (R := Y.Kc) hsub).toLinearMap) f := by
    intro f
    rw [Sys.ThZA, ← MvPowerSeries.coe_substAlgHom hsub]
    rfl
  have hval : MvPolynomial.coeff m (applyD P (X.ThZA Y.Kc j (MvPowerSeries.map φ E * U))) =
      (p : Y.Kc) ^ ⌈g⌉ * ∑ n ∈ S, c n * φ (algebraMap (WW p) (K0 p) (a n)) := by
    rw [hU', hTh, map_add, ← hTh, hz, zero_add, map_sum, MvPolynomial.coeff_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, ← hTh, hφ, ThZA_map, applyD_map, MvPolynomial.coeff_smul, MvPolynomial.coeff_map, ha n, map_mul,
      map_zpow₀, map_natCast, smul_eq_mul]
    ring
  rw [hval]
  exact geC_of_mem Y g _ (Y.Oc.sum_mem fun n _ => Y.Oc.mul_mem (hU n) (Y.witt_mem_integers_Cp _))

end GlobalTheory.TwU.LowGen
