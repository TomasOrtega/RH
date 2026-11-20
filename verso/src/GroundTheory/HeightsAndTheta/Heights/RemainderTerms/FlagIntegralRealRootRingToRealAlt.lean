import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsPowerSumDecompositionHomogeneousComponent
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.FlagIntegralRealEqMulDdConst
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace TermBoundEq

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities.
-/
theorem flagIntegralReal_rootRingToReal (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h P) = (flagIntegral f N P : ℝ) := by
  subst h
  have hid : (Prod.map id (finCongr (rfl : j + k = j + k)) : Fin f × Fin (j + k) → _) = id :=
    funext fun _ => rfl
  have : rootRingToReal f (j + k) j k rfl P = map (algebraMap ℚ ℝ) P := by
    simp only [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hid,
      rename_id_apply]
  rw [this, flagIntegralReal_map]

def coeffMap {σ : Type*} (φ : Module.Dual ℚ ℝ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ d ∈ P.support, monomial d (φ (coeff d P))

variable {σ : Type*} (φ : Module.Dual ℚ ℝ)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem coeff_coeffMap (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    coeff d (coeffMap φ P) = φ (coeff d P) := by
  classical
  rw [coeffMap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [notMem_support_iff.1 hd, map_zero]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem coeffMap_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    coeffMap φ (∑ i ∈ s, P i) = ∑ i ∈ s, coeffMap φ (P i) := by
  ext d
  simp only [coeff_coeffMap, coeff_sum, map_sum]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_map_mul (R : MvPolynomial σ ℚ) (P : MvPolynomial σ ℝ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R * P) = R * coeffMap φ P := by
  classical
  ext d
  rw [coeff_coeffMap, coeff_mul, coeff_mul, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_coeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

/- English proof (translation)
By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.
-/
theorem coeffMap_map (R : MvPolynomial σ ℚ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R) = φ 1 • R := by
  ext d
  rw [coeff_coeffMap, coeff_map, coeff_smul, smul_eq_mul, ← mul_one (algebraMap ℚ ℝ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem dual_flagIntegralReal (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    φ (flagIntegralReal f N P) = flagIntegral f N (coeffMap φ P) := by
  have hterm : ∀ α : Fin f × Fin N →₀ ℕ,
      coeff α P * ((coeff α (blockVandermonde f N) : ℚ) : ℝ) *
          α.prod (fun _ e => (e.factorial : ℝ)) =
        (coeff α (blockVandermonde f N) * α.prod (fun _ e => (e.factorial : ℚ))) • coeff α P := by
    intro α
    rw [Rat.smul_def]
    simp only [Finsupp.prod, Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast]
    ring
  show φ (∑ α ∈ _, _) = _
  simp only [hterm, map_sum, map_smul, smul_eq_mul, flagIntegral, coeff_coeffMap]
  exact sum_congr rfl fun α _ => by ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem flagIntegral_sub_smul (f N : ℕ) (A B : RootRing f N) (s : ℚ) :
    flagIntegral f N (A - s • B) = flagIntegral f N A - s * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [coeff_sub, coeff_smul, smul_eq_mul]
  ring

end TermBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
