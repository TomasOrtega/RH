import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalIdempotentsAdeleUnitCombinationStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

/- English proof (translation)
Simplify using `[nrm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nrm_smul_eq_sq_mul {R : Type*} [CommRing R] {a b : R} (t : R) (x : ℍ[R, a, b]) :
    nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

/- English proof (translation)
Establish `key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i)`. Introduce `i`. Establish `hs : η i • (∑ j, η j • y j) = η i • y i`. Rewrite using `[Finset.smul_sum, Finset.sum_eq_single i]`. Rewrite using `[smul_smul, h1]`.

Introduce `j _ hj`. Rewrite using `[smul_smul, h2 i j (Ne.symm hj), zero_smul]`. Simplify using the standard rewrite rules. Use `congrArg nrm hs` as an intermediate fact. Rewrite `this` using `[nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1]`. Then use the resulting hypothesis.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_mul, h3, one_mul]`. Use `_ = _ := Finset.sum_congr rfl fun i _ => key i`.
-/
theorem nrm_sum_orthIdem_smul {R : Type*} [CommRing R] {a b : R} {ι : Type} [Fintype ι] (η : ι → R)
    (y : ι → ℍ[R, a, b]) (h1 : ∀ i, η i * η i = η i) (h2 : ∀ i j, i ≠ j → η i * η j = 0)
    (h3 : ∑ i, η i = 1) : nrm (∑ i, η i • y i) = ∑ i, η i * nrm (y i) := by
  classical
  have key : ∀ i, η i * nrm (∑ j, η j • y j) = η i * nrm (y i) := by
    intro i
    have hs : η i • (∑ j, η j • y j) = η i • y i := by
      rw [Finset.smul_sum, Finset.sum_eq_single i]
      · rw [smul_smul, h1]
      · intro j _ hj
        rw [smul_smul, h2 i j (Ne.symm hj), zero_smul]
      · simp
    have := congrArg nrm hs
    rwa [nrm_smul_eq_sq_mul, nrm_smul_eq_sq_mul, sq, h1] at this
  calc nrm (∑ i, η i • y i) = ∑ i, η i * nrm (∑ j, η j • y j) := by
        rw [← Finset.sum_mul, h3, one_mul]
    _ = _ := Finset.sum_congr rfl fun i _ => key i

def quatStdBasis {R : Type*} [CommRing R] (a b : R) : Fin 4 → ℍ[R, a, b] :=
  ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/- English proof (translation)
Establish `h1` using `congrArg QuaternionAlgebra.re hpp`. Establish `h2` using `congrArg QuaternionAlgebra.re hqq`. Simplify using `[QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2`. Simplify using `[Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]`. Take the linear combination `(-4 * a * b) * h1 + (-4 * a * b) * h2`.
-/
theorem nrm_intertwiner_comb {R : Type*} [CommRing R] {a b c : R} (p q : ℍ[R, a, b]) (hp : p.re = 0) (hq : q.re = 0)
    (hpp : p * p = algebraMap R ℍ[R, a, b] c) (hqq : q * q = algebraMap R ℍ[R, a, b] c) :
    ∑ i, (![a * b, -b, -a, 1] : Fin 4 → R) i * nrm (p * quatStdBasis a b i + quatStdBasis a b i * q)
      = -8 * a * b * c := by
  have h1 := congrArg QuaternionAlgebra.re hpp
  have h2 := congrArg QuaternionAlgebra.re hqq
  simp [QuaternionAlgebra.algebraMap_eq, hp, hq] at h1 h2
  simp [Fin.sum_univ_four, quatStdBasis, nrm, hp, hq]
  linear_combination (-4 * a * b) * h1 + (-4 * a * b) * h2

/- English proof (translation)
Introduce `F _ _ a b ha hb c hc p q hp hq hpp hqq`. Establish `hcomb` using `nrm_intertwiner_comb p q hp hq hpp hqq`. Establish `hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c)`. Establish `h : IsUnit (-8 * a * b * c)`. Use `Ne.isUnit ?_` and prove the remaining obligations.

Establish `: (-8 : F) ≠ 0` using `by norm_num`. Conclude with `mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc`. Establish `h'` using `h.map (algebraMap F (AF F))`. Rewrite `h'` using `[map_mul, map_mul, map_mul, map_neg, map_ofNat]`. Then use the resulting hypothesis. Rewrite `hu` using `[← hcomb]`.

Take `⟨η, h1, h2, h3, h4⟩` from `GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu`. Use `⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[nrm_sum_orthIdem_smul η _ h1 h2 h3]`. Conclude with `h4`. Rewrite using `[Finset.sum_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, mul_smul_comm]`. Use `congr 1`. Rewrite using `[add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc, Algebra.commutes]`.
-/
theorem exists_unit_intertwiner : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ c : F, c ≠ 0 → ∀ p q : DA F a b, p.re = 0 → q.re = 0 → p * p = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → q * q = algebraMap (AF F) (DA F a b) (algebraMap F (AF F) c) → ∃ y : DA F a b, IsUnit (nrm y) ∧ y * q = p * y := by
  intro F _ _ a b ha hb c hc p q hp hq hpp hqq
  have hcomb := nrm_intertwiner_comb p q hp hq hpp hqq
  have hu : IsUnit (-8 * algebraMap F (AF F) a * algebraMap F (AF F) b * algebraMap F (AF F) c) := by
    have h : IsUnit (-8 * a * b * c) := by
      refine Ne.isUnit ?_
      have : (-8 : F) ≠ 0 := by norm_num
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero this ha) hb) hc
    have h' := h.map (algebraMap F (AF F))
    rwa [map_mul, map_mul, map_mul, map_neg, map_ofNat] at h'
  rw [← hcomb] at hu
  obtain ⟨η, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_orthogonal_idempotents_adele_unit_combination F (Fin 4) _ _ hu
  refine ⟨∑ i, η i • (p * quatStdBasis _ _ i + quatStdBasis _ _ i * q), ?_, ?_⟩
  · rw [nrm_sum_orthIdem_smul η _ h1 h2 h3]; exact h4
  · rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, mul_smul_comm]
    congr 1
    rw [add_mul, mul_add, mul_assoc _ q q, hqq, ← mul_assoc p p, hpp, add_comm, mul_assoc,
      Algebra.commutes]

end GlobalTheory.QSA
