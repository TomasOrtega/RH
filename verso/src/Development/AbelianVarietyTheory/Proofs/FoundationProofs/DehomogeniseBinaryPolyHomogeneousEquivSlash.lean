import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryMonomialDegreeSubstExpansionStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Simplify using `[deh, mon]`.
-/
theorem dehH_mon (w : ℕ) (i : Fin (w + 1)) : deh (mon ℂ w i) = Polynomial.X ^ (i : ℕ) := by
  simp [deh, mon]

/- English proof (translation)
Simplify using `[deh, slP, Polynomial.smul_eq_C_mul]`.
-/
theorem dehH_slP_mon (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (i : ℕ) :
    deh (slP m (MvPolynomial.X 0 ^ i * MvPolynomial.X 1 ^ (w - i))) =
      (Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
        (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [deh, slP, Polynomial.smul_eq_C_mul]

/- English proof (translation)
Establish `h` using `(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp`. Use `conv_lhs => rw [h]`. Rewrite using `[map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) * Polynomial.X ^ i)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, dehH_mon]`.

Simplify using `[deh]`.
-/
theorem dehH_expand (w : ℕ) (p : MvPolynomial (Fin 2) ℂ) (hp : p.IsHomogeneous w) :
    deh p = ∑ i ∈ Finset.range (w + 1),
      Polynomial.C (MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) * Polynomial.X ^ i := by
  have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
  conv_lhs => rw [h]
  rw [map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (MvPolynomial.coeff
    (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) * Polynomial.X ^ i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, dehH_mon]
  simp [deh]

/- English proof (translation)
Simplify using `[Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, hj]`.
-/
theorem dehH_coeff (w : ℕ) (c : ℕ → ℂ) (j : ℕ) (hj : j < w + 1) :
    (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i).coeff j = c j := by
  simp [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, hj]

end GlobalTheory.KZ.H3

namespace GlobalTheory.KZ.H3

/- English proof (translation)
Rewrite using `[GlobalTheory.HeckeFamilyMatrices.slP, LinearMap.sum_apply]`. Simplify using `only [LinearMap.comp_apply, Polynomial.lcoeff_apply, LinearMap.toSpanSingleton_apply]`. Use `Finset.sum_congr rfl fun i hi => ?_` and prove the remaining obligations. Rewrite using `[dehH_coeff w c i (Finset.mem_range.mp hi), Polynomial.smul_eq_C_mul]`.
-/
theorem dehH_slP_sum (w : ℕ) (m : Matrix (Fin 2) (Fin 2) ℤ) (c : ℕ → ℂ) :
    GlobalTheory.HeckeFamilyMatrices.slP w m (∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) * Polynomial.X ^ i) =
      ∑ i ∈ Finset.range (w + 1), Polynomial.C (c i) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)) := by
  rw [GlobalTheory.HeckeFamilyMatrices.slP, LinearMap.sum_apply]
  simp only [LinearMap.comp_apply, Polynomial.lcoeff_apply,
    LinearMap.toSpanSingleton_apply]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [dehH_coeff w c i (Finset.mem_range.mp hi), Polynomial.smul_eq_C_mul]

/- English proof (translation)
Use extensionality with `j`. Distinguish the cases in `hj : j < w + 1`. Conclude with `dehH_coeff w _ j hj`. Rewrite using `[Polynomial.finset_sum_coeff]`. Rewrite `hq` using `[Polynomial.mem_degreeLT]`.

Establish `h0 : q.coeff j = 0` using `Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hq (by exact_mod_cast not_lt.mp hj))`. Rewrite using `[h0]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul_X_pow]`. Establish `: j ≠ i` using `fun h => hj (h ▸ Finset.mem_range.mp hi)`.

Simplify using `[this]`.
-/
theorem dehH_sum_eq (w : ℕ) (q : Polynomial ℂ) (hq : q ∈ Polynomial.degreeLT ℂ (w + 1)) :
    ∑ i ∈ Finset.range (w + 1), Polynomial.C (q.coeff i) * Polynomial.X ^ i = q := by
  ext j
  by_cases hj : j < w + 1
  · exact dehH_coeff w _ j hj
  · rw [Polynomial.finset_sum_coeff]
    rw [Polynomial.mem_degreeLT] at hq
    have h0 : q.coeff j = 0 := Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hq (by exact_mod_cast not_lt.mp hj))
    rw [h0]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [Polynomial.coeff_C_mul_X_pow]
    have : j ≠ i := fun h => hj (h ▸ Finset.mem_range.mp hi)
    simp [this]

/- English proof (translation)
Introduce `w`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m p hp`. Establish `h` using `(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp`. Rewrite using `[dehH_expand w p hp, dehH_slP_sum]`.

Use `conv_lhs => rw [h]`. Rewrite using `[map_sum, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) * ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i * (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + …`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, MvPolynomial.algHom_C, mon, dehH_slP_mon]`. Simplify using `[deh]`.

Introduce `p hp`. Rewrite using `[dehH_expand w p hp]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.mem_degreeLT]`. Use `lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_` and prove the remaining obligations.

Use `Finset.mem_range.mp hi` as an intermediate fact. Conclude with `this` after adjusting the coercions. Introduce `q hq`. Use `⟨∑ i : Fin (w + 1), MvPolynomial.C (q.coeff i) * mon ℂ w i, ?_, ?_⟩` and prove the remaining obligations. Conclude with `MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ((GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.2.1 i).C_mul _`.

Rewrite using `[map_sum]`. Simplify using `only [map_mul, dehH_mon]`. Simplify using `only [deh, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i)]`. Conclude with `dehH_sum_eq w q hq`.

Introduce `p p' hp hp' he`. Rewrite using `[(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp, (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p' hp']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h1` using `dehH_coeff w (fun i => MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) i i.2`. Establish `h2` using `dehH_coeff w (fun i => MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p') i i.2`.

Rewrite `h1` using `[← dehH_expand w p hp, he, dehH_expand w p' hp', h2]`. Rewrite using `[h1]`.
-/
theorem deh_homog_iso : ∀ w : ℕ, (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) ℂ), p.IsHomogeneous w → deh (slP m p) = GlobalTheory.HeckeFamilyMatrices.slP w m (deh p)) ∧ (∀ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → deh p ∈ Polynomial.degreeLT ℂ (w + 1)) ∧ (∀ q ∈ Polynomial.degreeLT ℂ (w + 1), ∃ p : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w ∧ deh p = q) ∧ (∀ p p' : MvPolynomial (Fin 2) ℂ, p.IsHomogeneous w → p'.IsHomogeneous w → deh p = deh p' → p = p') := by
  intro w
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m p hp
    have h := (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp
    rw [dehH_expand w p hp, dehH_slP_sum]
    conv_lhs => rw [h]
    rw [map_sum, map_sum, ← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (MvPolynomial.coeff
      (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) *
        ((Polynomial.C ((m 0 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 0 1 : ℤ) : ℂ)) ^ i *
          (Polynomial.C ((m 1 0 : ℤ) : ℂ) * Polynomial.X + Polynomial.C ((m 1 1 : ℤ) : ℂ)) ^ (w - i)))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, MvPolynomial.algHom_C, mon, dehH_slP_mon]
    simp [deh]
  · intro p hp
    rw [dehH_expand w p hp]
    refine Submodule.sum_mem _ fun i hi => ?_
    rw [Polynomial.mem_degreeLT]
    refine lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le _ _) ?_
    have := Finset.mem_range.mp hi
    exact_mod_cast this
  · intro q hq
    refine ⟨∑ i : Fin (w + 1), MvPolynomial.C (q.coeff i) * mon ℂ w i, ?_, ?_⟩
    · exact MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ =>
        ((GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.2.1 i).C_mul _
    · rw [map_sum]
      simp only [map_mul, dehH_mon]
      simp only [deh, MvPolynomial.aeval_C, Polynomial.algebraMap_eq]
      rw [Fin.sum_univ_eq_sum_range (fun i => Polynomial.C (q.coeff i) * Polynomial.X ^ i)]
      exact dehH_sum_eq w q hq
  · intro p p' hp hp' he
    rw [(GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p hp, (GlobalTheory.T.binaryMonomialDegree_subst_expansion ℂ w).2.1 p' hp']
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 := dehH_coeff w (fun i => MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p) i i.2
    have h2 := dehH_coeff w (fun i => MvPolynomial.coeff (Finsupp.single 0 i + Finsupp.single 1 (w - i)) p') i i.2
    rw [← dehH_expand w p hp, he, dehH_expand w p' hp', h2] at h1
    rw [h1]

end GlobalTheory.KZ.H3
