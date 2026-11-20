import Formalism.GradedWeylDivisibility.StatementD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LDrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActMul

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `R K _ _ _ k n ν g hg F hF`. Unfold `nablaL at hF`. Rewrite `hF` using `[Submodule.mem_comap, Submodule.mem_map]`. Take `⟨G, hG, hGF⟩` from `hF`. Establish `hGF' : map (algebraMap R K) G = rowAct K g F` using `hGF`.

Establish `hGK : map (algebraMap R K) G ∈ dualWeyl K k n ν`. Unfold `dualWeyl at hG ⊢`. Rewrite `hG`, the goal using `[Submodule.mem_inf]`. Take `⟨hG1, hG2⟩` from `hG`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite `hG1`, the goal using `[mem_weightedHomogeneousSubmodule]`. Introduce `d hd`. Apply `hG1` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises.

Rewrite using `[coeff_map, h0, map_zero]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hG2 ⊢`. Introduce `l j hlj`. Establish `e` using `hG2 l j hlj`. Establish `hc : ∀ p : MvPolynomial (Fin k × Fin n) R, colAddGen K l j (map (algebraMap R K) p) = map (algebraMap R K) (colAddGen R l j p)`.

Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on`. Name the introduced variables `a`. Simplify using `[colAddGen]`. Name the introduced variables `p q hp hq`.

Simplify using `only [map_add, hp, hq]`. Name the introduced variables `p v hp`. Simplify using `only [map_mul, hp]`. Use `congr 1`. Simplify using `only [colAddGen, map_X, aeval_X]`.

Apply the tactic sequence `split_ifs <;> simp`. Simplify using `only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢`. Rewrite using `[hc, ← map_rename, ← map_sub, e, map_zero]`. Establish `hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K), P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν`. Introduce `A P hP`.

Unfold `dualWeyl at hP ⊢`. Rewrite `hP`, the goal using `[Submodule.mem_inf]`. Take `⟨hP1, hP2⟩` from `hP`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite `hP1`, the goal using `[mem_weightedHomogeneousSubmodule]`.

Establish `hXw : ∀ v : Fin k × Fin n, IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v)`. Introduce `v`. Simplify using `only [rowAct, aeval_X]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `b _`.

Establish `h` using `(isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul (isWeightedHomogeneous_X K (colW k n) (b, v.2))`. Simplify `h` using `[colW]`. Rewrite using `[P.as_sum, map_sum]`. Apply `IsWeightedHomogeneous.sum` to reduce the goal to its premises. Introduce `d hd`.

Rewrite using `[← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]`. Simplify using `only [map_pow]`. Establish `hC : rowAct K A (C (coeff d P) : MvPolynomial (Fin k × Fin n) K) = C (coeff d P)`. Simplify using `[rowAct]`. Rewrite using `[hC]`.

Establish `h` using `(isWeightedHomogeneous_C (colW k n) (coeff d P)).mul (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))`. Simplify `h` using `[Finsupp.prod, Finsupp.sum]`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢`. Introduce `l j hlj`. Establish `e` using `hP2 l j hlj`.

Simplify using `only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢`. Set `A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K` to `aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))`. Establish `h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r` using `k) l j) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`.

Distinguish the cases in `hv : v.2 = j`. Simplify using `[A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add, mul_left_comm]`. Simplify using `[A', colAddGen, rowAct, hv]`. Establish `h2 : (rename (R` using `K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) = A'.comp (rename some) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `v`. Simplify using `[A', rowAct]`. Establish `e1` using `congrArg (fun Φ => Φ P) h1`. Establish `e2` using `congrArg (fun Φ => Φ P) h2`. Simplify using `only [AlgHom.comp_apply] at e1 e2`.

Rewrite using `[e1, e2, ← map_sub, e, map_zero]`. Establish `hid : rowAct K (1 : Matrix (Fin k) (Fin k) K) F = F`. Establish `e1 : rowAct K (n` using `n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`.

Simplify using `only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single v.1]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`.

Simplify using the standard rewrite rules. Rewrite using `[e1]`. Both sides reduce to the same expression. Establish `e` using `congrArg (fun Φ => Φ F) (row_action_mul K k n g⁻¹ g)`. Simplify using `only [AlgHom.comp_apply] at e`.

Rewrite `e` using `[Matrix.mul_nonsing_inv g hg, hid]`. Rewrite using `[← e, ← hGF']`. Conclude with `hinv _ _ hGK`.
-/
theorem nabla_weight_le : NablaLLe := by
  intro R K _ _ _ k n ν g hg F hF
  unfold nablaL at hF
  rw [Submodule.mem_comap, Submodule.mem_map] at hF
  obtain ⟨G, hG, hGF⟩ := hF
  have hGF' : map (algebraMap R K) G = rowAct K g F := hGF

  have hGK : map (algebraMap R K) G ∈ dualWeyl K k n ν := by
    unfold dualWeyl at hG ⊢
    rw [Submodule.mem_inf] at hG ⊢
    obtain ⟨hG1, hG2⟩ := hG
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hG1 ⊢
      intro d hd
      apply hG1
      intro h0
      apply hd
      rw [coeff_map, h0, map_zero]
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hG2 ⊢
      intro l j hlj
      have e := hG2 l j hlj
      have hc : ∀ p : MvPolynomial (Fin k × Fin n) R,
          colAddGen K l j (map (algebraMap R K) p) = map (algebraMap R K) (colAddGen R l j p) := by
        intro p
        induction p using MvPolynomial.induction_on
        · rename_i a
          simp [colAddGen]
        · rename_i p q hp hq
          simp only [map_add, hp, hq]
        · rename_i p v hp
          simp only [map_mul, hp]
          congr 1
          simp only [colAddGen, map_X, aeval_X]
          split_ifs <;> simp
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      rw [hc, ← map_rename, ← map_sub, e, map_zero]

  have hinv : ∀ (A : Matrix (Fin k) (Fin k) K) (P : MvPolynomial (Fin k × Fin n) K),
      P ∈ dualWeyl K k n ν → rowAct K A P ∈ dualWeyl K k n ν := by
    intro A P hP
    unfold dualWeyl at hP ⊢
    rw [Submodule.mem_inf] at hP ⊢
    obtain ⟨hP1, hP2⟩ := hP
    refine ⟨?_, ?_⟩
    · rw [mem_weightedHomogeneousSubmodule] at hP1 ⊢
      have hXw : ∀ v : Fin k × Fin n,
          IsWeightedHomogeneous (colW k n) (rowAct K A (X v)) (colW k n v) := by
        intro v
        simp only [rowAct, aeval_X]
        apply IsWeightedHomogeneous.sum
        intro b _
        have h := (isWeightedHomogeneous_C (colW k n) (A v.1 b)).mul
          (isWeightedHomogeneous_X K (colW k n) (b, v.2))
        simpa [colW] using h
      rw [P.as_sum, map_sum]
      apply IsWeightedHomogeneous.sum
      intro d hd
      rw [← hP1 (mem_support_iff.mp hd), monomial_eq, map_mul, map_finsuppProd, Finsupp.weight_apply]
      simp only [map_pow]
      have hC : rowAct K A (C (coeff d P) : MvPolynomial (Fin k × Fin n) K) = C (coeff d P) := by
        simp [rowAct]
      rw [hC]
      have h := (isWeightedHomogeneous_C (colW k n) (coeff d P)).mul
        (IsWeightedHomogeneous.prod d.support _ _ fun v _ => (hXw v).pow (d v))
      simpa [Finsupp.prod, Finsupp.sum] using h
    · simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hP2 ⊢
      intro l j hlj
      have e := hP2 l j hlj
      simp only [LinearMap.sub_apply, AlgHom.toLinearMap_apply] at e ⊢
      let A' : MvPolynomial (Option (Fin k × Fin n)) K →ₐ[K] MvPolynomial (Option (Fin k × Fin n)) K :=
        aeval fun o => o.elim (X none) (fun v => ∑ b : Fin k, C (A v.1 b) * X (some (b, v.2)))
      have h1 : (colAddGen K l j).comp (rowAct K A) = A'.comp (colAddGen K (r := k) l j) := by
        apply MvPolynomial.algHom_ext
        intro v
        by_cases hv : v.2 = j
        · simp [A', colAddGen, rowAct, hv, Finset.mul_sum, Finset.sum_add_distrib, mul_add,
            mul_left_comm]
        · simp [A', colAddGen, rowAct, hv]
      have h2 : (rename (R := K) (some : Fin k × Fin n → Option (Fin k × Fin n))).comp (rowAct K A) =
          A'.comp (rename some) := by
        apply MvPolynomial.algHom_ext
        intro v
        simp [A', rowAct]
      have e1 := congrArg (fun Φ => Φ P) h1
      have e2 := congrArg (fun Φ => Φ P) h2
      simp only [AlgHom.comp_apply] at e1 e2
      rw [e1, e2, ← map_sub, e, map_zero]
  have hid : rowAct K (1 : Matrix (Fin k) (Fin k) K) F = F := by
    have e1 : rowAct K (n := n) (1 : Matrix (Fin k) (Fin k) K) = AlgHom.id K _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [rowAct, aeval_X, AlgHom.coe_id, id_eq, Matrix.one_apply]
      rw [Finset.sum_eq_single v.1]
      · simp
      · intro c _ hc
        simp [Ne.symm hc]
      · simp
    rw [e1]
    rfl
  have e := congrArg (fun Φ => Φ F) (row_action_mul K k n g⁻¹ g)
  simp only [AlgHom.comp_apply] at e
  rw [Matrix.mul_nonsing_inv g hg, hid] at e
  rw [← e, ← hGF']
  exact hinv _ _ hGK

end Formalism.GradedWeylDivisibility
