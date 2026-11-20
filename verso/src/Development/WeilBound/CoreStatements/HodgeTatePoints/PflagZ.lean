import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSymmetricSpanHsymm
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinear
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.CycleListPermInvariant
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumProductExpansion
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GenNumLinearSubst
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HsymmDualRootsTrivNumZero
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HasExpansionOfMemSpan

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace PositivityTheory.HtPt.Pflag

def idxList {N : ℕ} (α : Fin N → ℕ) : List (Fin N) :=
  (List.finRange N).flatMap fun i => List.replicate (α i) i

/- English proof (translation)
Simplify using `only [idxList, List.count_flatMap]`. Rewrite using `[← List.ofFn_eq_map, List.sum_ofFn]`. Simplify using `[List.count_replicate]`.
-/
theorem count_idxList {N : ℕ} (α : Fin N → ℕ) (j : Fin N) : (idxList α).count j = α j := by
  classical
  simp only [idxList, List.count_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp [List.count_replicate]

/- English proof (translation)
Simplify using `only [idxList, List.length_flatMap]`. Rewrite using `[← List.ofFn_eq_map, List.sum_ofFn]`. Simplify using the standard rewrite rules.
-/
theorem length_idxList {N : ℕ} (α : Fin N → ℕ) : (idxList α).length = ∑ i, α i := by
  simp only [idxList, List.length_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn]
  simp

/- English proof (translation)
Simplify using `[idxList, rootList, List.map_flatMap, List.map_replicate]`.
-/
theorem map_idxList {K : Type} {N : ℕ} (x : Fin N → K → ℤ) (α : Fin N → ℕ) :
    (idxList α).map x = rootList x α := by
  simp [idxList, rootList, List.map_flatMap, List.map_replicate]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add, Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]`.
-/
theorem prod_map_X {σ : Type} [DecidableEq σ] (s : Multiset σ) :
    ((s.map X).prod : MvPolynomial σ ℝ) = monomial (Multiset.toFinsupp s) 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, ih, ← Multiset.singleton_add, map_add,
      Multiset.toFinsupp_singleton, X, monomial_mul, one_mul]

/- English proof (translation)
Establish `h` using `hH (mem_support_iff.mp hμ)`. Simplify using `only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]`. Rewrite using `[← h]`. Simplify using `[Finsupp.weight_apply, Finsupp.sum]`.
-/
theorem length_classList_of_hom {K σ : Type} (cls : σ → K → ℤ) {H : MvPolynomial σ ℝ} {m : ℕ}
    (hH : H.IsHomogeneous m) {μ : σ →₀ ℕ} (hμ : μ ∈ H.support) : (classList cls μ).length = m := by
  classical
  have h := hH (mem_support_iff.mp hμ)
  simp only [classList, Multiset.length_toList, Multiset.card_map, Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

/- English proof (translation)
Apply `IsHomogeneous.sum` to reduce the goal to its premises. Introduce `s _`. Rewrite using `[prod_map_X]`. Apply `isHomogeneous_monomial` to reduce the goal to its premises. Establish `h` using `Finsupp.card_toMultiset (Multiset.toFinsupp (s : Multiset (Fin N)))`.

Rewrite `h` using `[Multiset.toFinsupp_toMultiset]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem isHomogeneous_hsymm_real (N a : ℕ) : (hsymm (Fin N) ℝ a).IsHomogeneous a := by
  classical
  apply IsHomogeneous.sum
  intro s _
  rw [prod_map_X]
  apply isHomogeneous_monomial
  have h := Finsupp.card_toMultiset (Multiset.toFinsupp (s : Multiset (Fin N)))
  rw [Multiset.toFinsupp_toMultiset] at h
  calc Finsupp.degree (Multiset.toFinsupp (s : Multiset (Fin N)))
      = (Multiset.toFinsupp (s : Multiset (Fin N))).sum fun _ => id := rfl
    _ = a := by rw [← h]; simp

section
variable (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
  [∀ k, Fintype (ι k)] (V : Ideal (MRing ι F))

/- English proof (translation)
Rewrite using `[hsymm, (genNum_linear F K ι (Fin N) V x Q).2.2.1]`. Repeatedly rewrite using `[prod_map_X, (genNum_linear F K ι (Fin N) V x Q).2.2.2, one_mul]`. Use `push_cast`. Use `symm`. Use `Finset.sum_bij' (fun α hα => (⟨(idxList α : Multiset (Fin N)), by` and prove the remaining obligations.

Rewrite using `[Multiset.coe_card, length_idxList, (Finset.Nat.mem_antidiagonalTuple.mp hα)]⟩ : Sym (Fin N) a))`. Use the proof step `(fun s _ => fun i => (s : Multiset (Fin N)).count i) ?_ ?_ ?_ ?_ ?_`. Introduce `α _`. Conclude with `Finset.mem_univ _`. Introduce `s _`.

Rewrite using `[Finset.Nat.mem_antidiagonalTuple]`. Rewrite using `[← Finset.sum_subset (Finset.subset_univ (s : Multiset (Fin N)).toFinset)]`. Rewrite using `[Multiset.toFinset_sum_count_eq]`. Conclude with `s.2`. Introduce `i _ hi`.

Simplify using `using hi`. Introduce `α _`. Use function extensionality and compare the values at `i`. Simplify using `[Multiset.coe_count, count_idxList]`. Introduce `s _`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `[Multiset.coe_count, count_idxList]`. Introduce `α _`. Rewrite using `[intNumL_perm_of_perm F K ι V (rootList x α ++ Q) _]`.

Apply `List.Perm.append_right` to reduce the goal to its premises. Rewrite using `[← map_idxList]`. Rewrite using `[← Multiset.coe_eq_coe]`. Simplify using `[classList, Multiset.toFinsupp_toMultiset]`.
-/
theorem genNum_hsymm {N : ℕ} (x : Fin N → K → ℤ) (a : ℕ) (Q : List (K → ℤ)) :
    genNum F V x (hsymm (Fin N) ℝ a) Q =
      ((∑ α ∈ Finset.Nat.antidiagonalTuple N a, intNumL F V (rootList x α ++ Q) : ℤ) : ℝ) := by
  classical
  rw [hsymm, (genNum_linear F K ι (Fin N) V x Q).2.2.1]
  simp_rw [prod_map_X, (genNum_linear F K ι (Fin N) V x Q).2.2.2, one_mul]
  push_cast
  symm
  refine Finset.sum_bij'
    (fun α hα => (⟨(idxList α : Multiset (Fin N)), by
      rw [Multiset.coe_card, length_idxList, (Finset.Nat.mem_antidiagonalTuple.mp hα)]⟩ : Sym (Fin N) a))
    (fun s _ => fun i => (s : Multiset (Fin N)).count i) ?_ ?_ ?_ ?_ ?_
  · intro α _
    exact Finset.mem_univ _
  · intro s _
    rw [Finset.Nat.mem_antidiagonalTuple]
    rw [← Finset.sum_subset (Finset.subset_univ (s : Multiset (Fin N)).toFinset)]
    · rw [Multiset.toFinset_sum_count_eq]
      exact s.2
    · intro i _ hi
      simpa using hi
  · intro α _
    funext i
    simp [Multiset.coe_count, count_idxList]
  · intro s _
    apply Subtype.ext
    ext i
    simp [Multiset.coe_count, count_idxList]
  · intro α _
    rw [intNumL_perm_of_perm F K ι V (rootList x α ++ Q) _]
    apply List.Perm.append_right
    rw [← map_idxList]
    rw [← Multiset.coe_eq_coe]
    simp [classList, Multiset.toFinsupp_toMultiset]

/- English proof (translation)
Establish `h` using `genNum_linear_subst F K ι V d hV hd (Fin N) (Fin N) b (fun t i => if t = i then -1 else 0) H m hH Q hQ`. Establish `e1 : (fun t : Fin N => ∑ i : Fin N, (if t = i then (-1 : ℤ) else 0) • b i) = fun t => -b t`. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules. Establish `e2 : (fun t : Fin N => ∑ i : Fin N, C (((if t = i then (-1 : ℤ) else 0 : ℤ) : ℝ)) * (X i : MvPolynomial (Fin N) ℝ)) = fun t => (-X t : MvPolynomial (Fin N) ℝ)`.

Use function extensionality and compare the values at `t`. Simplify using `only [apply_ite (fun z : ℤ => ((z : ℝ))), Int.cast_neg, Int.cast_one, Int.cast_zero, apply_ite C, map_neg, map_one, map_zero, ite_mul, neg_mul, one_mul, zero_mul]`. Rewrite using `[Finset.sum_ite_eq Finset.univ t (fun i => -(X i : MvPolynomial (Fin N) ℝ))]`. Simplify using the standard rewrite rules. Rewrite `h` using `[e1, e2]`.

Conclude with `h.symm`.
-/
theorem genNum_neg (d : ℕ) (hV : IsMultiProjPrime V)
    (hd : ringKrullDim (MRing ι F ⧸ V) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) {N : ℕ}
    (b : Fin N → K → ℤ) (H : MvPolynomial (Fin N) ℝ) (m : ℕ) (hH : H.IsHomogeneous m)
    (Q : List (K → ℤ)) (hQ : m + Q.length = d) :
    genNum F V b (aeval (fun i => (-X i : MvPolynomial (Fin N) ℝ)) H) Q =
      genNum F V (fun i => -b i) H Q := by
  classical
  have h := genNum_linear_subst F K ι V d hV hd (Fin N) (Fin N) b
    (fun t i => if t = i then -1 else 0) H m hH Q hQ
  have e1 : (fun t : Fin N => ∑ i : Fin N, (if t = i then (-1 : ℤ) else 0) • b i) =
      fun t => -b t := by
    funext t
    simp
  have e2 : (fun t : Fin N => ∑ i : Fin N,
      C (((if t = i then (-1 : ℤ) else 0 : ℤ) : ℝ)) * (X i : MvPolynomial (Fin N) ℝ)) =
      fun t => (-X t : MvPolynomial (Fin N) ℝ) := by
    funext t
    simp only [apply_ite (fun z : ℤ => ((z : ℝ))), Int.cast_neg, Int.cast_one, Int.cast_zero,
      apply_ite C, map_neg, map_one, map_zero, ite_mul, neg_mul, one_mul, zero_mul]
    rw [Finset.sum_ite_eq Finset.univ t (fun i => -(X i : MvPolynomial (Fin N) ℝ))]
    simp
  rw [e1, e2] at h
  exact h.symm

end

end PositivityTheory.HtPt.Pflag
