import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivationFinsetSumApply

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

/- English proof (translation)
The claim follows from `gl_action_eq_derivation LL S a b F`.
-/
theorem gl_operator_apply_derivation (LL : Letters ι) (S : Set ι) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K) :
    glOps K n LL S a b F = glDerivation K LL S a b F := gl_action_eq_derivation LL S a b F

/- English proof (translation)
Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Establish `h` using `congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F) (gl_derivation_lie_bracket (K := K) LL S a b c d)`. Simplify using `only [Derivation.commutator_apply] at h`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, gl_operator_apply_derivation]`. Rewrite using `[h]`.

Apply the tactic sequence `by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, gl_operator_apply_derivation]`.
-/
theorem polynomial_gl_commutation (LL : Letters ι) (S : Set ι) (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S c d - glOps K n LL S c d * glOps K n LL S a b =
      (if b = c then glOps K n LL S a d else 0) - (if d = a then glOps K n LL S c b else 0) := by
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F)
    (gl_derivation_lie_bracket (K := K) LL S a b c d)
  simp only [Derivation.commutator_apply] at h
  simp only [LinearMap.sub_apply, Module.End.mul_apply, gl_operator_apply_derivation]
  rw [h]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;> simp [h1, h2, gl_operator_apply_derivation]

/- English proof (translation)
Establish `h0 : ⁅glDerivation K LL S a b, glDerivation K LL S' c d⁆ = 0`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨l, e⟩`. Rewrite using `[Derivation.commutator_apply]`. Distinguish the cases in `hl : l ∈ S`.

Establish `hl' : l ∉ S'` using `fun h => (Set.disjoint_left.1 hd) hl h`. Simplify using `only [gl_derivation_variable, hl, hl', if_true, if_false, map_zero]`. Apply the tactic sequence `split_ifs <;> simp [gl_derivation_variable, hl']`. Apply the tactic sequence `simp only [gl_derivation_variable, hl, if_false, map_zero] split_ifs <;> simp [gl_derivation_variable, hl]`. Use `LinearMap.ext fun F => ?_` and prove the remaining obligations.

Establish `h` using `congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F) h0`. Simplify using `only [Derivation.commutator_apply] at h`. Simplify using `only [Module.End.mul_apply, gl_operator_apply_derivation]`. Conclude with `sub_eq_zero.1 h`.
-/
theorem disjoint_letters_commute (LL : Letters ι) (S S' : Set ι) (hd : Disjoint S S') (a b c d : Fin n) :
    glOps K n LL S a b * glOps K n LL S' c d = glOps K n LL S' c d * glOps K n LL S a b := by
  classical
  have h0 : ⁅glDerivation K LL S a b, glDerivation K LL S' c d⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.commutator_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∉ S' := fun h => (Set.disjoint_left.1 hd) hl h
      simp only [gl_derivation_variable, hl, hl', if_true, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl']
    · simp only [gl_derivation_variable, hl, if_false, map_zero]
      split_ifs <;> simp [gl_derivation_variable, hl]
  refine LinearMap.ext fun F => ?_
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin n) K) (MvPolynomial (ι × Fin n) K) => D F) h0
  simp only [Derivation.commutator_apply] at h
  simp only [Module.End.mul_apply, gl_operator_apply_derivation]
  exact sub_eq_zero.1 h

/- English proof (translation)
Establish `h0 : glDerivation K LL S' a b = glDerivation K LL S a b + glDerivation K LL (S' \ S) a b`. Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨l, e⟩`. Rewrite using `[Derivation.add_apply]`. Distinguish the cases in `hl : l ∈ S`.

Establish `hl' : l ∈ S'` using `hs hl`. Simplify using `[gl_derivation_variable, hl, hl']`. Apply the tactic sequence `by_cases hl' : l ∈ S' <;> simp [gl_derivation_variable, hl, hl']`. Use `LinearMap.ext fun F => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.add_apply, gl_operator_apply_derivation, h0, Derivation.add_apply]`.
-/
theorem gl_operator_union_add (LL : Letters ι) (S S' : Set ι) (hs : S ⊆ S') (a b : Fin n) :
    glOps K n LL S' a b = glOps K n LL S a b + glOps K n LL (S' \ S) a b := by
  classical
  have h0 : glDerivation K LL S' a b = glDerivation K LL S a b + glDerivation K LL (S' \ S) a b := by
    apply MvPolynomial.derivation_ext
    rintro ⟨l, e⟩
    rw [Derivation.add_apply]
    by_cases hl : l ∈ S
    · have hl' : l ∈ S' := hs hl
      simp [gl_derivation_variable, hl, hl']
    · by_cases hl' : l ∈ S' <;> simp [gl_derivation_variable, hl, hl']
  refine LinearMap.ext fun F => ?_
  simp only [LinearMap.add_apply, gl_operator_apply_derivation, h0, Derivation.add_apply]

/- English proof (translation)
Rewrite using `[MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul, add_comm (Finsupp.single v 1)]`.
-/
theorem variable_mul_pderiv_monomial {σ : Type} (v w : σ) (m : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * pderiv w (monomial m c) =
      monomial (m - Finsupp.single w 1 + Finsupp.single v 1) (c * (m w : K)) := by
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul, one_mul,
    add_comm (Finsupp.single v 1)]

open Classical in
/- English proof (translation)
Simplify using `only [glDerivation, derivation_finset_sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`. Simplify using `only [Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]`. Simplify using `only [Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]`.

Simplify using the standard rewrite rules.
-/
theorem gl_derivation_monomial (LL : Letters ι) (S : Set ι) (a b : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a b (monomial m c) =
      ∑ l : ι, if l ∈ S then
        (if LL.vec l then monomial (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) (c * (m (l, b) : K))
         else -monomial (m - Finsupp.single (l, a) 1 + Finsupp.single (l, b) 1) (c * (m (l, a) : K)))
      else 0 := by
  simp only [glDerivation, derivation_finset_sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs
  · simp only [Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp only [Derivation.neg_apply, Derivation.smul_apply, smul_eq_mul, variable_mul_pderiv_monomial]
  · simp

/- English proof (translation)
Unfold `multideg`. Establish `hle : ∀ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) ≤ m (i, c)`. Introduce `c`. Rewrite using `[Finsupp.single_apply]`. Use `split_ifs with hc`.

Rewrite using `[← hc]`. Conclude with `Nat.one_le_iff_ne_zero.mpr h`. Conclude with `Nat.zero_le _`. Establish `hs : ∑ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) = ∑ c : Fin n, (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c)`. Distinguish the cases in `hi : i = l`.

Substitute `hi` using the available equality. Simplify using `[Finsupp.single_apply]`. Simplify using `[Finsupp.single_apply, Ne.symm hi]`. Establish `key : ∀ c : Fin n, (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) + (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) = m (i, c) + (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c)`. Introduce `c`.

Rewrite using `[Finsupp.add_apply, Finsupp.tsub_apply]`. Use `hle c` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hsum` using `Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => key c)`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, hs]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem multidegree_polarization_move (m : ι × Fin n →₀ ℕ) (l : ι) (a b : Fin n) (h : m (l, b) ≠ 0) (i : ι) :
    multideg (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1) i = multideg m i := by
  classical
  unfold multideg
  have hle : ∀ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) ≤ m (i, c) := by
    intro c
    rw [Finsupp.single_apply]
    split_ifs with hc
    · rw [← hc]; exact Nat.one_le_iff_ne_zero.mpr h
    · exact Nat.zero_le _
  have hs : ∑ c : Fin n, (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c) =
      ∑ c : Fin n, (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    by_cases hi : i = l
    · subst hi
      simp [Finsupp.single_apply]
    · simp [Finsupp.single_apply, Ne.symm hi]
  have key : ∀ c : Fin n, (m - Finsupp.single (l, b) 1 + Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c)
      + (Finsupp.single (l, b) 1 : ι × Fin n →₀ ℕ) (i, c)
      = m (i, c) + (Finsupp.single (l, a) 1 : ι × Fin n →₀ ℕ) (i, c) := by
    intro c
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    have := hle c
    omega
  have hsum := Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => key c)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hs] at hsum
  omega

/- English proof (translation)
Rewrite using `[gl_operator_apply_derivation, F.as_sum, map_sum]`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hm' : ∀ i, multideg m i = d i` using `(MvPolynomial.mem_restrictSupport_iff K).1 hF (by simpa using hm)`. Rewrite using `[gl_derivation_monomial]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations.

Use `split_ifs`. Rewrite using `[Pol, monomial_mem_restrictSupport]`. Distinguish the cases in `h0 : m (l, b) = 0`. Use `right`. Simplify using `[h0]`.

Use `left`. Introduce `i`. Rewrite using `[multidegree_polarization_move m l a b h0, hm']`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Rewrite using `[Pol, monomial_mem_restrictSupport]`.

Distinguish the cases in `h0 : m (l, a) = 0`. Use `right`. Simplify using `[h0]`. Use `left`. Introduce `i`.

Rewrite using `[multidegree_polarization_move m l b a h0, hm']`. Conclude with `Submodule.zero_mem _`.
-/
theorem gl_operator_preserves_multidegree (LL : Letters ι) (S : Set ι) (d : ι → ℕ) (a b : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ Pol K n d) : glOps K n LL S a b F ∈ Pol K n d := by
  classical
  rw [gl_operator_apply_derivation, F.as_sum, map_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hm' : ∀ i, multideg m i = d i := (MvPolynomial.mem_restrictSupport_iff K).1 hF (by simpa using hm)
  rw [gl_derivation_monomial]
  refine Submodule.sum_mem _ fun l _ => ?_
  split_ifs
  · rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, b) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l a b h0, hm']
  · refine Submodule.neg_mem _ ?_
    rw [Pol, monomial_mem_restrictSupport]
    by_cases h0 : m (l, a) = 0
    · right; simp [h0]
    · left; intro i; rw [multidegree_polarization_move m l b a h0, hm']
  · exact Submodule.zero_mem _

/- English proof (translation)
Establish `hfin : Set.Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}`. Use `(Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : ι × Fin n => d v.1))).subset ?_` and prove the remaining obligations. Introduce `m hm v`. Use `hm v.1` as an intermediate fact. Simplify using `only [Finsupp.equivFunOnFinite_symm_apply_apply]`.

Rewrite using `[← this]`. Conclude with `Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)`. Establish `: Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i}` using `hfin`. Conclude with `Module.Finite.of_basis (basisRestrictSupport K {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i})`.
-/
theorem homogeneous_multidegree_findim (d : ι → ℕ) : FiniteDimensional K (Pol K n d) := by
  classical
  have hfin : Set.Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := by
    refine (Set.finite_Iic (Finsupp.equivFunOnFinite.symm (fun v : ι × Fin n => d v.1))).subset ?_
    intro m hm v
    have := hm v.1
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← this]
    exact Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  have : Finite {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i} := hfin
  exact Module.Finite.of_basis (basisRestrictSupport K {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = d i})

end Formalism.MainNotions.G.GLWeightTheory
