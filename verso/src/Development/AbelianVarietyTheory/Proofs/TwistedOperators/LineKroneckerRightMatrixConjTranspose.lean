import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ISupEigenspaceEqTop

noncomputable section

open MvPolynomial GlobalTheory.Capelli Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.JointHarm

section Adjoint

variable {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {ι : MvPolynomial σ ℂ →ₗ[ℂ] H}

/- English proof (translation)
Simplify using `[smul_monomial]`.
-/
theorem monomial_eq_smul (m : σ →₀ ℕ) (c : ℂ) :
    monomial m c = c • (monomial m 1 : MvPolynomial σ ℂ) := by simp [smul_monomial]

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `add P P' hP hP' => simp only [mul_add, map_add, inner_add_left, hP, hP']`. Consider the case `monomial α c`. Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `add Q Q' hQ hQ' => simp only [map_add, inner_add_right, hQ, hQ']`.

Consider the case `monomial β d`. Rewrite using `[monomial_eq_smul α c, monomial_eq_smul β d, mul_smul_comm, Derivation.map_smul]`. Simplify using `only [map_smul, inner_smul_left, inner_smul_right]`. Use `congr 2`. Rewrite using `[pderiv_monomial, monomial_eq_smul (β - _), map_smul, inner_smul_right, X, monomial_mul, one_mul, h, h, one_mul]`.

Distinguish the cases in `e : Finsupp.single i 1 + α = β`. Substitute `e` using the available equality. Rewrite using `[if_pos rfl, if_pos (by simp)]`. Rewrite using `[Finsupp.prod_of_support_subset _ (s := insert i α.support) _ _ (by simp), Finsupp.prod_of_support_subset α (s := insert i α.support) (Finset.subset_insert _ _) _ (by simp), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i _), ← Finset.mul_prod_erase (insert i α.support) _ ( …`. Use `congr 1`.

Simplify using `[add_comm 1, Nat.factorial_succ]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Simplify using `[Finsupp.single_apply, (Finset.ne_of_mem_erase hj).symm]`. Introduce `j hj`. Distinguish the cases in `hji : j = i`.

Simplify using `[hji]`. Simplify `hj` using `[hji, Finsupp.single_apply, Ne.symm hji]`. Rewrite using `[if_neg e]`. Distinguish the cases in `hb : β i = 0`. Simplify using `[hb]`.

Rewrite using `[if_neg, mul_zero]`. Introduce and unpack `rfl`. Apply `e` to reduce the goal to its premises. Use extensionality with `j`. Distinguish the cases in `hji : j = i`.

Substitute `hji` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[Ne.symm hji]`.
-/
theorem inner_X_mul (h : IsFockIP ι) (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (X i * P)) (ι Q) = inner ℂ (ι P) (ι (pderiv i Q)) := by
  induction P using MvPolynomial.induction_on' with
  | add P P' hP hP' => simp only [mul_add, map_add, inner_add_left, hP, hP']
  | monomial α c =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' hQ hQ' => simp only [map_add, inner_add_right, hQ, hQ']
    | monomial β d =>
      rw [monomial_eq_smul α c, monomial_eq_smul β d, mul_smul_comm, Derivation.map_smul]
      simp only [map_smul, inner_smul_left, inner_smul_right]
      congr 2
      rw [pderiv_monomial, monomial_eq_smul (β - _), map_smul, inner_smul_right, X, monomial_mul,
        one_mul, h, h, one_mul]
      by_cases e : Finsupp.single i 1 + α = β
      · subst e
        rw [if_pos rfl, if_pos (by simp)]
        rw [Finsupp.prod_of_support_subset _ (s := insert i α.support) _ _ (by simp),
          Finsupp.prod_of_support_subset α (s := insert i α.support)
            (Finset.subset_insert _ _) _ (by simp),
          ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i _),
          ← Finset.mul_prod_erase (insert i α.support) _ (Finset.mem_insert_self i _), ← mul_assoc]
        · congr 1
          · simp [add_comm 1, Nat.factorial_succ]
          · refine Finset.prod_congr rfl fun j hj => ?_
            simp [Finsupp.single_apply, (Finset.ne_of_mem_erase hj).symm]
        · intro j hj
          by_cases hji : j = i
          · simp [hji]
          · simpa [hji, Finsupp.single_apply, Ne.symm hji] using hj
      · rw [if_neg e]
        by_cases hb : β i = 0
        · simp [hb]
        · rw [if_neg, mul_zero]
          rintro rfl
          apply e
          ext j
          by_cases hji : j = i
          · subst hji; simp; omega
          · simp [Ne.symm hji]

/- English proof (translation)
Rewrite using `[← inner_conj_symm, ← inner_X_mul h, inner_conj_symm]`.
-/
theorem inner_pderiv (h : IsFockIP ι) (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (pderiv i P)) (ι Q) = inner ℂ (ι P) (ι (X i * Q)) := by
  rw [← inner_conj_symm, ← inner_X_mul h, inner_conj_symm]

/- English proof (translation)
Rewrite using `[polar_apply, polar_apply, inner_X_mul h, inner_pderiv h]`.
-/
theorem inner_polar (h : IsFockIP ι) (u v : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (polar ℂ u v P)) (ι Q) = inner ℂ (ι P) (ι (polar ℂ v u Q)) := by
  rw [polar_apply, polar_apply, inner_X_mul h, inner_pderiv h]

/- English proof (translation)
Simplify using `only [colOp, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, inner_polar h]`.
-/
theorem inner_colOp (h : IsFockIP ι) {I J : Type*} [Fintype I] (z : I × J → σ) (k l : J)
    (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (colOp ℂ z k l P)) (ι Q) = inner ℂ (ι P) (ι (colOp ℂ z l k Q)) := by
  simp only [colOp, LinearMap.sum_apply, map_sum, sum_inner, inner_sum, inner_polar h]

/- English proof (translation)
Simplify using `only [mixedOp, LinearMap.sub_apply, map_sub, inner_sub_left, inner_sub_right, inner_colOp h]`.
-/
theorem inner_mixedOp (h : IsFockIP ι) {I I' J : Type*} [Fintype I] [Fintype I'] (z : I × J → σ)
    (y : I' × J → σ) (k l : J) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (mixedOp ℂ z y k l P)) (ι Q) = inner ℂ (ι P) (ι (mixedOp ℂ z y l k Q)) := by
  simp only [mixedOp, LinearMap.sub_apply, map_sub, inner_sub_left, inner_sub_right, inner_colOp h]

end Adjoint

/- English proof (translation)
Take `⟨_, ⟨u, hu, rfl⟩, o, ho, e⟩` from `Submodule.exists_add_mem_mem_orthogonal (K := R.map ι) (ι w)`. Use `⟨u, hu, fun v hv => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, e, add_sub_cancel_left]`. Conclude with `Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hv) ho`.
-/
theorem exists_orth {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H) (R : Submodule ℂ V) [FiniteDimensional ℂ R] (w : V) :
    ∃ u ∈ R, ∀ v ∈ R, inner ℂ (ι v) (ι (w - u)) = 0 := by
  obtain ⟨_, ⟨u, hu, rfl⟩, o, ho, e⟩ := Submodule.exists_add_mem_mem_orthogonal (K := R.map ι) (ι w)
  refine ⟨u, hu, fun v hv => ?_⟩
  rw [map_sub, e, add_sub_cancel_left]
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.mem_map_of_mem hv) ho

instance finite_homog {σ : Type} [Finite σ] (d : ℕ) : FiniteDimensional ℂ (homog σ d) :=
  Submodule.finiteDimensional_of_le (S₂ := restrictTotalDegree σ ℂ d) fun P hP =>
    (mem_restrictTotalDegree _ _ _).2 (IsHomogeneous.totalDegree_le hP)

section Parts

variable {σ : Type}

/- English proof (translation)
Establish `hh` using `fun d => homogeneousComponent_isHomogeneous d P`. Establish `key : ∀ (T : Module.End ℂ (MvPolynomial σ ℂ)), ∑ᶠ d, T (homogeneousComponent d P) = T P`. Introduce `T`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)), ← map_sum, sum_homogeneousComponent]`. Introduce `d hd`.

Assume the negation of the conclusion as `h`. Conclude with `hd (by simp only; rw [homogeneousComponent_eq_zero _ _ (by simpa using h), map_zero])`. Prove the components needed by the constructor for the conclusion. Rewrite using `[← key U, plusPart]`. Use `finsum_congr fun d => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ (hh d)), if_pos rfl, homogeneousComponent_of_mem (hD _ _ (hh d)), if_neg (by omega), add_zero]`. Establish `h2 : ∀ d, homogeneousComponent d ((U + D) (homogeneousComponent (d + 2) P)) = D (homogeneousComponent (d + 2) P)` using `fun d => by`. Rewrite using `[LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ (hh _)), if_neg (by omega), homogeneousComponent_of_mem (hD _ _ (hh _)), if_pos (by omega), zero_add]`. Rewrite using `[minusPart, finsum_congr h2, ← key D]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)), finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1 + 1 + 1)), Finset.sum_range_succ' _ (P.totalDegree + 1 + 1), Finset.sum_range_succ' (fun k => D (homogeneousComponent (k + 1) P)) (P.tot …`.

Simplify using the standard rewrite rules. Use `all_goals`. Introduce `d hd`. Assume the negation of the conclusion as `h`. Conclude with `hd (by`.

Simplify using `only`. Rewrite using `[homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero])`.
-/
theorem parts_of_add (U D : Module.End ℂ (MvPolynomial σ ℂ))
    (hU : ∀ d P, P.IsHomogeneous d → (U P).IsHomogeneous (d + 2))
    (hD : ∀ d P, P.IsHomogeneous d → (D P).IsHomogeneous (d - 2))
    (hD0 : ∀ d < 2, ∀ P, P.IsHomogeneous d → D P = 0) (P : MvPolynomial σ ℂ) :
    plusPart (U + D) P = U P ∧ minusPart (U + D) P = D P := by
  have hh := fun d => homogeneousComponent_isHomogeneous d P
  have key : ∀ (T : Module.End ℂ (MvPolynomial σ ℂ)),
      ∑ᶠ d, T (homogeneousComponent d P) = T P := by
    intro T
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)), ← map_sum,
      sum_homogeneousComponent]
    intro d hd
    by_contra h
    exact hd (by simp only; rw [homogeneousComponent_eq_zero _ _ (by simpa using h), map_zero])
  constructor
  · rw [← key U, plusPart]
    refine finsum_congr fun d => ?_
    rw [LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ (hh d)), if_pos rfl,
      homogeneousComponent_of_mem (hD _ _ (hh d)), if_neg (by omega), add_zero]
  · have h2 : ∀ d, homogeneousComponent d ((U + D) (homogeneousComponent (d + 2) P)) =
        D (homogeneousComponent (d + 2) P) := fun d => by
      rw [LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ (hh _)),
        if_neg (by omega), homogeneousComponent_of_mem (hD _ _ (hh _)), if_pos (by omega), zero_add]
    rw [minusPart, finsum_congr h2, ← key D]
    rw [finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)),
      finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1 + 1 + 1)),
      Finset.sum_range_succ' _ (P.totalDegree + 1 + 1),
      Finset.sum_range_succ' (fun k => D (homogeneousComponent (k + 1) P)) (P.totalDegree + 1),
      hD0 0 (by omega) _ (hh 0), hD0 (0 + 1) (by omega) _ (hh _)]
    · simp
    all_goals
      intro d hd
      by_contra h
      exact hd (by
        simp only
        rw [homogeneousComponent_eq_zero _ _ (by simp at h; omega), map_zero])

end Parts

section Lines

variable {p q r s : ℕ}

def upOp (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', if linePos l then M l l' • LinearMap.mulLeft ℂ (X l * X l') else 0

def dnOp (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', if linePos l then 0 else
    -M l l' • ((pderiv l).toLinearMap * (pderiv l').toLinearMap)

def Odd' (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Prop :=
  ∀ l l', linePos l = linePos l' → M l l' = 0

/- English proof (translation)
Rewrite using `[omAct_apply, upOp, dnOp, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : linePos l = linePos l'`.

Simplify using `[h l l' e]`. Establish `hne : l ≠ l'` using `fun h => e (by rw [h])`. Apply the tactic sequence `cases h1 : linePos l <;> cases h2 : linePos l' <;> simp_all [omE, raiB, lowB]`. Both sides reduce to the same expression.
-/
theorem omAct_odd {M : Matrix (Ln p q r s) (Ln p q r s) ℂ} (h : Odd' M) :
    omAct p q r s M = upOp M + dnOp M := by
  rw [omAct_apply, upOp, dnOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases e : linePos l = linePos l'
  · simp [h l l' e]
  · have hne : l ≠ l' := fun h => e (by rw [h])
    cases h1 : linePos l <;> cases h2 : linePos l' <;> simp_all [omE, raiB, lowB]
    rfl

/- English proof (translation)
Simplify using `only [upOp, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem upOp_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    upOp M P = ∑ l, ∑ l', if linePos l then M l l' • (X l * X l' * P) else 0 := by
  simp only [upOp, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  split_ifs <;> rfl

/- English proof (translation)
Simplify using `only [dnOp, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem dnOp_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    dnOp M P = ∑ l, ∑ l', if linePos l then 0 else -M l l' • pderiv l (pderiv l' P) := by
  simp only [dnOp, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  split_ifs <;> rfl

/- English proof (translation)
Rewrite using `[upOp_apply]`. Use `IsHomogeneous.sum _ _ _ fun l _ => IsHomogeneous.sum _ _ _ fun l' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Use `(homogeneousSubmodule _ ℂ (d + 2)).smul_mem _ ?_` and prove the remaining obligations. Use `((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP` as an intermediate fact.

Rewrite `this` using `[add_comm]`. Then use the resulting hypothesis. Conclude with `isHomogeneous_zero _ _ _`.
-/
theorem upOp_homog (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (P : Pol p q r s)
    (hP : P.IsHomogeneous d) : (upOp M P).IsHomogeneous (d + 2) := by
  rw [upOp_apply]
  refine IsHomogeneous.sum _ _ _ fun l _ => IsHomogeneous.sum _ _ _ fun l' _ => ?_
  split_ifs
  · refine (homogeneousSubmodule _ ℂ (d + 2)).smul_mem _ ?_
    have := ((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP
    rwa [add_comm] at this
  · exact isHomogeneous_zero _ _ _

/- English proof (translation)
Rewrite using `[dnOp_apply]`. Use `IsHomogeneous.sum _ _ _ fun l _ => IsHomogeneous.sum _ _ _ fun l' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `isHomogeneous_zero _ _ _`. Conclude with `(homogeneousSubmodule _ ℂ (d - 2)).smul_mem _ (hP.pderiv.pderiv)`.
-/
theorem dnOp_homog (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (P : Pol p q r s)
    (hP : P.IsHomogeneous d) : (dnOp M P).IsHomogeneous (d - 2) := by
  rw [dnOp_apply]
  refine IsHomogeneous.sum _ _ _ fun l _ => IsHomogeneous.sum _ _ _ fun l' _ => ?_
  split_ifs
  · exact isHomogeneous_zero _ _ _
  · exact (homogeneousSubmodule _ ℂ (d - 2)).smul_mem _ (hP.pderiv.pderiv)

/- English proof (translation)
Rewrite using `[dnOp_apply]`. Use `Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_` and prove the remaining obligations. Use `split_ifs`. Both sides reduce to the same expression. Establish `h : (pderiv l' P).IsHomogeneous 0`.

Use `hP.pderiv (i := l')` as an intermediate fact. Rewrite `this` using `[show d - 1 = 0 by omega]`. Then use the resulting hypothesis. Rewrite using `[totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 h), pderiv_C, smul_zero]`.
-/
theorem dnOp_low (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (hd : d < 2) (P : Pol p q r s)
    (hP : P.IsHomogeneous d) : dnOp M P = 0 := by
  rw [dnOp_apply]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_
  split_ifs
  · rfl
  · have h : (pderiv l' P).IsHomogeneous 0 := by
      have := hP.pderiv (i := l')
      rwa [show d - 1 = 0 by omega] at this
    rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 h), pderiv_C,
      smul_zero]

/- English proof (translation)
Rewrite using `[omAct_odd h]`. Conclude with `parts_of_add _ _ (upOp_homog M) (dnOp_homog M) (dnOp_low M) P`.
-/
theorem parts_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ} (h : Odd' M) (P : Pol p q r s) :
    plusPart (omAct p q r s M) P = upOp M P ∧ minusPart (omAct p q r s M) P = dnOp M P := by
  rw [omAct_odd h]
  exact parts_of_add _ _ (upOp_homog M) (dnOp_homog M) (dnOp_low M) P

/- English proof (translation)
Rewrite using `[upOp_apply, dnOp_apply, Finset.sum_comm]`. Simplify using `only [map_sum, sum_inner, inner_sum, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Distinguish the cases in `e : linePos l' = linePos l`. Simplify using `[h l' l e]`.

Apply the tactic sequence `cases h1 : linePos l <;> cases h2 : linePos l' <;> simp_all [mul_assoc]`. Rewrite using `[inner_smul_left, inner_smul_right, inner_X_mul hι, inner_X_mul hι]`.
-/
theorem inner_upOp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (h : Odd' M) (Q P : Pol p q r s) :
    inner ℂ (ι (upOp M Q)) (ι P) = -inner ℂ (ι Q) (ι (dnOp M.conjTranspose P)) := by
  rw [upOp_apply, dnOp_apply, Finset.sum_comm]
  simp only [map_sum, sum_inner, inner_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => ?_
  by_cases e : linePos l' = linePos l
  · simp [h l' l e]
  · cases h1 : linePos l <;> cases h2 : linePos l' <;> simp_all [mul_assoc]
    rw [inner_smul_left, inner_smul_right, inner_X_mul hι, inner_X_mul hι]

/- English proof (translation)
Establish `hle : Submodule.span ℂ R ≤ homog (Ln p q r s) (d + 2)`. Use `Submodule.span_le.2 fun P hP => ?_` and prove the remaining obligations. Take `⟨Q, hQ, M, hM, rfl⟩` from `(hR P).1 hP`. Rewrite using `[(parts_omAct (hS M hM) Q).1]`. Conclude with `upOp_homog M d Q hQ`.

Use `le_antisymm (fun P hP => ?_) (sup_le inf_le_left hle)` and prove the remaining obligations. Use `Submodule.finiteDimensional_of_le hle` as an intermediate fact. Take `⟨u, hu, ho⟩` from `exists_orth ι (Submodule.span ℂ R) P`. Establish `hh` using `Submodule.sub_mem _ hP (hle hu)`. Rewrite using `[← sub_add_cancel P u]`.

Use `Submodule.add_mem_sup ⟨hh, Submodule.subset_span (hK _ fun M hM => ?_)⟩ hu` and prove the remaining obligations. Take `⟨N, hN, rfl⟩` from `hS' M hM`. Rewrite using `[(parts_omAct (hS _ hM) _).2]`. Establish `h1` using `ho _ (Submodule.subset_span ((hR _).2 ⟨_, dnOp_homog N.conjTranspose (d + 2) _ hh, N, hN, rfl⟩))`. Rewrite `h1` using `[(parts_omAct (hS _ hN) _).1, inner_upOp hι (hS _ hN), neg_eq_zero, inner_self_eq_zero]`.

Conclude with `hinj (h1.trans (map_zero ι).symm)`.
-/
theorem fischer {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) (hinj : Function.Injective ι)
    (S : Set (Matrix (Ln p q r s) (Ln p q r s) ℂ)) (hS : ∀ M ∈ S, Odd' M)
    (hS' : ∀ M ∈ S, ∃ N ∈ S, M = N.conjTranspose) (d : ℕ) (K R : Set (Pol p q r s))
    (hK : ∀ P, (∀ M ∈ S, minusPart (omAct p q r s M) P = 0) → P ∈ K)
    (hR : ∀ P, P ∈ R ↔ ∃ Q ∈ homog (Ln p q r s) d, ∃ M ∈ S, P = plusPart (omAct p q r s M) Q) :
    homog (Ln p q r s) (d + 2) =
      (homog (Ln p q r s) (d + 2) ⊓ Submodule.span ℂ K) ⊔ Submodule.span ℂ R := by
  have hle : Submodule.span ℂ R ≤ homog (Ln p q r s) (d + 2) := by
    refine Submodule.span_le.2 fun P hP => ?_
    obtain ⟨Q, hQ, M, hM, rfl⟩ := (hR P).1 hP
    rw [(parts_omAct (hS M hM) Q).1]
    exact upOp_homog M d Q hQ
  refine le_antisymm (fun P hP => ?_) (sup_le inf_le_left hle)
  have := Submodule.finiteDimensional_of_le hle
  obtain ⟨u, hu, ho⟩ := exists_orth ι (Submodule.span ℂ R) P
  have hh := Submodule.sub_mem _ hP (hle hu)
  rw [← sub_add_cancel P u]
  refine Submodule.add_mem_sup ⟨hh, Submodule.subset_span (hK _ fun M hM => ?_)⟩ hu
  obtain ⟨N, hN, rfl⟩ := hS' M hM
  rw [(parts_omAct (hS _ hM) _).2]
  have h1 := ho _ (Submodule.subset_span ((hR _).2
    ⟨_, dnOp_homog N.conjTranspose (d + 2) _ hh, N, hN, rfl⟩))
  rw [(parts_omAct (hS _ hN) _).1, inner_upOp hι (hS _ hN), neg_eq_zero, inner_self_eq_zero] at h1
  exact hinj (h1.trans (map_zero ι).symm)

def kron1 (r s : ℕ) (Z : Mat p q) : Matrix (Ln p q r s) (Ln p q r s) ℂ :=
  Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)

def kron2 (p q : ℕ) (Z : Mat r s) : Matrix (Ln p q r s) (Ln p q r s) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Mat p q) Z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct1_eq (Z : Mat p q) : fockAct1 p q r s Z = omAct p q r s (kron1 r s Z) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct2_eq (Z : Mat r s) : fockAct2 p q r s Z = omAct p q r s (kron2 p q Z) := rfl

/- English proof (translation)
Introduce and unpack `⟨a, c⟩ ⟨b, d⟩ e`. Distinguish the cases in `hcd : c = d`. Substitute `hcd` using the available equality. Establish `: sameBlock a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>`.

Simplify using `[linePos, sameBlock]`. Simplify using `[kron1, h a b this]`. Simplify using `[kron1, hcd]`.
-/
theorem odd_kron1 {Z : Mat p q} (h : IsPC Z) : Odd' (kron1 r s Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ e
  by_cases hcd : c = d
  · subst hcd
    have : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
        simp_all [linePos, sameBlock]
    simp [kron1, h a b this]
  · simp [kron1, hcd]

/- English proof (translation)
Introduce and unpack `⟨a, c⟩ ⟨b, d⟩ e`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `: sameBlock c d`. Apply the tactic sequence `rcases a with a | a <;> rcases d with d | d <;> rcases c with c | c <;>`.

Simplify using `[linePos, sameBlock]`. Simplify using `[kron2, h c d this]`. Simplify using `[kron2, hab]`.
-/
theorem odd_kron2 {Z : Mat r s} (h : IsPC Z) : Odd' (kron2 p q Z) := by
  rintro ⟨a, c⟩ ⟨b, d⟩ e
  by_cases hab : a = b
  · subst hab
    have : sameBlock c d := by
      rcases a with a | a <;> rcases d with d | d <;> rcases c with c | c <;>
        simp_all [linePos, sameBlock]
    simp [kron2, h c d this]
  · simp [kron2, hab]

/- English proof (translation)
Introduce `a b hab`. Rewrite using `[Matrix.conjTranspose_apply, h b a, star_zero]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`.
-/
theorem isPC_conjTranspose {Z : Mat p q} (h : IsPC Z) : IsPC Z.conjTranspose := by
  intro a b hab
  rw [Matrix.conjTranspose_apply, h b a, star_zero]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

/- English proof (translation)
Use extensionality with `⟨a, c⟩ ⟨b, d⟩`. Simplify using `[kron1, Matrix.one_apply, eq_comm]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lineKroneckerLeftMatrix_conjTranspose (Z : Mat p q) :
    kron1 r s Z = (kron1 r s Z.conjTranspose).conjTranspose := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [kron1, Matrix.one_apply, eq_comm]
  split_ifs <;> simp

/- English proof (translation)
Use extensionality with `⟨a, c⟩ ⟨b, d⟩`. Simplify using `[kron2, Matrix.one_apply, eq_comm]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem lineKroneckerRightMatrix_conjTranspose (Z : Mat r s) :
    kron2 p q Z = (kron2 p q Z.conjTranspose).conjTranspose := by
  ext ⟨a, c⟩ ⟨b, d⟩
  simp [kron2, Matrix.one_apply, eq_comm]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[fockAct1_eq, (parts_omAct (odd_kron1 h) P).2, dnOp_apply, Fintype.sum_prod_type_right]`. Use `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Establish `e : linePos ((c, a) : Ln r s p q) = linePos ((a, c) : Ln p q r s)`.

Apply the tactic sequence `rcases a with a | a <;> rcases c with c | c <;> rfl`. Rewrite using `[e]`. Use `split_ifs`. Simplify using the standard rewrite rules. Apply the tactic sequence `rw [Finset.sum_eq_single c] <;> simp +contextual [kron1, Matrix.one_apply, eq_comm]`.
-/
theorem minusPart_fockAct1_offDiagonal {Z : Mat p q} (h : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct1 p q r s Z) P = ∑ c, ∑ a, ∑ b,
      if linePos ((c, a) : Ln r s p q) then 0 else -Z a b • pderiv (a, c) (pderiv (b, c) P) := by
  rw [fockAct1_eq, (parts_omAct (odd_kron1 h) P).2, dnOp_apply, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  have e : linePos ((c, a) : Ln r s p q) = linePos ((a, c) : Ln p q r s) := by
    rcases a with a | a <;> rcases c with c | c <;> rfl
  rw [e]
  split_ifs
  · simp
  · rw [Finset.sum_eq_single c] <;> simp +contextual [kron1, Matrix.one_apply, eq_comm]

/- English proof (translation)
Rewrite using `[fockAct2_eq, (parts_omAct (odd_kron2 h) P).2, dnOp_apply, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type_right]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Simplify using the standard rewrite rules. Apply the tactic sequence `rw [Finset.sum_eq_single a] <;> simp +contextual [kron2, Matrix.one_apply, eq_comm]`.
-/
theorem minusPart_fockAct2_offDiagonal {Z : Mat r s} (h : IsPC Z) (P : Pol p q r s) :
    minusPart (fockAct2 p q r s Z) P = ∑ a, ∑ c, ∑ d,
      if linePos ((a, c) : Ln p q r s) then 0 else -Z c d • pderiv (a, c) (pderiv (a, d) P) := by
  rw [fockAct2_eq, (parts_omAct (odd_kron2 h) P).2, dnOp_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs
  · simp
  · rw [Finset.sum_eq_single a] <;> simp +contextual [kron2, Matrix.one_apply, eq_comm]

end Lines

end GlobalTheory.JointHarm
