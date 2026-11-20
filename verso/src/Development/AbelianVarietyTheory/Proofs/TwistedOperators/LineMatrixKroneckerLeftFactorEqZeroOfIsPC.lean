import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

noncomputable section
namespace GlobalTheory.FockDeg
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial Matrix

section General
variable {σ : Type}

/- English proof (translation)
Establish `h0 : P.totalDegree = 0` using `Nat.le_zero.mp h.totalDegree_le`. Rewrite `h0` using `[totalDegree_eq_zero_iff_eq_C]`. Rewrite using `[h0, pderiv_C]`.
-/
theorem pderiv_eq_zero_of_deg_zero {P : MvPolynomial σ ℂ} (h : P.IsHomogeneous 0) (i : σ) :
    pderiv i P = 0 := by
  have h0 : P.totalDegree = 0 := Nat.le_zero.mp h.totalDegree_le
  rw [totalDegree_eq_zero_iff_eq_C] at h0
  rw [h0, pderiv_C]

/- English proof (translation)
Establish `h : ∀ d, homogeneousComponent (d + 2) ((U + D) (homogeneousComponent d P)) = U (homogeneousComponent d P)`. Introduce `d`. Establish `hm` using `homogeneousComponent_mem d P`. Rewrite using `[LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU d _ hm), homogeneousComponent_of_mem (hD d _ hm), if_pos rfl, if_neg (by omega), add_zero]`. Unfold `plusPart`.

Simplify using `only [h]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)), ← map_sum, sum_homogeneousComponent]`. Introduce `d hd`. Assume the negation of the conclusion as `hc`. Apply `hd` to reduce the goal to its premises.

Establish `: P.totalDegree < d` using `by simpa using hc`. Simplify using `[homogeneousComponent_eq_zero _ _ this]`.
-/
theorem plusPart_add (U D : Module.End ℂ (MvPolynomial σ ℂ))
    (hU : ∀ d P, P ∈ homog σ d → U P ∈ homog σ (d + 2))
    (hD : ∀ d P, P ∈ homog σ d → D P ∈ homog σ (d - 2)) (P : MvPolynomial σ ℂ) :
    plusPart (U + D) P = U P := by
  have h : ∀ d, homogeneousComponent (d + 2) ((U + D) (homogeneousComponent d P)) =
      U (homogeneousComponent d P) := by
    intro d
    have hm := homogeneousComponent_mem d P
    rw [LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU d _ hm),
      homogeneousComponent_of_mem (hD d _ hm), if_pos rfl, if_neg (by omega), add_zero]
  unfold plusPart
  simp only [h]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1)), ← map_sum,
    sum_homogeneousComponent]
  intro d hd
  by_contra hc
  apply hd
  have : P.totalDegree < d := by simpa using hc
  simp [homogeneousComponent_eq_zero _ _ this]

/- English proof (translation)
Establish `h : ∀ d, homogeneousComponent d ((U + D) (homogeneousComponent (d + 2) P)) = D (homogeneousComponent (d + 2) P)`. Introduce `d`. Establish `hm` using `homogeneousComponent_mem (d + 2) P`. Rewrite using `[LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ hm), homogeneousComponent_of_mem (hD _ _ hm), if_neg (by omega), if_pos (by omega), zero_add]`. Unfold `minusPart`.

Simplify using `only [h]`. Rewrite using `[finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1))]`. Establish `h2 : ∑ d ∈ Finset.range (P.totalDegree + 1 + 1 + 1), homogeneousComponent d P = P`. Rewrite using `[Finset.sum_range_succ, Finset.sum_range_succ, sum_homogeneousComponent, homogeneousComponent_eq_zero _ _ (by omega), homogeneousComponent_eq_zero _ _ (by omega)]`. Simplify using the standard rewrite rules.

Use `conv_rhs => rw [← h2]`. Rewrite using `[Finset.sum_range_succ' _ (P.totalDegree + 1 + 1), Finset.sum_range_succ' _ (P.totalDegree + 1), map_add, map_add, map_sum, hD0 _ _ (by omega) (homogeneousComponent_mem 0 P), hD0 _ _ (by omega) (homogeneousComponent_mem (0 + 1) P), add_zero, add_zero]`. Introduce `d hd`. Assume the negation of the conclusion as `hc`. Apply `hd` to reduce the goal to its premises.

Establish `: P.totalDegree < d + 2`. Establish `: P.totalDegree < d` using `by simpa using hc`. Use linear arithmetic over natural numbers and integers. Simplify using `[homogeneousComponent_eq_zero _ _ this]`.
-/
theorem minusPart_add (U D : Module.End ℂ (MvPolynomial σ ℂ))
    (hU : ∀ d P, P ∈ homog σ d → U P ∈ homog σ (d + 2))
    (hD : ∀ d P, P ∈ homog σ d → D P ∈ homog σ (d - 2))
    (hD0 : ∀ d P, d < 2 → P ∈ homog σ d → D P = 0) (P : MvPolynomial σ ℂ) :
    minusPart (U + D) P = D P := by
  have h : ∀ d, homogeneousComponent d ((U + D) (homogeneousComponent (d + 2) P)) =
      D (homogeneousComponent (d + 2) P) := by
    intro d
    have hm := homogeneousComponent_mem (d + 2) P
    rw [LinearMap.add_apply, map_add, homogeneousComponent_of_mem (hU _ _ hm),
      homogeneousComponent_of_mem (hD _ _ hm), if_neg (by omega), if_pos (by omega), zero_add]
  unfold minusPart
  simp only [h]
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (P.totalDegree + 1))]
  · have h2 : ∑ d ∈ Finset.range (P.totalDegree + 1 + 1 + 1), homogeneousComponent d P = P := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ, sum_homogeneousComponent,
        homogeneousComponent_eq_zero _ _ (by omega), homogeneousComponent_eq_zero _ _ (by omega)]
      simp
    conv_rhs => rw [← h2]
    rw [Finset.sum_range_succ' _ (P.totalDegree + 1 + 1), Finset.sum_range_succ' _ (P.totalDegree + 1),
      map_add, map_add, map_sum,
      hD0 _ _ (by omega) (homogeneousComponent_mem 0 P),
      hD0 _ _ (by omega) (homogeneousComponent_mem (0 + 1) P), add_zero, add_zero]
  · intro d hd
    by_contra hc
    apply hd
    have : P.totalDegree < d + 2 := by
      have : P.totalDegree < d := by simpa using hc
      omega
    simp [homogeneousComponent_eq_zero _ _ this]

/- English proof (translation)
Rewrite using `[Finsupp.prod_of_support_subset _ (s := insert i α.support) _ _ (by simp), Finsupp.prod_of_support_subset α (s := insert i α.support) (Finset.subset_insert _ _) _ (by simp), ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i α.support), ← Finset.mul_prod_erase _ _ (Finset.mem_ …`. Use `congr 1`. Simplify using `[Nat.factorial_succ]`. Use `Finset.prod_congr rfl fun j hj => ?_` and prove the remaining obligations. Establish `: j ≠ i` using `(Finset.mem_erase.mp hj).1`.

Simplify using `[Finsupp.single_apply, this.symm]`. Introduce `j hj`. Distinguish the cases in `h : j = i`. Simplify using `[h]`. Use `Finsupp.mem_support_iff.mp hj` as an intermediate fact.

Simplify using `[Finsupp.single_apply, Ne.symm h] at this`. Simplify using `[this]`.
-/
theorem prod_factorial_add_single [DecidableEq σ] (i : σ) (α : σ →₀ ℕ) :
    (α + Finsupp.single i 1).prod (fun _ k => (k.factorial : ℂ)) =
      ((α i : ℂ) + 1) * α.prod (fun _ k => (k.factorial : ℂ)) := by
  rw [Finsupp.prod_of_support_subset _ (s := insert i α.support) _ _ (by simp),
    Finsupp.prod_of_support_subset α (s := insert i α.support) (Finset.subset_insert _ _) _ (by simp),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i α.support),
    ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self i α.support), ← mul_assoc]
  · congr 1
    · simp [Nat.factorial_succ]
    · refine Finset.prod_congr rfl fun j hj => ?_
      have : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [Finsupp.single_apply, this.symm]
  · intro j hj
    by_cases h : j = i
    · simp [h]
    · have := Finsupp.mem_support_iff.mp hj
      simp [Finsupp.single_apply, Ne.symm h] at this
      simp [this]

/- English proof (translation)
Establish `key : ∀ α β : σ →₀ ℕ, inner ℂ (ι (X i * monomial α 1)) (ι (monomial β 1)) = inner ℂ (ι (monomial α 1)) (ι (pderiv i (monomial β (1 : ℂ))))`. Introduce `α β`. Establish `h1 : (X i : MvPolynomial σ ℂ) * monomial α 1 = monomial (α + Finsupp.single i 1) 1`. Rewrite using `[X, monomial_mul, add_comm, one_mul]`. Establish `h2 : pderiv i (monomial β (1 : ℂ)) = ((β i : ℕ) : ℂ) • monomial (β - Finsupp.single i 1) (1 : ℂ)`.

Rewrite using `[pderiv_monomial, smul_monomial]`. Simplify using the standard rewrite rules. Rewrite using `[h1, h2, map_smul, inner_smul_right, hι, hι]`. Distinguish the cases in `h : α + Finsupp.single i 1 = β`. Substitute `h` using the available equality.

Rewrite using `[if_pos rfl, if_pos (by simp), prod_factorial_add_single]`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Distinguish the cases in `h0 : β i = 0`. Simplify using `[h0]`.

Rewrite using `[if_neg, mul_zero]`. Introduce `h'`. Apply `h` to reduce the goal to its premises. Rewrite using `[h']`. Use extensionality with `j`.

Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Simplify using `[Finsupp.single_apply, Ne.symm hj]`.

Establish `hm : ∀ (α : σ →₀ ℕ) (c : ℂ), (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1`. Introduce `α c`. Rewrite using `[smul_monomial]`. Simplify using the standard rewrite rules. Proceed by induction on `P using MvPolynomial.induction_on' with`.

Consider the case `add P P' h h' => simp only [mul_add, map_add, inner_add_left, h, h']`. Consider the case `monomial α a`. Proceed by induction on `Q using MvPolynomial.induction_on' with`. Consider the case `add Q Q' h h' => simp only [map_add, inner_add_right, h, h']`. Consider the case `monomial β b`.

Rewrite using `[hm α a, hm β b, mul_smul_comm, Derivation.map_smul]`. Simplify using `only [map_smul, inner_smul_left, inner_smul_right, key]`.
-/
theorem inner_X_mul [DecidableEq σ] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) (i : σ) (P Q : MvPolynomial σ ℂ) :
    inner ℂ (ι (X i * P)) (ι Q) = inner ℂ (ι P) (ι (pderiv i Q)) := by
  have key : ∀ α β : σ →₀ ℕ, inner ℂ (ι (X i * monomial α 1)) (ι (monomial β 1)) =
      inner ℂ (ι (monomial α 1)) (ι (pderiv i (monomial β (1 : ℂ)))) := by
    intro α β
    have h1 : (X i : MvPolynomial σ ℂ) * monomial α 1 = monomial (α + Finsupp.single i 1) 1 := by
      rw [X, monomial_mul, add_comm, one_mul]
    have h2 : pderiv i (monomial β (1 : ℂ)) =
        ((β i : ℕ) : ℂ) • monomial (β - Finsupp.single i 1) (1 : ℂ) := by
      rw [pderiv_monomial, smul_monomial]; simp
    rw [h1, h2, map_smul, inner_smul_right, hι, hι]
    by_cases h : α + Finsupp.single i 1 = β
    · subst h
      rw [if_pos rfl, if_pos (by simp), prod_factorial_add_single]
      simp
    · rw [if_neg h]
      by_cases h0 : β i = 0
      · simp [h0]
      · rw [if_neg, mul_zero]
        intro h'
        apply h
        rw [h']
        ext j
        by_cases hj : j = i
        · subst hj; simp; omega
        · simp [Finsupp.single_apply, Ne.symm hj]
  have hm : ∀ (α : σ →₀ ℕ) (c : ℂ), (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    intro α c; rw [smul_monomial]; simp
  induction P using MvPolynomial.induction_on' with
  | add P P' h h' => simp only [mul_add, map_add, inner_add_left, h, h']
  | monomial α a =>
    induction Q using MvPolynomial.induction_on' with
    | add Q Q' h h' => simp only [map_add, inner_add_right, h, h']
    | monomial β b =>
      rw [hm α a, hm β b, mul_smul_comm, Derivation.map_smul]
      simp only [map_smul, inner_smul_left, inner_smul_right, key]

end General

section Lines
variable {p q r s : ℕ}

def upOp (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', (if linePos l then M l l' else 0) • LinearMap.mulLeft ℂ (X l * X l')

def downOp (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) : Module.End ℂ (Pol p q r s) :=
  ∑ l, ∑ l', (if linePos l then 0 else -M l l') •
    ((pderiv l).toLinearMap * (pderiv l').toLinearMap : Module.End ℂ (Pol p q r s))

/- English proof (translation)
Establish `hP' : P.IsHomogeneous d` using `hP`. Unfold `omE`. Rewrite using `[LinearMap.add_apply]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations. Consider the cases of `hl : linePos l`.

Establish `hl' : linePos l' = false` using `h ▸ hl`. Simplify using `only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]`. Use `Submodule.neg_mem _ ?_` and prove the remaining obligations. Use `((isHomogeneous_X ℂ l').mul hP').pderiv (i := l)` as an intermediate fact. Rewrite `this` using `[show 1 + d - 1 = d by omega]`.

Conclude with `this`. Establish `hl' : linePos l' = true` using `h ▸ hl`. Simplify using `only [raiB, lowB, hl, hl', if_true]`. Use `show (X l * pderiv l' P).IsHomogeneous d`. Break down `d with _ | d` into its components or cases.

Rewrite using `[pderiv_eq_zero_of_deg_zero hP', mul_zero]`. Conclude with `isHomogeneous_zero _ _ _`. Use `(isHomogeneous_X ℂ l).mul (hP'.pderiv (i := l'))` as an intermediate fact. Rewrite `this` using `[show 1 + (d + 1 - 1) = d + 1 by omega]`. Conclude with `this`.

Use `split_ifs`. Conclude with `Submodule.smul_mem _ _ hP`. Conclude with `Submodule.zero_mem _`.
-/
theorem omE_mem_homog {l l' : Ln p q r s} (h : linePos l = linePos l') {d : ℕ} {P : Pol p q r s}
    (hP : P ∈ homog (Ix p q × Ix r s) d) : omE l l' P ∈ homog (Ix p q × Ix r s) d := by
  have hP' : P.IsHomogeneous d := hP
  unfold omE
  rw [LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · cases hl : linePos l
    · have hl' : linePos l' = false := h ▸ hl
      simp only [raiB, lowB, hl, hl', Bool.false_eq_true, if_false]
      refine Submodule.neg_mem _ ?_
      have := ((isHomogeneous_X ℂ l').mul hP').pderiv (i := l)
      rw [show 1 + d - 1 = d by omega] at this
      exact this
    · have hl' : linePos l' = true := h ▸ hl
      simp only [raiB, lowB, hl, hl', if_true]
      show (X l * pderiv l' P).IsHomogeneous d
      rcases d with _ | d
      · rw [pderiv_eq_zero_of_deg_zero hP', mul_zero]; exact isHomogeneous_zero _ _ _
      · have := (isHomogeneous_X ℂ l).mul (hP'.pderiv (i := l'))
        rw [show 1 + (d + 1 - 1) = d + 1 by omega] at this
        exact this
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

/- English proof (translation)
Rewrite using `[omAct_apply, LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.sum_apply]`. Use `Submodule.sum_mem _ fun l' _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : linePos l = linePos l'`.

Conclude with `Submodule.smul_mem _ _ (omE_mem_homog h hP)`. Simplify using `[hM l l' h]`.
-/
theorem omAct_mem_homog {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l ≠ linePos l' → M l l' = 0) {d : ℕ} {P : Pol p q r s}
    (hP : P ∈ homog (Ix p q × Ix r s) d) : omAct p q r s M P ∈ homog (Ix p q × Ix r s) d := by
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  by_cases h : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (omE_mem_homog h hP)
  · simp [hM l l' h]

/- English proof (translation)
Rewrite using `[omAct_apply, upOp, downOp, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l' _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : linePos l = linePos l'`.

Simplify using `[hM l l' h]`. Establish `hne : l ≠ l'` using `fun e => h (e ▸ rfl)`. Consider the cases of `hl : linePos l`. Establish `hl' : linePos l' = true` using `by simpa [hl] using h`. Simplify using `[omE, raiB, lowB, hl, hl', hne]`.

Establish `hl' : linePos l' = false` using `by simpa [hl] using h`. Simplify using `only [omE, raiB, lowB, hl, hl', hne, if_true, if_false, Bool.false_eq_true, add_zero, zero_smul]`. Use `congr 1`. Use `ext1 P`. Use `ext1`.

Simplify using `[mul_assoc]`.
-/
theorem omAct_eq_up_add_down {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) :
    omAct p q r s M = upOp M + downOp M := by
  rw [omAct_apply, upOp, downOp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l' _ => ?_
  by_cases h : linePos l = linePos l'
  · simp [hM l l' h]
  · have hne : l ≠ l' := fun e => h (e ▸ rfl)
    cases hl : linePos l
    · have hl' : linePos l' = true := by simpa [hl] using h
      simp [omE, raiB, lowB, hl, hl', hne]
    · have hl' : linePos l' = false := by simpa [hl] using h
      simp only [omE, raiB, lowB, hl, hl', hne, if_true, if_false, Bool.false_eq_true, add_zero,
        zero_smul]
      congr 1
      ext1 P
      ext1
      simp [mul_assoc]

/- English proof (translation)
Simplify using `only [upOp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply]`.
-/
theorem upOp_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    upOp M P = ∑ l, ∑ l', (if linePos l then M l l' else 0) • (X l * X l' * P) := by
  simp only [upOp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply]

/- English proof (translation)
Simplify using `only [downOp, LinearMap.sum_apply, LinearMap.smul_apply]`. Both sides reduce to the same expression.
-/
theorem downOp_apply (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    downOp M P = ∑ l, ∑ l', (if linePos l then 0 else -M l l') • pderiv l (pderiv l' P) := by
  simp only [downOp, LinearMap.sum_apply, LinearMap.smul_apply]
  rfl

/- English proof (translation)
Rewrite using `[upOp_apply]`. Use `Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Use `((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP` as an intermediate fact. Rewrite `this` using `[show 1 + 1 + d = d + 2 by omega]`. Conclude with `this`.
-/
theorem upOp_mem (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (P : Pol p q r s)
    (hP : P ∈ homog (Ix p q × Ix r s) d) : upOp M P ∈ homog (Ix p q × Ix r s) (d + 2) := by
  rw [upOp_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => Submodule.smul_mem _ _ ?_
  have := ((isHomogeneous_X ℂ l).mul (isHomogeneous_X ℂ l')).mul hP
  rw [show 1 + 1 + d = d + 2 by omega] at this
  exact this

/- English proof (translation)
Rewrite using `[downOp_apply]`. Use `Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Conclude with `(IsHomogeneous.pderiv (i := l') hP).pderiv (i := l)`.
-/
theorem downOp_mem (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (P : Pol p q r s)
    (hP : P ∈ homog (Ix p q × Ix r s) d) : downOp M P ∈ homog (Ix p q × Ix r s) (d - 2) := by
  rw [downOp_apply]
  refine Submodule.sum_mem _ fun l _ => Submodule.sum_mem _ fun l' _ => Submodule.smul_mem _ _ ?_
  exact (IsHomogeneous.pderiv (i := l') hP).pderiv (i := l)

/- English proof (translation)
Rewrite using `[downOp_apply]`. Use `Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_` and prove the remaining obligations. Use `IsHomogeneous.pderiv (i := l') hP` as an intermediate fact. Rewrite `this` using `[show d - 1 = 0 by omega]`. Rewrite using `[pderiv_eq_zero_of_deg_zero this, smul_zero]`.
-/
theorem downOp_low (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (d : ℕ) (P : Pol p q r s) (hd : d < 2)
    (hP : P ∈ homog (Ix p q × Ix r s) d) : downOp M P = 0 := by
  rw [downOp_apply]
  refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun l' _ => ?_
  have := IsHomogeneous.pderiv (i := l') hP
  rw [show d - 1 = 0 by omega] at this
  rw [pderiv_eq_zero_of_deg_zero this, smul_zero]

/- English proof (translation)
Rewrite using `[omAct_eq_up_add_down hM]`. Conclude with `plusPart_add _ _ (upOp_mem M) (downOp_mem M) P`.
-/
theorem plusPart_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) (P : Pol p q r s) :
    plusPart (omAct p q r s M) P = upOp M P := by
  rw [omAct_eq_up_add_down hM]
  exact plusPart_add _ _ (upOp_mem M) (downOp_mem M) P

/- English proof (translation)
Rewrite using `[omAct_eq_up_add_down hM]`. Conclude with `minusPart_add _ _ (upOp_mem M) (downOp_mem M) (downOp_low M) P`.
-/
theorem minusPart_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) (P : Pol p q r s) :
    minusPart (omAct p q r s M) P = downOp M P := by
  rw [omAct_eq_up_add_down hM]
  exact minusPart_add _ _ (upOp_mem M) (downOp_mem M) (downOp_low M) P

/- English proof (translation)
Rewrite using `[plusPart_omAct hM, minusPart_omAct hM, omAct_eq_up_add_down hM, LinearMap.add_apply]`.
-/
theorem omAct_eq_parts {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) (P : Pol p q r s) :
    omAct p q r s M P = plusPart (omAct p q r s M) P + minusPart (omAct p q r s M) P := by
  rw [plusPart_omAct hM, minusPart_omAct hM, omAct_eq_up_add_down hM, LinearMap.add_apply]

/- English proof (translation)
Establish `hM' : ∀ l l', linePos l = linePos l' → Mᴴ l l' = 0`. Introduce `l l' h`. Simplify using `[hM l' l h.symm]`. Rewrite using `[plusPart_omAct hM, minusPart_omAct hM', upOp_apply, downOp_apply]`. Simplify using `only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, ← Finset.sum_neg_distrib]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc, inner_X_mul hι]`. Establish `e : inner ℂ (ι (X l' * P)) (ι (pderiv l Q)) = inner ℂ (ι P) (ι (pderiv l' (pderiv l Q)))` using `inner_X_mul hι _ _ _`. Rewrite using `[e]`.

Distinguish the cases in `h : linePos l = linePos l'`. Simplify using `[hM l l' h]`. Consider the cases of `hl : linePos l`. Establish `hl' : linePos l' = true` using `by simpa [hl] using h`. Simplify using `[hl']`.

Establish `hl' : linePos l' = false` using `by simpa [hl] using h`. Simplify using `[hl']`.
-/
theorem inner_plusPart_omAct {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ι : Pol p q r s →ₗ[ℂ] H} (hι : IsFockIP ι) {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (hM : ∀ l l', linePos l = linePos l' → M l l' = 0) (P Q : Pol p q r s) :
    inner ℂ (ι (plusPart (omAct p q r s M) P)) (ι Q) =
      - inner ℂ (ι P) (ι (minusPart (omAct p q r s Mᴴ) Q)) := by
  have hM' : ∀ l l', linePos l = linePos l' → Mᴴ l l' = 0 := by
    intro l l' h; simp [hM l' l h.symm]
  rw [plusPart_omAct hM, minusPart_omAct hM', upOp_apply, downOp_apply]
  simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    ← Finset.sum_neg_distrib]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l' _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc, inner_X_mul hι]
  have e : inner ℂ (ι (X l' * P)) (ι (pderiv l Q)) =
    inner ℂ (ι P) (ι (pderiv l' (pderiv l Q))) := inner_X_mul hι _ _ _
  rw [e]
  by_cases h : linePos l = linePos l'
  · simp [hM l l' h]
  · cases hl : linePos l
    · have hl' : linePos l' = true := by simpa [hl] using h
      simp [hl']
    · have hl' : linePos l' = false := by simpa [hl] using h
      simp [hl']

/- English proof (translation)
Establish `hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;>`. Simplify using `[Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Use extensionality with `a b`. Use `hZ b a` as an intermediate fact. Rewrite using `[conjR, adjZ, hJ, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]`.
-/
theorem conjR_of_isPC {Z : Mat p q} (hZ : IsPC Z) : conjR Z = Zᴴ := by
  have hJ : Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  ext a b
  have := hZ b a
  rw [conjR, adjZ, hJ, Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [linePos, sameBlock]`.
-/
theorem linePos_eq_iff_fst (a b : Ix p q) (c : Ix r s) :
    linePos ((a, c) : Ln p q r s) = linePos ((b, c) : Ln p q r s) ↔ sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [linePos, sameBlock]

/- English proof (translation)
Apply the tactic sequence `rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp [linePos, sameBlock]`.
-/
theorem linePos_eq_iff_snd (a : Ix p q) (c d : Ix r s) :
    linePos ((a, c) : Ln p q r s) = linePos ((a, d) : Ln p q r s) ↔ sameBlock c d := by
  rcases a with a | a <;> rcases c with c | c <;> rcases d with d | d <;> simp [linePos, sameBlock]

def kr1 (r s : ℕ) (Z : Mat p q) : Matrix (Ln p q r s) (Ln p q r s) ℂ :=
  Matrix.kroneckerMap (· * ·) Z (1 : Mat r s)

def kr2 (p q : ℕ) (Z : Mat r s) : Matrix (Ln p q r s) (Ln p q r s) ℂ :=
  Matrix.kroneckerMap (· * ·) (1 : Mat p q) Z

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct1_eq (Z : Mat p q) : fockAct1 p q r s Z = omAct p q r s (kr1 r s Z) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fockAct2_eq (Z : Mat r s) : fockAct2 p q r s Z = omAct p q r s (kr2 p q Z) := rfl

/- English proof (translation)
Use extensionality with `⟨a, c⟩ ⟨b, d⟩`. Distinguish the cases in `h : c = d`. Substitute `h` using the available equality. Simplify using `[kr1]`. Simplify using `[kr1, h, Ne.symm h]`.
-/
theorem lineMatrixKroneckerLeftFactor_conjTranspose (Z : Mat p q) : kr1 r s Zᴴ = (kr1 r s Z)ᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h : c = d
  · subst h; simp [kr1]
  · simp [kr1, h, Ne.symm h]

/- English proof (translation)
Use extensionality with `⟨a, c⟩ ⟨b, d⟩`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[kr2]`. Simplify using `[kr2, h, Ne.symm h]`.
-/
theorem lineMatrixKroneckerRightFactor_conjTranspose (Z : Mat r s) : kr2 p q Zᴴ = (kr2 p q Z)ᴴ := by
  ext ⟨a, c⟩ ⟨b, d⟩
  by_cases h : a = b
  · subst h; simp [kr2]
  · simp [kr2, h, Ne.symm h]

/- English proof (translation)
Take `⟨a, c⟩` from `l`. Take `⟨b, d⟩` from `l'`. Distinguish the cases in `e : c = d`. Substitute `e` using the available equality. Simplify using `[kr1, hZ a b (fun h' => h ((linePos_eq_iff_fst a b c).mpr h'))]`.

Simplify using `[kr1, e]`.
-/
theorem lineMatrixKroneckerLeftFactor_eq_zero_of_isKC {Z : Mat p q} (hZ : IsKC Z) (l l' : Ln p q r s) (h : linePos l ≠ linePos l') :
    kr1 r s Z l l' = 0 := by
  obtain ⟨a, c⟩ := l
  obtain ⟨b, d⟩ := l'
  by_cases e : c = d
  · subst e; simp [kr1, hZ a b (fun h' => h ((linePos_eq_iff_fst a b c).mpr h'))]
  · simp [kr1, e]

/- English proof (translation)
Take `⟨a, c⟩` from `l`. Take `⟨b, d⟩` from `l'`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using `[kr2, hZ c d (fun h' => h ((linePos_eq_iff_snd a c d).mpr h'))]`.

Simplify using `[kr2, e]`.
-/
theorem lineMatrixKroneckerRightFactor_eq_zero_of_isKC {Z : Mat r s} (hZ : IsKC Z) (l l' : Ln p q r s) (h : linePos l ≠ linePos l') :
    kr2 p q Z l l' = 0 := by
  obtain ⟨a, c⟩ := l
  obtain ⟨b, d⟩ := l'
  by_cases e : a = b
  · subst e; simp [kr2, hZ c d (fun h' => h ((linePos_eq_iff_snd a c d).mpr h'))]
  · simp [kr2, e]

/- English proof (translation)
Take `⟨a, c⟩` from `l`. Take `⟨b, d⟩` from `l'`. Distinguish the cases in `e : c = d`. Substitute `e` using the available equality. Simplify using `[kr1, hZ a b ((linePos_eq_iff_fst a b c).mp h)]`.

Simplify using `[kr1, e]`.
-/
theorem lineMatrixKroneckerLeftFactor_eq_zero_of_isPC {Z : Mat p q} (hZ : IsPC Z) (l l' : Ln p q r s) (h : linePos l = linePos l') :
    kr1 r s Z l l' = 0 := by
  obtain ⟨a, c⟩ := l
  obtain ⟨b, d⟩ := l'
  by_cases e : c = d
  · subst e; simp [kr1, hZ a b ((linePos_eq_iff_fst a b c).mp h)]
  · simp [kr1, e]

/- English proof (translation)
Take `⟨a, c⟩` from `l`. Take `⟨b, d⟩` from `l'`. Distinguish the cases in `e : a = b`. Substitute `e` using the available equality. Simplify using `[kr2, hZ c d ((linePos_eq_iff_snd a c d).mp h)]`.

Simplify using `[kr2, e]`.
-/
theorem lineMatrixKroneckerRightFactor_eq_zero_of_isPC {Z : Mat r s} (hZ : IsPC Z) (l l' : Ln p q r s) (h : linePos l = linePos l') :
    kr2 p q Z l l' = 0 := by
  obtain ⟨a, c⟩ := l
  obtain ⟨b, d⟩ := l'
  by_cases e : a = b
  · subst e; simp [kr2, hZ c d ((linePos_eq_iff_snd a c d).mp h)]
  · simp [kr2, e]

end Lines

/- English proof (translation)
Introduce `X p q r s`. Establish `hι` using `isFockIsometry_of_fockData (X.fock p q r s)`. Use `⟨fun Z hZ d P hP => omAct_mem_homog (lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hZ) hP, fun Z hZ d P hP => omAct_mem_homog (lineMatrixKroneckerRightFactor_eq_zero_of_isKC hZ) hP, fun Z hZ P => omAct_eq_parts (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) P, fun Z hZ P => o …` and prove the remaining obligations. Rewrite using `[conjR_of_isPC hZ]`. Simplify using `only [FockData.act1, fockAct1_eq, lineMatrixKroneckerLeftFactor_conjTranspose]`.

Conclude with `inner_plusPart_omAct hι (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) P Q`. Rewrite using `[conjR_of_isPC hZ]`. Simplify using `only [FockData.act2, fockAct2_eq, lineMatrixKroneckerRightFactor_conjTranspose]`. Conclude with `inner_plusPart_omAct hι (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ) P Q`.
-/
theorem degrees_and_adjoints : ∀ X : ProvA, admH1 X := by
  intro X p q r s
  have hι := isFockIsometry_of_fockData (X.fock p q r s)
  refine ⟨fun Z hZ d P hP => omAct_mem_homog (lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hZ) hP,
    fun Z hZ d P hP => omAct_mem_homog (lineMatrixKroneckerRightFactor_eq_zero_of_isKC hZ) hP,
    fun Z hZ P => omAct_eq_parts (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) P,
    fun Z hZ P => omAct_eq_parts (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ) P, fun Z hZ P Q => ?_, fun Z hZ P Q => ?_⟩
  · rw [conjR_of_isPC hZ]
    simp only [FockData.act1, fockAct1_eq, lineMatrixKroneckerLeftFactor_conjTranspose]
    exact inner_plusPart_omAct hι (lineMatrixKroneckerLeftFactor_eq_zero_of_isPC hZ) P Q
  · rw [conjR_of_isPC hZ]
    simp only [FockData.act2, fockAct2_eq, lineMatrixKroneckerRightFactor_conjTranspose]
    exact inner_plusPart_omAct hι (lineMatrixKroneckerRightFactor_eq_zero_of_isPC hZ) P Q

end GlobalTheory.FockDeg
