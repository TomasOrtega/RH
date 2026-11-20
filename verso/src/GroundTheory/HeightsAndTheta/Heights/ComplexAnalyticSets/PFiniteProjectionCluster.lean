import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteProjectionCluster
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelProper
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial Topology

noncomputable section

namespace FiniteProjectionCluster

variable {n d : ℕ}

/- English proof (translation)
Establish `h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0}`. Use extensionality with `x`. Simplify using `[zeroSet]`. Rewrite using `[h]`. Conclude with `isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const`.
-/
theorem isClosed_zeroSet (J : Ideal (MvPolynomial (Fin n) ℂ)) : IsClosed (zeroSet J) := by
  have h : zeroSet J = ⋂ q ∈ J, {x : Fin n → ℂ | eval x q = 0} := by
    ext x; simp [zeroSet]
  rw [h]
  exact isClosed_biInter fun q _ => isClosed_eq (MvPolynomial.continuous_eval q) continuous_const

/- English proof (translation)
Take `⟨P, hPm, hP⟩` from `hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))`. Use `⟨P, hPm, fun x hx => ?_⟩` and prove the remaining obligations. Establish `hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom` using `rfl`. Rewrite `hP` using `[hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem]`. Establish `h0` using `hx _ hP`.

Rewrite `h0` using `[Polynomial.hom_eval₂, eval_X]`. Establish `hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x)` using `RingHom.ext (FibreBound.eval_pullback A x)`. Rewrite `h0` using `[hcomp, Polynomial.eval₂_eq_eval_map]`. Conclude with `h0`.
-/
theorem exists_monic (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (j : Fin n) :
    ∃ P : Polynomial (MvPolynomial (Fin d) ℂ), P.Monic ∧
      ∀ x ∈ zeroSet J, (P.map (eval (A.mulVec x))).IsRoot (x j) := by
  obtain ⟨P, hPm, hP⟩ := hA.finite.to_isIntegral (Ideal.Quotient.mk J (X j))
  refine ⟨P, hPm, fun x hx => ?_⟩
  have hf : (projHom J A).toRingHom = (Ideal.Quotient.mk J).comp (pullback A).toRingHom := rfl
  rw [hf, ← Polynomial.hom_eval₂, Ideal.Quotient.eq_zero_iff_mem] at hP
  have h0 := hx _ hP
  rw [Polynomial.hom_eval₂, eval_X] at h0
  have hcomp : (eval x).comp (pullback A).toRingHom = eval (A.mulVec x) :=
    RingHom.ext (FibreBound.eval_pullback A x)
  rw [hcomp, Polynomial.eval₂_eq_eval_map] at h0
  exact h0

/- English proof (translation)
Use `choose P hPm hP using exists_monic J A hA`. Set `g : (Fin d → ℂ) → ℝ` to `fun y => ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)`. Establish `hg : Continuous g` using `continuous_finsetSum _ fun j _ => continuous_const.add (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)`. Take `⟨C, hC⟩` from `(isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn`. Use `⟨C, fun x hx hd => ?_⟩` and prove the remaining obligations.

Establish `hy : A.mulVec x ∈ Metric.closedBall c R` using `hd`. Establish `hgC : g (A.mulVec x) ≤ C` using `(Real.le_norm_self _).trans (hC _ hy)`. Use `(pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_` and prove the remaining obligations. Establish `hj` using `IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)`. Establish `hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤ g (A.mulVec x)` using `Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _)) (Finset.mem_univ j)`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_bound (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (c : Fin d → ℂ) (R : ℝ) :
    ∃ C : ℝ, ∀ x ∈ zeroSet J, dist (A.mulVec x) c ≤ R → ‖x‖ ≤ C := by
  choose P hPm hP using exists_monic J A hA
  let g : (Fin d → ℂ) → ℝ := fun y =>
    ∑ j, (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval y ((P j).coeff i)‖)
  have hg : Continuous g :=
    continuous_finsetSum _ fun j _ => continuous_const.add
      (continuous_finsetSum _ fun i _ => (MvPolynomial.continuous_eval _).norm)
  obtain ⟨C, hC⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun x hx hd => ?_⟩
  have hy : A.mulVec x ∈ Metric.closedBall c R := hd
  have hgC : g (A.mulVec x) ≤ C := (Real.le_norm_self _).trans (hC _ hy)
  refine (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hC _ hy))).2 fun j => ?_
  have hj := IndefiniteRowSideFullHecke.ComplexSets.norm_lt_of_isRoot_map_eval (hPm j) (A.mulVec x) (hP j x hx)
  have hle : (1 + ∑ i ∈ Finset.range (P j).natDegree, ‖eval (A.mulVec x) ((P j).coeff i)‖) ≤
      g (A.mulVec x) :=
    Finset.single_le_sum (f := fun j => 1 + ∑ i ∈ Finset.range (P j).natDegree,
      ‖eval (A.mulVec x) ((P j).coeff i)‖)
      (fun k _ => add_nonneg zero_le_one (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.mem_univ j)
  linarith

/- English proof (translation)
Use `choose P hPm hP using exists_monic J A hA`. Use `(Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a}) fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxA⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]`. Introduce `j`.

Rewrite using `[← hxA]`. Conclude with `hP j x hx`.
-/
theorem fibre_finite (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (hA : IsFiniteProjection J A) (y : Fin d → ℂ) :
    {x | x ∈ zeroSet J ∧ A.mulVec x = y}.Finite := by
  choose P hPm hP using exists_monic J A hA
  refine (Set.Finite.pi (t := fun j => {a | ((P j).map (eval y)).IsRoot a})
    fun j => Polynomial.finite_setOfPred_isRoot ((hPm j).map _).ne_zero).subset ?_
  rintro x ⟨hx, hxA⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_ofPred_eq]
  intro j
  rw [← hxA]
  exact hP j x hx

end FiniteProjectionCluster

open FiniteProjectionCluster in

/- English proof (translation)
Introduce `n d J A w U hA hw hU`. Establish `hcont : Continuous fun x : Fin n → ℂ => A.mulVec x` using `Continuous.matrix_mulVec continuous_const continuous_id`. Take `⟨C, hC⟩` from `exists_bound J A hA (A.mulVec w) 1`. Establish `hF` using `fibre_finite J A hA (A.mulVec w)`. Take `⟨ε0, hε0, hballU⟩` from `Metric.mem_nhds_iff.1 hU`.

Take `⟨ε, ⟨hε, hεlt⟩, hεF⟩` from `((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty`. Use `set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef`. Establish `hKc : IsCompact K`. Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations. Conclude with `((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const) continuous_const)).inter Metric.isClosed_sphere`.

Conclude with `(Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)`. Establish `hT : IsCompact (A.mulVec '' K)` using `hKc.image hcont`. Establish `hnot : A.mulVec w ∉ A.mulVec '' K`. Introduce and unpack `⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩`. Conclude with `hεF ⟨x, ⟨hx, hxA⟩, hxs⟩`.

Take `⟨r0, hr0, hr0T⟩` from `Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot`. Use `⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball, Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε, (Metric.ball_subset_ball hεlt.le).trans hballU, Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall h …` and prove the remaining obligations. Introduce and unpack `x ⟨hx, hxr⟩`. Establish `hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1` using `hxr`. Distinguish the cases in `h : dist x w < ε`.

Conclude with `Or.inl h`. Use `Or.inr fun hcb => ?_` and prove the remaining obligations. Establish `heq : dist x w = ε` using `le_antisymm hcb (not_lt.1 h)`. Establish `hxK : x ∈ K` using `⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩`. Conclude with `hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩`.

Use `(Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_` and prove the remaining obligations. Establish `hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1` using `hx.2`. Conclude with `mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))`.
-/
theorem FiniteProjectionCluster.proof : FiniteProjectionCluster.Statement := by
  intro n d J A w U hA hw hU
  have hcont : Continuous fun x : Fin n → ℂ => A.mulVec x :=
    Continuous.matrix_mulVec continuous_const continuous_id
  obtain ⟨C, hC⟩ := exists_bound J A hA (A.mulVec w) 1
  have hF := fibre_finite J A hA (A.mulVec w)
  obtain ⟨ε0, hε0, hballU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε, ⟨hε, hεlt⟩, hεF⟩ :=
    ((Set.Ioo_infinite hε0).sdiff (hF.image fun x => dist x w)).nonempty
  set K := zeroSet J ∩ {x | dist (A.mulVec x) (A.mulVec w) ≤ 1} ∩ Metric.sphere w ε with hKdef
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact ((isClosed_zeroSet J).inter (isClosed_le (hcont.dist continuous_const)
        continuous_const)).inter Metric.isClosed_sphere
    · exact (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx =>
        mem_closedBall_zero_iff.2 (hC x hx.1.1 hx.1.2)
  have hT : IsCompact (A.mulVec '' K) := hKc.image hcont
  have hnot : A.mulVec w ∉ A.mulVec '' K := by
    rintro ⟨x, ⟨⟨hx, _⟩, hxs⟩, hxA⟩
    exact hεF ⟨x, ⟨hx, hxA⟩, hxs⟩
  obtain ⟨r0, hr0, hr0T⟩ := Metric.isOpen_iff.1 hT.isClosed.isOpen_compl _ hnot
  refine ⟨min r0 1, Metric.ball w ε, (Metric.closedBall w ε)ᶜ, lt_min hr0 one_pos, Metric.isOpen_ball,
    Metric.isClosed_closedBall.isOpen_compl, Metric.mem_ball_self hε,
    (Metric.ball_subset_ball hεlt.le).trans hballU,
    Set.disjoint_left.2 fun x hx hx' => hx' (Metric.ball_subset_closedBall hx), ?_, ?_⟩
  · rintro x ⟨hx, hxr⟩
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hxr
    by_cases h : dist x w < ε
    · exact Or.inl h
    · refine Or.inr fun hcb => ?_
      have heq : dist x w = ε := le_antisymm hcb (not_lt.1 h)
      have hxK : x ∈ K := ⟨⟨hx, hxr'.le.trans (min_le_right _ _)⟩, heq⟩
      exact hr0T (Metric.mem_ball.2 (hxr'.trans_le (min_le_left _ _))) ⟨x, hxK, rfl⟩
  · refine (Metric.isBounded_closedBall (x := 0) (r := C)).subset fun x hx => ?_
    have hxr' : dist (A.mulVec x) (A.mulVec w) < min r0 1 := hx.2
    exact mem_closedBall_zero_iff.2 (hC x hx.1 (hxr'.le.trans (min_le_right _ _)))

end

end GroundTheory.Heights₂.Heights.ComplexSets
