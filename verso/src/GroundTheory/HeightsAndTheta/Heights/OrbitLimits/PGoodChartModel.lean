import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartModel
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartZeroSet
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StGoodChartDim
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteProjHomInjective
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeAvoidsFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

namespace GoodChartModel

/- English proof (translation)
Break down `hr.eq_or_lt with h | h` into its components or cases. Rewrite using `[← h]`. Conclude with `Ideal.subset_span ⟨f, hf, rfl⟩`. Rewrite using `[homogeneousComponent_eq_zero (n := r) (φ := f) h]`. Conclude with `zero_mem _`.
-/
theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

/- English proof (translation)
Simplify using `[linPoly, Matrix.mulVec, dotProduct]`.
-/
theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

/- English proof (translation)
Take `⟨r, hr, G, hG, hrel⟩` from `segre_rel hP.2.1.2.1 Ψ hΨ (σ a)`. Use `set A := chartProjMatrix σ Ψ with hA`. Set `Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ` to `fun j => rename σ.symm (G j)`. Establish `hGx : ∀ j, (Gx j).totalDegree ≤ r - 1` using `fun j => (totalDegree_rename_le _ _).trans (hG j)`. Set `f : MvPolynomial (Fin m) ℂ` to `X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)`.

Establish `hfJ : f ∈ J`. Use `hJ ?_` and prove the remaining obligations. Rewrite using `[projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]`. Introduce and unpack `_ ⟨z, hz, hz1, rfl⟩`. Establish `hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z`.

Use function extensionality and compare the values at `i'`. Simplify using the standard rewrite rules. Establish `h` using `hrel z hz`. Rewrite `h` using `[Fin.sum_univ_succ, hz1, one_mul]`. Express the relevant statement in the definitionally equal form `eval (fun a => segre z (σ a)) f = 0`.

Simplify using `only [f, Gx, map_sub, map_add, map_pow, map_sum, map_mul, eval_X, eval_rename, hw, eval_linPoly, hA, chartProjMatrix_mulVec]`. Rewrite using `[h]`. Simplify using `[Equiv.apply_symm_apply, mul_comm]`. Establish `hdeg : f.totalDegree ≤ r`. Use `(totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)` and prove the remaining obligations.

Use `(totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)` and prove the remaining obligations. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Establish `h1` using `hGx j.succ`. Establish `h2` using `(isHomogeneous_linPoly A j).totalDegree_le`.

Use linear arithmetic over natural numbers and integers. Establish `h1 : 1 ≤ r` using `hr`. Establish `hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r`. Rewrite using `[homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)), if_pos rfl]`. Establish `h0 : homogeneousComponent r (Gx 0) = 0` using `homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)`.

Establish `hcomp : homogeneousComponent r f = X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j`. Simplify using `only [f, map_sub, map_add, map_sum, hX, h0, zero_add, homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]`. Establish `hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈ leadIdeal J ⊔ linIdeal A` using `add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg)) (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))`. Rewrite `hmem` using `[hcomp, sub_add_cancel]`. Conclude with `⟨r, hmem⟩`.
-/
theorem pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : projChartIdeal P σ Ψ ≤ J) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine hJ ?_
    rw [projChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hz1, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hz1, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    simp only [f, Gx, map_sub, map_add, map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    simp only [f, map_sub, map_add, map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

end GoodChartModel

/- English proof (translation)
Introduce `K _ ι _ P e m σ Ψ hP hΨ`. Use `⟨hZ K ι P e m σ Ψ hP.2.1.2.1, fun J hJ => ?_⟩` and prove the remaining obligations. Establish `hdim` using `hD K ι P e m σ Ψ hP J hJ`. Establish `hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite`. Establish `hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical`.

Use `Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)` and prove the remaining obligations. Take `⟨r, hr⟩` from `GoodChartModel.pow_mem hP hΨ hJ.1.2 a`. Conclude with `⟨r, hr⟩`. Take `⟨N, hN⟩` from `Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)`. Conclude with `ConeAvoidsFinite.proof m e N J _ hN`.

Conclude with `⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩`.
-/
theorem GoodChartModel.proof (hZ : GoodChartZeroSet.Statement) (hD : GoodChartDim.Statement) :
    GoodChartModel.Statement := by
  intro K _ ι _ P e m σ Ψ hP hΨ
  refine ⟨hZ K ι P e m σ Ψ hP.2.1.2.1, fun J hJ => ?_⟩
  have hdim := hD K ι P e m σ Ψ hP J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := GoodChartModel.pow_mem hP hΨ hJ.1.2 a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨hdim, ⟨FiniteProjHomInjective.proof m e J _ hJ.1.1 hdim hfin, hfin⟩⟩

end GroundTheory.Heights₂.Heights
