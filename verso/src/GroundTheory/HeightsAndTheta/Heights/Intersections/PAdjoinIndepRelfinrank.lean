import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StAdjoinIndepRelfinrank
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open IntermediateField IntermediateField.algebraAdjoinAdjoin Module

/- English proof (translation)
Introduce `F Ω _ _ _ L₀ L ι t hle ht`. Use `set L' : IntermediateField L₀ Ω := extendScalars hle with hL'`. Use `set A : IntermediateField L₀ Ω := adjoin L₀ (Set.range t) with hA`. Establish `ht' : AlgebraicIndependent L' t` using `ht`. Set `b` to `Module.Free.chooseBasis L₀ L'`.

Establish `hR : LinearIndependent (Algebra.adjoin L₀ (Set.range t)) (algebraMap L' Ω ∘ b)`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Establish `hmem : ∀ j, ∃ p : MvPolynomial ι L₀, MvPolynomial.aeval t p = (g j : Ω)` using `fun j => by`. Establish `: (g j : Ω) ∈ (MvPolynomial.aeval t : MvPolynomial ι L₀ →ₐ[L₀] Ω).range`.

Rewrite using `[← Algebra.adjoin_range_eq_range_aeval]`. Conclude with `(g j).2`. Take `⟨p, hp⟩` from `this`. Conclude with `⟨p, hp⟩`. Use `choose p hp using hmem`.

Use `set q : MvPolynomial ι L' := ∑ j ∈ s, MvPolynomial.C (b j) * MvPolynomial.map (algebraMap L₀ L') (p j) with hq`. Establish `hq0 : q = 0`. Apply `ht'.eq_zero_of_aeval_eq_zero` to reduce the goal to its premises. Rewrite using `[hq, map_sum]`. Rewrite using `[← hg]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap, hp, Subalgebra.smul_def, Function.comp_apply, mul_comm]`. Both sides reduce to the same expression. Establish `hcoef : ∀ m, ∀ j ∈ s, MvPolynomial.coeff m (p j) = 0`. Introduce `m`.

Establish `h` using `congrArg (MvPolynomial.coeff m) hq0`. Rewrite `h` using `[hq, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero]`. Simplify using `only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h`. Establish `hb` using `(linearIndependent_iff'.mp b.linearIndependent) s (fun j => MvPolynomial.coeff m (p j))`. Apply `hb` to reduce the goal to its premises.

Rewrite using `[← h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, mul_comm]`. Establish `hpi : p i = 0` using `MvPolynomial.ext _ _ fun m => hcoef m i hi`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[← hp i, hpi, map_zero]`. Both sides reduce to the same expression. Establish `hK : LinearIndependent A (algebraMap L' Ω ∘ b)` using `(LinearIndependent.iff_fractionRing (Algebra.adjoin L₀ (Set.range t)) A).mp hR`. Establish `hdisj : A.LinearDisjoint L'` using `LinearDisjoint.of_basis_right' b hK`. Establish `hlow : A.restrictScalars F = L₀ ⊔ adjoin F (Set.range t)`.

Rewrite using `[hA, restrictScalars_adjoin_eq_sup]`. Establish `hle' : A ≤ (adjoin L' (A : Set Ω)).restrictScalars L₀` using `subset_adjoin L' (A : Set Ω)`. Establish `hup : ((adjoin L' (A : Set Ω)).restrictScalars L₀).restrictScalars F = L ⊔ adjoin F (Set.range t)`. Use `(restrictScalars_adjoin_eq_sup F L (A : Set Ω)).trans ?_` and prove the remaining obligations. Establish `hAF : adjoin F (A : Set Ω) = L₀ ⊔ adjoin F (Set.range t)`.

Rewrite using `[← hlow]`. Conclude with `adjoin_self F (A.restrictScalars F)`. Rewrite using `[hAF, ← sup_assoc, sup_eq_left.mpr hle]`. Establish `hrel : IntermediateField.relfinrank (L₀ ⊔ adjoin F (Set.range t)) (L ⊔ adjoin F (Set.range t)) = finrank A (extendScalars hle')`. Rewrite using `[← hlow, ← hup]`.

Conclude with `relfinrank_eq_finrank_of_le hle'`. Rewrite using `[hrel, relfinrank_eq_finrank_of_le hle]`. Distinguish the cases in `hfin : Module.Finite L₀ L'`. Establish `: Algebra.IsAlgebraic L₀ L'` using `Algebra.IsAlgebraic.of_finite L₀ L'`. Use `hdisj.adjoin_rank_eq_rank_right_of_isAlgebraic_right` as an intermediate fact.

Conclude with `congrArg Cardinal.toNat this`. Rewrite using `[finrank_of_not_finite hfin, finrank_of_not_finite]`. Introduce `hfin'`. Apply `hfin` to reduce the goal to its premises. Set `v : _ → extendScalars hle'` to `fun j => ⟨algebraMap L' Ω (b j), by`.

Conclude with `IntermediateField.algebraMap_mem (adjoin L' (A : Set Ω)) (b j)⟩`. Establish `hv : LinearIndependent A v`. Apply `LinearIndependent.of_comp (extendScalars hle').val.toLinearMap` to reduce the goal to its premises. Conclude with `hK`. Use `hv.finite_of_isNoetherian` as an intermediate fact.

Conclude with `Module.Finite.of_basis b`.
-/
theorem AdjoinIndepRelfinrank.proof : AdjoinIndepRelfinrank.Statement := by
  intro F Ω _ _ _ L₀ L ι t hle ht
  set L' : IntermediateField L₀ Ω := extendScalars hle with hL'
  set A : IntermediateField L₀ Ω := adjoin L₀ (Set.range t) with hA
  have ht' : AlgebraicIndependent L' t := ht

  let b := Module.Free.chooseBasis L₀ L'

  have hR : LinearIndependent (Algebra.adjoin L₀ (Set.range t)) (algebraMap L' Ω ∘ b) := by
    rw [linearIndependent_iff']
    intro s g hg i hi
    have hmem : ∀ j, ∃ p : MvPolynomial ι L₀, MvPolynomial.aeval t p = (g j : Ω) := fun j => by
      have : (g j : Ω) ∈ (MvPolynomial.aeval t : MvPolynomial ι L₀ →ₐ[L₀] Ω).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval]
        exact (g j).2
      obtain ⟨p, hp⟩ := this
      exact ⟨p, hp⟩
    choose p hp using hmem
    set q : MvPolynomial ι L' :=
      ∑ j ∈ s, MvPolynomial.C (b j) * MvPolynomial.map (algebraMap L₀ L') (p j) with hq
    have hq0 : q = 0 := by
      apply ht'.eq_zero_of_aeval_eq_zero
      rw [hq, map_sum]
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_map_algebraMap, hp, Subalgebra.smul_def,
        Function.comp_apply, mul_comm]
      rfl
    have hcoef : ∀ m, ∀ j ∈ s, MvPolynomial.coeff m (p j) = 0 := by
      intro m
      have h := congrArg (MvPolynomial.coeff m) hq0
      rw [hq, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at h
      simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map] at h
      have hb := (linearIndependent_iff'.mp b.linearIndependent) s (fun j => MvPolynomial.coeff m (p j))
      apply hb
      rw [← h]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hpi : p i = 0 := MvPolynomial.ext _ _ fun m => hcoef m i hi
    apply Subtype.ext
    rw [← hp i, hpi, map_zero]
    rfl
  have hK : LinearIndependent A (algebraMap L' Ω ∘ b) :=
    (LinearIndependent.iff_fractionRing (Algebra.adjoin L₀ (Set.range t)) A).mp hR
  have hdisj : A.LinearDisjoint L' := LinearDisjoint.of_basis_right' b hK

  have hlow : A.restrictScalars F = L₀ ⊔ adjoin F (Set.range t) := by
    rw [hA, restrictScalars_adjoin_eq_sup]
  have hle' : A ≤ (adjoin L' (A : Set Ω)).restrictScalars L₀ := subset_adjoin L' (A : Set Ω)
  have hup : ((adjoin L' (A : Set Ω)).restrictScalars L₀).restrictScalars F =
      L ⊔ adjoin F (Set.range t) := by
    refine (restrictScalars_adjoin_eq_sup F L (A : Set Ω)).trans ?_
    have hAF : adjoin F (A : Set Ω) = L₀ ⊔ adjoin F (Set.range t) := by
      rw [← hlow]
      exact adjoin_self F (A.restrictScalars F)
    rw [hAF, ← sup_assoc, sup_eq_left.mpr hle]
  have hrel : IntermediateField.relfinrank (L₀ ⊔ adjoin F (Set.range t)) (L ⊔ adjoin F (Set.range t)) =
      finrank A (extendScalars hle') := by
    rw [← hlow, ← hup]
    exact relfinrank_eq_finrank_of_le hle'
  rw [hrel, relfinrank_eq_finrank_of_le hle]
  by_cases hfin : Module.Finite L₀ L'
  · have : Algebra.IsAlgebraic L₀ L' := Algebra.IsAlgebraic.of_finite L₀ L'
    have := hdisj.adjoin_rank_eq_rank_right_of_isAlgebraic_right
    exact congrArg Cardinal.toNat this
  · rw [finrank_of_not_finite hfin, finrank_of_not_finite]
    intro hfin'
    apply hfin
    let v : _ → extendScalars hle' := fun j => ⟨algebraMap L' Ω (b j), by
      exact IntermediateField.algebraMap_mem (adjoin L' (A : Set Ω)) (b j)⟩
    have hv : LinearIndependent A v := by
      apply LinearIndependent.of_comp (extendScalars hle').val.toLinearMap
      exact hK
    have := hv.finite_of_isNoetherian
    exact Module.Finite.of_basis b
end GroundTheory.Heights₂.Heights.Inter
