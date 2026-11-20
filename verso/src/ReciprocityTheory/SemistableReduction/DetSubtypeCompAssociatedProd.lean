import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import Lemmata.GeneralBFactLast.Imports
import Lemmata.GeneralBFactTail.Imports

namespace ReciprocityTheory.MultiplicativeHeights

open Module Submodule

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)`.
-/
theorem det_subtype_comp_associated_prod {R M : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (b : Basis ι R M) (N : Submodule R M)
    (h : finrank R N = finrank R M) (e : M ≃ₗ[R] N) :
    Associated (LinearMap.det (N.subtype ∘ₗ (e : M →ₗ[R] N)))
      (∏ i, smithNormalFormCoeffs b h i) := by
  first | exact Bl.general_b_fact_tail.goal1 .. | (apply Bl.general_b_fact_tail.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_tail.goal1 <;> assumption)

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)`.
-/
theorem addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by
  first | exact Bl.general_b_fact'''''''.goal1 .. | (apply Bl.general_b_fact'''''''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact'''''''.goal1 <;> assumption)

/- English proof (translation)
Introduce `O B _ _ _ _ _ _ _ _ g hg`. Establish `: Module.Free O B` using `Module.free_iff_isTorsionFree.mpr inferInstance`. Use `set b := Module.Free.chooseBasis O B`. Use `set I : Ideal B := Ideal.span ({g} : Set B)`. Establish `hI : I ≠ ⊥` using `by simpa [I] using hg`.

Establish `h` using `Ideal.finrank_eq_finrank b I hI`. Establish `hlen : Module.length O (B ⧸ I) = ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i)`. Rewrite using `[(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Ring.ord_eq_addVal]`.

Both sides reduce to the same expression. Establish `hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i)`. Rewrite using `[Algebra.norm_apply]`. Establish `key` using `det_subtype_comp_associated_prod b (I.restrictScalars O) h (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))`. Use `key using 2` and compare the differences between its conclusion and the goal.

Use `b.ext fun i => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]`. Establish `h1` using `Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i`. Use `Eq.trans ?_ (congrArg Subtype.val h1).symm` and prove the remaining obligations. Rewrite using `[Equiv.refl_apply, Ideal.basisSpanSingleton_apply]`.

Both sides reduce to the same expression. Rewrite using `[hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]`. Conclude with `Ring.ord_eq_of_associated hdet`.
-/
theorem gaugeSplitting_holds : NormLengthStatement := by
  intro O B _ _ _ _ _ _ _ _ g hg
  classical
  have : Module.Free O B := Module.free_iff_isTorsionFree.mpr inferInstance
  set b := Module.Free.chooseBasis O B
  set I : Ideal B := Ideal.span ({g} : Set B)
  have hI : I ≠ ⊥ := by simpa [I] using hg
  have h := Ideal.finrank_eq_finrank b I hI
  have hlen : Module.length O (B ⧸ I) =
      ∑ i, IsDiscreteValuationRing.addVal O (smithNormalFormCoeffs b h i) := by
    rw [(Ideal.quotientEquivPiSpan I b hI).length_eq, Module.length_pi_of_fintype]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Ring.ord_eq_addVal]
    rfl
  have hdet : Associated (Algebra.norm O g) (∏ i, smithNormalFormCoeffs b h i) := by
    rw [Algebra.norm_apply]
    have key := det_subtype_comp_associated_prod b (I.restrictScalars O) h
      (b.equiv (Ideal.basisSpanSingleton b hg) (Equiv.refl _))
    convert key using 2
    refine b.ext fun i => ?_
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
    have h1 := Basis.equiv_apply (b := b) (b' := Ideal.basisSpanSingleton b hg) (e := Equiv.refl _) i
    refine Eq.trans ?_ (congrArg Subtype.val h1).symm
    rw [Equiv.refl_apply, Ideal.basisSpanSingleton_apply]
    rfl
  rw [hlen, ← addVal_prod, ← Ring.ord_eq_addVal, ← Ring.ord_eq_addVal]
  exact Ring.ord_eq_of_associated hdet

end ReciprocityTheory.MultiplicativeHeights
