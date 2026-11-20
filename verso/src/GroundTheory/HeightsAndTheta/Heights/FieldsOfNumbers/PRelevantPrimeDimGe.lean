import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsDegreeBound
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

/- English proof (translation)
Introduce `F _ K _ _ ι _ P hP`. Use `hP.isPrime` as an intermediate fact. Use `choose i hi using hP.relevant`. Set `j : K → (Σ k, ι k)` to `fun k => ⟨k, i k⟩`. Set `x : K → MRing ι F ⧸ P` to `fun k => Ideal.Quotient.mk P (X (j k))`.

Establish `key : ∀ p : MvPolynomial K F, aeval x p = Ideal.Quotient.mk P (rename j p)`. Introduce `p`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a`. Simplify using `only [aeval_C, rename_C]`.

Both sides reduce to the same expression. Consider the case `add p q hp hq => simp [hp, hq]`. Consider the case `mul_X p k hp => simp [hp, x]`. Establish `hw : ∀ β : K →₀ ℕ, Finsupp.weight (blockWeight ι) (Finsupp.mapDomain j β) = ⇑β`. Introduce `β`.

Rewrite using `[Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]`. Use function extensionality and compare the values at `k'`. Simplify using `[Finsupp.sum, Finset.sum_apply, blockWeight, j, Pi.single_apply]`. Conclude with `fun h => h.symm`. Establish `hind : AlgebraicIndependent F x`.

Rewrite using `[algebraicIndependent_iff]`. Introduce `G hG`. Rewrite `hG` using `[key]`. Establish `hmem : rename j G ∈ P` using `Ideal.Quotient.eq_zero_iff_mem.mp hG`. Use extensionality with `α`.

Rewrite using `[coeff_zero]`. Establish `hcomp` using `hP.multiHomog _ hmem ⇑α`. Establish `hsum : rename j G = ∑ β ∈ G.support, monomial (Finsupp.mapDomain j β) (coeff β G)`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`.

Conclude with `G.as_sum`. Use `_ = _ := by rw [map_sum]; simp only [rename_monomial]`. Establish `hc : weightedHomogeneousComponent (blockWeight ι) (⇑α) (rename j G) = rename j (monomial α (coeff α G))`. Rewrite using `[hsum, map_sum, rename_monomial]`. Rewrite using `[Finset.sum_eq_single α]`.

Rewrite using `[weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw α)), if_pos rfl]`. Introduce `β _ hβ`. Rewrite using `[weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw β)), if_neg]`. Conclude with `fun h => hβ (DFunLike.coe_injective h).symm`. Introduce `hα`.

Rewrite using `[notMem_support_iff.mp hα]`. Simplify using the standard rewrite rules. Rewrite `hcomp` using `[hc, ← Ideal.Quotient.eq_zero_iff_mem, ← key, aeval_monomial]`. Break down `mul_eq_zero.mp hcomp with h | h` into its components or cases. Conclude with `(map_eq_zero_iff _ (algebraMap F _).injective).mp h`.

It suffices to derive a contradiction. Rewrite `h` using `[Finsupp.prod]`. Take `⟨k, -, hk⟩` from `Finset.prod_eq_zero_iff.mp h`. Conclude with `hi k (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff'.mp hk).1)`. Establish `h1` using `hind.lift_cardinalMk_le_trdeg`.

Simplify using `only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_uzero] at h1`. Rewrite using `[GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F]`. Establish `h2 : (Fintype.card K : ℕ∞) ≤ (Algebra.trdeg F (MRing ι F ⧸ P)).toENat` using `Cardinal.natCast_le_toENat.mpr h1`. Conclude with `h2` after adjusting the coercions.
-/
theorem RelevantPrimeDimGe.proof : RelevantPrimeDimGe.Statement.{u} := by
  intro F _ K _ _ ι _ P hP
  have := hP.isPrime
  classical
  choose i hi using hP.relevant
  let j : K → (Σ k, ι k) := fun k => ⟨k, i k⟩
  let x : K → MRing ι F ⧸ P := fun k => Ideal.Quotient.mk P (X (j k))
  have key : ∀ p : MvPolynomial K F, aeval x p = Ideal.Quotient.mk P (rename j p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, rename_C]
      rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p k hp => simp [hp, x]
  have hw : ∀ β : K →₀ ℕ, Finsupp.weight (blockWeight ι) (Finsupp.mapDomain j β) = ⇑β := by
    intro β
    rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by simp [add_smul])]
    funext k'
    simp [Finsupp.sum, Finset.sum_apply, blockWeight, j, Pi.single_apply]
    exact fun h => h.symm
  have hind : AlgebraicIndependent F x := by
    rw [algebraicIndependent_iff]
    intro G hG
    rw [key] at hG
    have hmem : rename j G ∈ P := Ideal.Quotient.eq_zero_iff_mem.mp hG
    ext α
    rw [coeff_zero]
    have hcomp := hP.multiHomog _ hmem ⇑α
    have hsum : rename j G = ∑ β ∈ G.support, monomial (Finsupp.mapDomain j β) (coeff β G) := by
      calc rename j G = rename j (∑ β ∈ G.support, monomial β (coeff β G)) := by
            congr 1; exact G.as_sum
        _ = _ := by rw [map_sum]; simp only [rename_monomial]
    have hc : weightedHomogeneousComponent (blockWeight ι) (⇑α) (rename j G) =
        rename j (monomial α (coeff α G)) := by
      rw [hsum, map_sum, rename_monomial]
      rw [Finset.sum_eq_single α]
      · rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw α)),
          if_pos rfl]
      · intro β _ hβ
        rw [weightedHomogeneousComponent_of_mem (isWeightedHomogeneous_monomial _ _ _ (hw β)),
          if_neg]
        exact fun h => hβ (DFunLike.coe_injective h).symm
      · intro hα
        rw [notMem_support_iff.mp hα]
        simp
    rw [hc, ← Ideal.Quotient.eq_zero_iff_mem, ← key, aeval_monomial] at hcomp
    rcases mul_eq_zero.mp hcomp with h | h
    · exact (map_eq_zero_iff _ (algebraMap F _).injective).mp h
    · exfalso
      rw [Finsupp.prod] at h
      obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h
      exact hi k (Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero_iff'.mp hk).1)
  have h1 := hind.lift_cardinalMk_le_trdeg
  simp only [Cardinal.mk_fintype, Cardinal.lift_natCast, Cardinal.lift_uzero] at h1
  rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F]
  have h2 : (Fintype.card K : ℕ∞) ≤ (Algebra.trdeg F (MRing ι F ⧸ P)).toENat :=
    Cardinal.natCast_le_toENat.mpr h1
  exact_mod_cast h2

end

end GroundTheory.Heights₂.Heights.FieldNumbers
