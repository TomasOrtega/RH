import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsKrullDimMatAct
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.IsAlgebraicAdjoinRangeIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStA
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace KrullDimMatAct

variable {Ω : Type} [Field Ω] [CharZero Ω] {J : Type} [Fintype J]

def coneAdjoinQ (x : J → Ω) : Subalgebra ℚ (Polynomial Ω) :=
  Algebra.adjoin ℚ (Set.range fun j => Polynomial.C (x j) * Polynomial.X)

/- English proof (translation)
Establish `h : Polynomial.C (matAct A x i) * Polynomial.X = ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X)`. Simplify using `only [matAct, map_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]`. Rewrite using `[h]`.

Conclude with `Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _`.
-/
theorem mem_coneAdjoinQ_matAct (A : Matrix J J ℚ) (x : J → Ω) (i : J) :
    Polynomial.C (matAct A x i) * Polynomial.X ∈ coneAdjoinQ x := by
  have h : Polynomial.C (matAct A x i) * Polynomial.X =
      ∑ j, A i j • (Polynomial.C (x j) * Polynomial.X) := by
    simp only [matAct, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, Polynomial.algebraMap_apply, eq_ratCast, Polynomial.C_mul, mul_assoc]
  rw [h]
  exact Subalgebra.sum_mem _ fun j _ =>
    Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range_self j)) _

/- English proof (translation)
The claim follows from `Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)`.
-/
theorem coneAdjoinQ_matAct_le (A : Matrix J J ℚ) (x : J → Ω) :
    coneAdjoinQ (matAct A x) ≤ coneAdjoinQ x :=
  Algebra.adjoin_le (Set.range_subset_iff.mpr fun i => mem_coneAdjoinQ_matAct A x i)

/- English proof (translation)
Take `⟨B', _, hB'B⟩` from `isInvMat_mul hB`. Use `le_antisymm (coneAdjoinQ_matAct_le B x) ?_` and prove the remaining obligations. Establish `h` using `coneAdjoinQ_matAct_le B' (matAct B x)`. Rewrite `h` using `[matAct_matAct hB'B]`. Then use the resulting hypothesis.
-/
theorem coneAdjoinQ_matAct_eq {B : Matrix J J ℚ} (hB : IsInvMat B) (x : J → Ω) :
    coneAdjoinQ (matAct B x) = coneAdjoinQ x := by
  classical
  obtain ⟨B', _, hB'B⟩ := isInvMat_mul hB
  refine le_antisymm (coneAdjoinQ_matAct_le B x) ?_
  have h := coneAdjoinQ_matAct_le B' (matAct B x)
  rwa [matAct_matAct hB'B] at h

/- English proof (translation)
Take `⟨s, h1, h2⟩` from `GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)`. Establish `hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) = fun j => Polynomial.C (x j) * Polynomial.X`. Use function extensionality and compare the values at `fun v => by simp [coneMap]`. Rewrite `h1` using `[hX]`. Conclude with `⟨s, h1, h2⟩`.
-/
theorem ringKrullDim_quot_coordIdeal (x : J → Ω) :
    ∃ s : ℕ, Algebra.trdeg ℚ (coneAdjoinQ x) = s ∧
      ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ x) = (s : WithBot ℕ∞) + 1 := by
  obtain ⟨s, h1, h2⟩ := GroundTheory.Heights₂.Heights.TrdegAdjoin.ringKrullDim_quotient_ker
    (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω)
  have hX : (fun v => (coneMap ℤ x : MvPolynomial J ℤ →+* Polynomial Ω) (X v)) =
      fun j => Polynomial.C (x j) * Polynomial.X :=
    funext fun v => by simp [coneMap]
  rw [hX] at h1
  exact ⟨s, h1, h2⟩

/- English proof (translation)
Introduce `Ω _ _ J _ x B hB`. Take `⟨s, hs, hds⟩` from `ringKrullDim_quot_coordIdeal (matAct B x)`. Take `⟨t, ht, hdt⟩` from `ringKrullDim_quot_coordIdeal x`. Rewrite `hs` using `[coneAdjoinQ_matAct_eq hB, ht]`. Establish `hst : s = t` using `by exact_mod_cast hs.symm`.

Rewrite using `[hds, hdt, hst]`.
-/
theorem proof : KrullDimMatAct.Statement := by
  intro Ω _ _ J _ x B hB
  obtain ⟨s, hs, hds⟩ := ringKrullDim_quot_coordIdeal (matAct B x)
  obtain ⟨t, ht, hdt⟩ := ringKrullDim_quot_coordIdeal x
  rw [coneAdjoinQ_matAct_eq hB, ht] at hs
  have hst : s = t := by exact_mod_cast hs.symm
  rw [hds, hdt, hst]

end KrullDimMatAct

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
