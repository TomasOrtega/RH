import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsChartDimBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurvePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSuppAC
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

universe u v w

/- English proof (translation)
Introduce `K _ ι _ F _ V i hV hi`. Take `⟨hVp, hVh, -⟩` from `hV`. Set `f : K → MRingOver F ι` to `fun k => X ⟨k, i k⟩ - 1`. Set `t : Set (MRingOver F ι ⧸ V)` to `Set.range (Ideal.Quotient.mk V ∘ f)`. Establish `hspan : Ideal.span t = (Ideal.span (Set.range f)).map (Ideal.Quotient.mk V)`.

Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Set `e : (MRingOver F ι ⧸ V) ⧸ Ideal.span t ≃+* MRingOver F ι ⧸ chartIdeal V i` to `(Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup V _)`. Establish `: IsDomain (MRingOver F ι ⧸ V)` using `Ideal.Quotient.isDomain V`. Establish `: Algebra.FiniteType F (MRingOver F ι ⧸ V)` using `Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V) (Ideal.Quotient.mkₐ_surjective F V)`. Establish `: IsNoetherianRing (MRingOver F ι ⧸ V)` using `Algebra.FiniteType.isNoetherianRing F _`.

Establish `hne : Ideal.span t ≠ ⊤`. Establish `: Nontrivial (MRingOver F ι ⧸ chartIdeal V i)` using `Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hVh hi)`. Establish `: Nontrivial ((MRingOver F ι ⧸ V) ⧸ Ideal.span t)` using `e.toEquiv.nontrivial`. Conclude with `Ideal.Quotient.nontrivial_iff.mp this`. Take `⟨M, hM, htM⟩` from `Ideal.exists_le_maximal _ hne`.

Take `⟨s, hs⟩` from `DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)`. Establish `: M.IsPrime` using `hM.isPrime`. Establish `h1` using `Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) t (fun x hx => htM (Ideal.subset_span hx))`. Rewrite `h1` using `[ringKrullDim_eq_of_ringEquiv e]`. Establish `h2 : t.encard ≤ Fintype.card K`.

Combine the equalities or inequalities in the displayed calculation. Use `(ringKrullDim_le_iff_isMaximal_height_le _).mpr fun N hN => ?_` and prove the remaining obligations. Rewrite using `[hs N hN, ← hs M hM]`. Use `h1.trans ?_` and prove the remaining obligations. Use `gcongr`.

Conclude with `h2` after adjusting the coercions.
-/
theorem ChartDimBound.proof : ChartDimBound.Statement.{u, v, w} := by
  intro K _ ι _ F _ V i hV hi
  classical
  obtain ⟨hVp, hVh, -⟩ := hV
  let f : K → MRingOver F ι := fun k => X ⟨k, i k⟩ - 1
  let t : Set (MRingOver F ι ⧸ V) := Set.range (Ideal.Quotient.mk V ∘ f)
  have hspan : Ideal.span t = (Ideal.span (Set.range f)).map (Ideal.Quotient.mk V) := by
    rw [Ideal.map_span, ← Set.range_comp]
  let e : (MRingOver F ι ⧸ V) ⧸ Ideal.span t ≃+* MRingOver F ι ⧸ chartIdeal V i :=
    (Ideal.quotEquivOfEq hspan).trans (DoubleQuot.quotQuotEquivQuotSup V _)
  have : IsDomain (MRingOver F ι ⧸ V) := Ideal.Quotient.isDomain V
  have : Algebra.FiniteType F (MRingOver F ι ⧸ V) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F V) (Ideal.Quotient.mkₐ_surjective F V)
  have : IsNoetherianRing (MRingOver F ι ⧸ V) := Algebra.FiniteType.isNoetherianRing F _
  have hne : Ideal.span t ≠ ⊤ := by
    have : Nontrivial (MRingOver F ι ⧸ chartIdeal V i) :=
      Ideal.Quotient.nontrivial_iff.mpr (chartIdeal_ne_top hVh hi)
    have : Nontrivial ((MRingOver F ι ⧸ V) ⧸ Ideal.span t) := e.toEquiv.nontrivial
    exact Ideal.Quotient.nontrivial_iff.mp this
  obtain ⟨M, hM, htM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs⟩ := DimF.exists_height_of_isMaximal_of_field F (MRingOver F ι ⧸ V)
  have : M.IsPrime := hM.isPrime
  have h1 := Ideal.height_le_ringKrullDim_quotient_add_encard (p := M) t
    (fun x hx => htM (Ideal.subset_span hx))
  rw [ringKrullDim_eq_of_ringEquiv e] at h1
  have h2 : t.encard ≤ Fintype.card K := by
    calc t.encard = ((Ideal.Quotient.mk V ∘ f) '' Set.univ).encard := by rw [Set.image_univ]
      _ ≤ (Set.univ : Set K).encard := Set.encard_image_le _ _
      _ = Fintype.card K := by simp [Set.encard_univ]
  refine (ringKrullDim_le_iff_isMaximal_height_le _).mpr fun N hN => ?_
  rw [hs N hN, ← hs M hM]
  refine h1.trans ?_
  gcongr
  exact_mod_cast h2

end GroundTheory.Heights₂.Heights.Targets
