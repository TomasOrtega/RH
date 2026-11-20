import Formalism.PeriodIntegrals.EfRankSum

namespace PI.UnitaryGroupMassFormula.EfRankSum

open Formalism.MainNotions.Gaps.EtaleWeightGaps IsLocalRing

/- English proof (translation)
Use `haveI := ζ.isMaximal`. Use `⟨inferInstance, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal)).symm`.
-/
theorem mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ζ.asIdeal ∈ (maximalIdeal O).primesOver ↥(As O A) := by
  haveI := ζ.isMaximal
  refine ⟨inferInstance, ⟨?_⟩⟩
  exact (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal ζ.asIdeal)).symm

/- English proof (translation)
Take `⟨hp, hl⟩` from `hq`. Establish `h : q.comap (algebraMap O ↥(As O A)) = maximalIdeal O` using `hl.over.symm`. Conclude with `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (h ▸ IsLocalRing.maximalIdeal.isMaximal O)`.
-/
theorem isMaximal_of_mem_primesOver (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] {q : Ideal ↥(As O A)}
    (hq : q ∈ (maximalIdeal O).primesOver ↥(As O A)) : q.IsMaximal := by
  obtain ⟨hp, hl⟩ := hq
  have h : q.comap (algebraMap O ↥(As O A)) = maximalIdeal O := hl.over.symm
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_comap q (h ▸ IsLocalRing.maximalIdeal.isMaximal O)

noncomputable def ptsEquiv (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] :
    Pts O A ≃ (maximalIdeal O).primesOver ↥(As O A) where
  toFun ζ := ⟨ζ.asIdeal, mem_primesOver O A ζ⟩
  invFun q := ⟨q.1, isMaximal_of_mem_primesOver O A q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ptsEquiv_apply (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] (ζ : Pts O A) :
    ((ptsEquiv O A ζ : (maximalIdeal O).primesOver ↥(As O A)) : Ideal ↥(As O A)) = ζ.asIdeal := rfl

/- English proof (translation)
Use `haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by`. Establish `hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite` using `Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)`. Conclude with `hfin.to_subtype`. Conclude with `Finite.of_equiv _ (ptsEquiv O A).symm`.
-/
theorem finite_pts (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A : Type) [CommRing A] [Algebra O A] [Module.Finite O ↥(As O A)] : Finite (Pts O A) := by
  classical
  haveI : Finite ((maximalIdeal O).primesOver ↥(As O A)) := by
    have hfin : ((maximalIdeal O).primesOver ↥(As O A)).Finite :=
      Algebra.QuasiFinite.finite_primesOver (maximalIdeal O)
    exact hfin.to_subtype
  exact Finite.of_equiv _ (ptsEquiv O A).symm

end PI.UnitaryGroupMassFormula.EfRankSum
