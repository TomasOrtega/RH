import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PExtInvMuA

open Module NumberField TensorProduct

noncomputable section

namespace Formalism.L2.Geo.ExtensionFiltration.ExtInvMu

open Formalism.BasicNotions Formalism.HN Formalism.HermitianLatticesTheory Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.L2.Geo.ExtensionFiltration.ExtInvSk

section Places

variable (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']

open Classical in

/- English proof (translation)
Establish `h` using `InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank K' v`. Establish `h0 : InfinitePlace.ramifiedPlacesOver K' v = ∅`. Use extensionality with `w`. Simplify using `only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]`. Introduce and unpack `⟨_, hw⟩`.

Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _) (InfinitePlace.isRamified_iff.1 hw).2`. Establish `h1 : InfinitePlace.unramifiedPlacesOver K' v = ((Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v : Finset (InfinitePlace K')) : Set (InfinitePlace K'))`. Use extensionality with `w`. Simplify using `only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hw, _⟩`. Conclude with `InfinitePlace.LiesOver.comap_eq w v`. Introduce and unpack `rfl`. Use `⟨⟨?_⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`.

Both sides reduce to the same expression. Assume the negation of the conclusion as `hr`. Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _) (InfinitePlace.isRamified_iff.1 hr).2`. Rewrite `h` using `[h0, h1, Set.ncard_empty, mul_zero, add_zero, Set.ncard_coe_finset]`. Conclude with `h`.
-/
theorem card_fiber [IsTotallyComplex K] (v : InfinitePlace K) :
    (Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v).card =
      finrank K K' := by
  classical
  have h := InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank K' v
  have h0 : InfinitePlace.ramifiedPlacesOver K' v = ∅ := by
    ext w
    simp only [InfinitePlace.ramifiedPlacesOver, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
      iff_false]
    rintro ⟨_, hw⟩
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
      (InfinitePlace.isRamified_iff.1 hw).2
  have h1 : InfinitePlace.unramifiedPlacesOver K' v =
      ((Finset.univ.filter fun v' : InfinitePlace K' => v'.comap (algebraMap K K') = v :
        Finset (InfinitePlace K')) : Set (InfinitePlace K')) := by
    ext w
    simp only [InfinitePlace.unramifiedPlacesOver, Set.mem_ofPred_eq, Finset.coe_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hw, _⟩
      exact InfinitePlace.LiesOver.comap_eq w v
    · rintro rfl
      refine ⟨⟨?_⟩, ?_⟩
      · ext x
        rfl
      · by_contra hr
        exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex _)
          (InfinitePlace.isRamified_iff.1 hr).2
  rw [h0, h1, Set.ncard_empty, mul_zero, add_zero, Set.ncard_coe_finset] at h
  exact h

/- English proof (translation)
Rewrite using `[← Finset.prod_fiberwise Finset.univ (fun v' : InfinitePlace K' => v'.comap (algebraMap K K')) (fun v' => g (v'.comap (algebraMap K K'))), ← Finset.prod_pow]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_congr rfl (fun v' hv' => congrArg g (Finset.mem_filter.1 hv').2), Finset.prod_const]`. Use `congr 1`. Use `card_fiber K K' v` and compare the differences between its conclusion and the goal.
-/
theorem prod_comap [IsTotallyComplex K] (g : InfinitePlace K → ℝ) :
    ∏ v' : InfinitePlace K', g (v'.comap (algebraMap K K')) = (∏ v, g v) ^ finrank K K' := by
  classical
  rw [← Finset.prod_fiberwise Finset.univ (fun v' : InfinitePlace K' => v'.comap (algebraMap K K'))
    (fun v' => g (v'.comap (algebraMap K K'))), ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_congr rfl (fun v' hv' => congrArg g (Finset.mem_filter.1 hv').2),
    Finset.prod_const]
  congr 1
  convert card_fiber K K' v

/- English proof (translation)
Establish `h1` using `sizeMu_finrank_eq K`. Establish `h2` using `sizeMu_finrank_eq K'`. Establish `h3` using `Module.finrank_mul_finrank ℚ K K'`. Rewrite `h3` using `[h1, h2]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nPl_ext [IsTotallyComplex K] [IsTotallyComplex K'] : nPl K' = finrank K K' * nPl K := by
  have h1 := sizeMu_finrank_eq K
  have h2 := sizeMu_finrank_eq K'
  have h3 := Module.finrank_mul_finrank ℚ K K'
  rw [h1, h2] at h3
  linarith

end Places

end Formalism.L2.Geo.ExtensionFiltration.ExtInvMu
