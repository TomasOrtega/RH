import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGenFibreHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace GenFibreHomog

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]`. Simplify using `[NumbersDVR.blockWeight, Pi.single_apply]`.
-/
theorem sum_block_eq_weight (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    ∑ i, m ⟨k, i⟩ = Finsupp.weight (NumbersDVR.blockWeight ι) m k := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_sigma]
  simp [NumbersDVR.blockWeight, Pi.single_apply]

/- English proof (translation)
Introduce `m hm k`. Rewrite using `[sum_block_eq_weight, hf (mem_support_iff.mp hm)]`.
-/
theorem isMultiHomog_of_weighted {f : MRing ι} {b : K → ℕ}
    (hf : IsWeightedHomogeneous (NumbersDVR.blockWeight ι) f b) : IsMultiHomog f b := by
  intro m hm k
  rw [sum_block_eq_weight, hf (mem_support_iff.mp hm)]

/- English proof (translation)
Proceed by induction on `f using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Establish `hm` using `isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)`. Rewrite using `[ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm), weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]`. Establish `hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) = monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1`.

Rewrite using `[monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using the standard rewrite rules. Rewrite using `[hX, coeff_C_mul, coeff_monomial]`. Distinguish the cases in `h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]`.
-/
theorem coeff_mConeMap {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (b : K → ℕ) (f : MRing ι) :
    coeff (Finsupp.equivFunOnFinite.symm b) (mConeMap y f) =
      aeval y (weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f) := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial m c =>
    have hm := isWeightedHomogeneous_monomial (NumbersDVR.blockWeight ι) m c
      (rfl : Finsupp.weight (NumbersDVR.blockWeight ι) m = _)
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted hm),
      weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hm)]
    have hX : (∏ k, (X k : MvPolynomial K Ω) ^ Finsupp.weight (NumbersDVR.blockWeight ι) m k) =
        monomial (Finsupp.equivFunOnFinite.symm (Finsupp.weight (NumbersDVR.blockWeight ι) m)) 1 := by
      rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
      simp
    rw [hX, coeff_C_mul, coeff_monomial]
    by_cases h : b = Finsupp.weight (NumbersDVR.blockWeight ι) m
    · subst h; simp
    · rw [if_neg h, if_neg (fun h' => h (Finsupp.equivFunOnFinite.symm.injective h').symm)]
      simp
  | add p q hp hq => rw [map_add, coeff_add, hp, hq, map_add, map_add]

/- English proof (translation)
Introduce `f hf b`. Establish `hf' : mConeMap y f = 0` using `RingHom.mem_ker.mp hf`. Use `RingHom.mem_ker.mpr ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mConeMap y _ = 0`. Rewrite using `[ProjLine.mConeMap_eq_of_isMultiHomog y (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)), ← coeff_mConeMap, hf', coeff_zero, map_zero, zero_mul]`.
-/
theorem isMultiHomogIdeal_mCoordIdeal {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) :
    NumbersDVR.IsMultiHomogIdeal (R := ℤ) (mCoordIdeal y) := by
  intro f hf b
  have hf' : mConeMap y f = 0 := RingHom.mem_ker.mp hf
  refine RingHom.mem_ker.mpr ?_
  change mConeMap y _ = 0
  rw [ProjLine.mConeMap_eq_of_isMultiHomog y
      (isMultiHomog_of_weighted (weightedHomogeneousComponent_isWeightedHomogeneous b f)),
    ← coeff_mConeMap, hf', coeff_zero, map_zero, zero_mul]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

omit [∀ k, Fintype (ι k)] in

/- English proof (translation)
Introduce `b f hf`. Establish `key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b : MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f` using `weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b`. Rewrite using `[key]`. Conclude with `h f hf b`.
-/
theorem isHomogeneous_of_isMultiHomogIdeal {R : Type} [CommRing R] {I : Ideal (MvPolynomial (Σ k, ι k) R)}
    (h : NumbersDVR.IsMultiHomogIdeal I) :
    I.IsHomogeneous (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
  intro b f hf
  have key : (DirectSum.decompose (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) f b :
      MvPolynomial (Σ k, ι k) R) = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f :=
    weightedDecomposition.decompose'_apply R (NumbersDVR.blockWeight ι) f b
  rw [key]
  exact h f hf b

end GenFibreHomog

open GenFibreHomog in
attribute [local instance] MvPolynomial.weightedGradedAlgebra in

/- English proof (translation)
Introduce `K _ _ ι _ Ω _ y`. Establish `hI` using `isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)`. Take `⟨S, hS⟩` from `(Ideal.IsHomogeneous.iff_exists _ _).mp hI`. Establish `hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι))`. Rewrite using `[hS, Ideal.map_span]`.

Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨s, -, rfl⟩, rfl⟩`. Take `⟨b, hb⟩` from `s.2`. Use `⟨b, ?_⟩` and prove the remaining obligations. Rewrite `hb`, the goal using `[mem_weightedHomogeneousSubmodule]`.

Introduce `d hd`. Apply `hb` to reduce the goal to its premises. Introduce `h0`. Apply `hd` to reduce the goal to its premises. Rewrite using `[coeff_map, h0, map_zero]`.

Introduce `f hf b`. Conclude with `weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b`.
-/
theorem GenFibreHomog.proof : GenFibreHomog.Statement := by
  intro K _ _ ι _ Ω _ y
  have hI := isHomogeneous_of_isMultiHomogIdeal (isMultiHomogIdeal_mCoordIdeal y)
  obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ _).mp hI
  have hJ : ((mCoordIdeal y).map (MvPolynomial.map (Int.castRingHom ℚ))).IsHomogeneous
      (weightedHomogeneousSubmodule ℚ (NumbersDVR.blockWeight ι)) := by
    rw [hS, Ideal.map_span]
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ ⟨_, ⟨s, -, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := s.2
    refine ⟨b, ?_⟩
    rw [mem_weightedHomogeneousSubmodule] at hb ⊢
    intro d hd
    apply hb
    intro h0
    apply hd
    rw [coeff_map, h0, map_zero]
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem ℚ _ hJ hf b

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
