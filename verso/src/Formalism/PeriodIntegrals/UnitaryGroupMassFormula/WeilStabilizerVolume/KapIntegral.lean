import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ESSymmApply

noncomputable section

namespace PI.VolStabW.RPA

open MeasureTheory Filter Finset
open scoped NNReal ENNReal

variable {ι : Type} {W : ι → Type} [∀ i, MeasurableSpace (W i)]
variable {m : ∀ i, Measure (W i)} {L : ∀ i, Set (W i)} [∀ i, SigmaFinite (m i)]

instance Rm_sf (S : Finset ι) : SigmaFinite (Rm m L S) := by unfold Rm; infer_instance

/- English proof (translation)
Use `set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'`. Unfold `Qm`. Use `split_ifs with hh`. Use `haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) := fun i => Pn_prob m L (hh i.1 i.2)`. Establish `hP : ∀ j : {i // i ∉ S}, Integrable (g j.1) (Pn m L j.1)` using `fun j => ((hg j.1).restrict).smul_measure (ENNReal.inv_ne_top.2 (hh j.1 j.2).1)`.

Set `F : (∀ j : T', W j.1.1) → ℂ` to `fun y => ∏ j : T', g j.1.1 (y j)`. Establish `hpi : Integrable F (Measure.pi (fun j : T' => Pn m L j.1.1))` using `Integrable.fintype_prod_dep (fun j => hP j.1)`. Establish `hre : (fun z : (∀ j : {i // i ∉ S}, W j.1) => ∏ j ∈ T', g j.1 (z j)) = fun z => F (T'.restrict z)`. Use function extensionality and compare the values at `z`. Conclude with `(Finset.prod_coe_sort T' (fun j => g j.1 (z j))).symm`.

Establish `hmap` using `Measure.infinitePi_map_restrict (μ := fun j : {i // i ∉ S} => Pn m L j.1) (I := T')`. Establish `hpi' : Integrable F ((Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1).map T'.restrict)` using `by rw [hmap]; exact hpi`. Establish `hint : Integrable (fun z => F (T'.restrict z)) (Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1)` using `(integrable_map_measure hpi'.aestronglyMeasurable (Finset.measurable_restrict _).aemeasurable).1 hpi'`. Rewrite using `[hre]`. Use `⟨hint.smul_measure_nnreal, ?_⟩` and prove the remaining obligations.

Rewrite using `[integral_smul_nnreal_measure, integral_restrict_infinitePi (fun j : {i // i ∉ S} => Pn m L j.1) hpi.aestronglyMeasurable]`. Simplify using `only [F]`. Rewrite using `[integral_fintype_prod_eq_prod]`. Simplify using `only [Pn, integral_smul_measure]`. Rewrite using `[Finset.prod_coe_sort T' (fun j => ((m j.1 (L j.1))⁻¹.toReal • ∫ w, g j.1 w ∂(m j.1).restrict (L j.1))), hT', Finset.prod_subtype_eq_prod_filter (f := fun i => ((m i (L i))⁻¹.toReal • ∫ w, g i w ∂(m i).restrict (L i))), ← Finset.sdiff_eq_filter, tl_split hT hST]`.

Establish `hmu : ∀ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i) = ∫ w, g i w ∂(m i).restrict (L i)`. Introduce `i hi`. Rewrite using `[mu, if_neg (Finset.mem_sdiff.1 hi).2]`. Rewrite using `[Finset.prod_congr rfl hmu]`. Establish `hone : (∏ i ∈ T \ S, ((am m L i : ℝ) : ℂ)) * (∏ i ∈ T \ S, (((m i (L i))⁻¹.toReal : ℝ) : ℂ)) = 1`.

Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_eq_one (fun i hi => ?_)` and prove the remaining obligations. Establish `h1` using `hh i (Finset.mem_sdiff.1 hi).2`. Rewrite using `[← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv, mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h1.1, h1.2⟩), Complex.ofReal_one]`. Simplify using `only [NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod, Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]`.

Take the linear combination `(((tl m L T : ℝ) : ℂ) * ∏ i ∈ T \ S, ∫ w, g i w ∂(m i).restrict (L i)) * hone`. Use `push_neg at hh`. Take `⟨i, hiS, hi⟩` from `hh`. Establish `h0 : m i (L i) = 0`. Assume the negation of the conclusion as `h`.

Conclude with `hfin i (hi h)`. Use `⟨integrable_zero_measure, ?_⟩` and prove the remaining obligations. Rewrite using `[integral_zero_measure]`. Distinguish the cases in `hiT : i ∈ T`. Rewrite using `[Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hiT, hiS⟩), zero_mul]`.

Rewrite using `[mu, if_neg hiS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]`. Rewrite using `[tl_zero hT hiT (by simp [am, h0])]`. Simplify using the standard rewrite rules.
-/
lemma Qm_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun z => ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j)) (Qm m L S) ∧
    ∫ z, ∏ j ∈ T.subtype (fun i => i ∉ S), g j.1 (z j) ∂Qm m L S =
      (∏ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  unfold Qm
  split_ifs with hh
  · haveI : ∀ i : {i // i ∉ S}, IsProbabilityMeasure (Pn m L i.1) :=
      fun i => Pn_prob m L (hh i.1 i.2)
    have hP : ∀ j : {i // i ∉ S}, Integrable (g j.1) (Pn m L j.1) := fun j =>
      ((hg j.1).restrict).smul_measure (ENNReal.inv_ne_top.2 (hh j.1 j.2).1)
    let F : (∀ j : T', W j.1.1) → ℂ := fun y => ∏ j : T', g j.1.1 (y j)
    have hpi : Integrable F (Measure.pi (fun j : T' => Pn m L j.1.1)) :=
      Integrable.fintype_prod_dep (fun j => hP j.1)
    have hre : (fun z : (∀ j : {i // i ∉ S}, W j.1) => ∏ j ∈ T', g j.1 (z j)) =
        fun z => F (T'.restrict z) := by
      funext z
      exact (Finset.prod_coe_sort T' (fun j => g j.1 (z j))).symm
    have hmap := Measure.infinitePi_map_restrict (μ := fun j : {i // i ∉ S} => Pn m L j.1) (I := T')
    have hpi' : Integrable F ((Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1).map
        T'.restrict) := by rw [hmap]; exact hpi
    have hint : Integrable (fun z => F (T'.restrict z))
        (Measure.infinitePi fun j : {i // i ∉ S} => Pn m L j.1) :=
      (integrable_map_measure hpi'.aestronglyMeasurable
        (Finset.measurable_restrict _).aemeasurable).1 hpi'
    rw [hre]
    refine ⟨hint.smul_measure_nnreal, ?_⟩
    rw [integral_smul_nnreal_measure,
      integral_restrict_infinitePi (fun j : {i // i ∉ S} => Pn m L j.1) hpi.aestronglyMeasurable]
    simp only [F]
    rw [integral_fintype_prod_eq_prod]
    simp only [Pn, integral_smul_measure]
    rw [Finset.prod_coe_sort T' (fun j => ((m j.1 (L j.1))⁻¹.toReal • ∫ w, g j.1 w ∂(m j.1).restrict (L j.1))),
      hT', Finset.prod_subtype_eq_prod_filter (f := fun i => ((m i (L i))⁻¹.toReal • ∫ w, g i w ∂(m i).restrict (L i))),
      ← Finset.sdiff_eq_filter, tl_split hT hST]
    have hmu : ∀ i ∈ T \ S, ∫ w, g i w ∂(mu m L S i) = ∫ w, g i w ∂(m i).restrict (L i) := by
      intro i hi
      rw [mu, if_neg (Finset.mem_sdiff.1 hi).2]
    rw [Finset.prod_congr rfl hmu]
    have hone : (∏ i ∈ T \ S, ((am m L i : ℝ) : ℂ)) * (∏ i ∈ T \ S, (((m i (L i))⁻¹.toReal : ℝ) : ℂ)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_eq_one (fun i hi => ?_)
      have h1 := hh i (Finset.mem_sdiff.1 hi).2
      rw [← Complex.ofReal_mul, am, ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_inv,
        mul_inv_cancel₀ (ENNReal.toReal_ne_zero.2 ⟨h1.1, h1.2⟩), Complex.ofReal_one]
    simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_mul, NNReal.coe_prod,
      Complex.ofReal_mul, Complex.ofReal_prod, Finset.prod_mul_distrib]
    linear_combination (((tl m L T : ℝ) : ℂ) * ∏ i ∈ T \ S, ∫ w, g i w ∂(m i).restrict (L i)) * hone
  · push_neg at hh
    obtain ⟨i, hiS, hi⟩ := hh
    have h0 : m i (L i) = 0 := by
      by_contra h; exact hfin i (hi h)
    refine ⟨integrable_zero_measure, ?_⟩
    rw [integral_zero_measure]
    by_cases hiT : i ∈ T
    · rw [Finset.prod_eq_zero (i := i) (Finset.mem_sdiff.2 ⟨hiT, hiS⟩), zero_mul]
      rw [mu, if_neg hiS, Measure.restrict_eq_zero.2 h0, integral_zero_measure]
    · rw [tl_zero hT hiT (by simp [am, h0])]
      simp

/- English proof (translation)
Use `set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'`. Establish `hfun : ∀ p, (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ((eS S).symm p) = (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j))`. Introduce `p`. Simplify using `only`. Rewrite using `[← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]`.

Use `congr 1`. Rewrite using `[Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.prod_coe_sort S]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[eS_symm_apply, dif_pos i.2]`. Rewrite using `[← Finset.prod_subtype_eq_prod_filter]`.

Use `Finset.prod_congr rfl (fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[eS_symm_apply, dif_neg j.2]`. Establish `hR : Integrable (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i)) (Rm m L S)`. Unfold `Rm`. Conclude with `Integrable.fintype_prod_dep (fun i => (hg i.1).restrict)`.

Take `⟨hQi, hQ⟩` from `Qm_integral hfin hT hST g hg`. Rewrite `hQi`, `hQ` using `[← hT']`. Establish `hcomp : (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm = fun p => (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j))`. Use function extensionality and compare the values at `hfun`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `kap`. Rewrite using `[integrable_map_equiv, hcomp]`. Conclude with `Integrable.mul_prod (μ := Rm m L S) (ν := Qm m L S) (f := fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i)) (g := fun z => ∏ j ∈ T', g j.1 (z j)) hR hQi`. Unfold `kap`. Rewrite using `[integral_map_equiv]`.

Use `(integral_congr_ae (ae_of_all _ hfun)).trans ?_` and prove the remaining obligations. Rewrite using `[integral_prod_mul (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i)) (fun z : (∀ i : {i // i ∉ S}, W i) => ∏ j ∈ T', g j.1 (z j)), hQ, Rm, integral_fintype_prod_eq_prod, ← Finset.prod_sdiff hST]`. Establish `hS : ∏ i : {i // i ∈ S}, ∫ w, g i.1 w ∂(m i.1).restrict (L i.1)ᶜ = ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i)`. Rewrite using `[← Finset.prod_coe_sort S]`. Use `Finset.prod_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Rewrite using `[mu, if_pos i.2]`. Rewrite using `[hS]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma kap_integral [DecidableEq ι] (hfin : ∀ i, m i (L i) ≠ ⊤) (hT : TailH m L)
    {S T : Finset ι} (hST : S ⊆ T) (g : ∀ i, W i → ℂ) (hg : ∀ i, Integrable (g i) (m i)) :
    Integrable (fun x => ∏ i ∈ T, g i (x i)) (kap m L S) ∧
    ∫ x, ∏ i ∈ T, g i (x i) ∂kap m L S =
      (∏ i ∈ T, ∫ w, g i w ∂(mu m L S i)) * (tl m L T : ℂ) := by
  classical
  set T' : Finset {i // i ∉ S} := T.subtype (fun i => i ∉ S) with hT'
  have hfun : ∀ p, (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ((eS S).symm p) =
      (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) := by
    intro p
    simp only
    rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => i ∈ S)]
    congr 1
    · rw [Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hST, ← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [eS_symm_apply, dif_pos i.2]
    · rw [← Finset.prod_subtype_eq_prod_filter]
      refine Finset.prod_congr rfl (fun j _ => ?_)
      rw [eS_symm_apply, dif_neg j.2]
  have hR : Integrable (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (Rm m L S) := by
    unfold Rm; exact Integrable.fintype_prod_dep (fun i => (hg i.1).restrict)
  obtain ⟨hQi, hQ⟩ := Qm_integral hfin hT hST g hg
  rw [← hT'] at hQi hQ
  have hcomp : (fun x : (∀ i, W i) => ∏ i ∈ T, g i (x i)) ∘ (eS S).symm =
      fun p => (∏ i : {i // i ∈ S}, g i.1 (p.1 i)) * (∏ j ∈ T', g j.1 (p.2 j)) :=
    funext hfun
  refine ⟨?_, ?_⟩
  · unfold kap
    rw [integrable_map_equiv, hcomp]
    exact Integrable.mul_prod (μ := Rm m L S) (ν := Qm m L S)
      (f := fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (g := fun z => ∏ j ∈ T', g j.1 (z j)) hR hQi
  · unfold kap
    rw [integral_map_equiv]
    refine (integral_congr_ae (ae_of_all _ hfun)).trans ?_
    rw [integral_prod_mul (fun y : (∀ i : {i // i ∈ S}, W i) => ∏ i : {i // i ∈ S}, g i.1 (y i))
      (fun z : (∀ i : {i // i ∉ S}, W i) => ∏ j ∈ T', g j.1 (z j)), hQ, Rm, integral_fintype_prod_eq_prod,
      ← Finset.prod_sdiff hST]
    have hS : ∏ i : {i // i ∈ S}, ∫ w, g i.1 w ∂(m i.1).restrict (L i.1)ᶜ =
        ∏ i ∈ S, ∫ w, g i w ∂(mu m L S i) := by
      rw [← Finset.prod_coe_sort S]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [mu, if_pos i.2]
    rw [hS]
    ring

end PI.VolStabW.RPA
