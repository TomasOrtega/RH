import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntPoint
import GroundTheory.HeightsAndTheta.Heights.Intersections.CompsDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Assembly
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial MeasureTheory
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsMultiProjPrime blockWeight)
open GroundTheory.Heights₂.Heights.FieldNumbers (IntNumBase.full homFracDegZero)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot ChartPartition mInt integralWith locDens)

section Algebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Establish `hpr` using `hP.isPrime`. Use `choose i hi using hP.relevant`. Establish `hg : h * ∏ k, (X ⟨k, i k⟩ : MRing ι ℂ) ∈ P`. Rewrite using `[← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P]`. Introduce `x hx`.

Establish `hx' : ∀ f ∈ P, eval x f = 0` using `fun f hf => hx f hf`. Use `show eval x (h * ∏ k, (X ⟨k, i k⟩ : MRing ι ℂ)) = 0`. Distinguish the cases in `hz : ∀ k, x ⟨k, i k⟩ ≠ 0`. Rewrite using `[map_mul, hv x ⟨fun k => ⟨i k, hz k⟩, hx'⟩, zero_mul]`. Use `push Not at hz`.

Take `⟨k, hk⟩` from `hz`. Rewrite using `[map_mul, map_prod]`. Conclude with `mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_X, hk]))`. Break down `hpr.mem_or_mem hg with h' | h'` into its components or cases. Conclude with `h'`.

Take `⟨k, -, hk⟩` from `Ideal.IsPrime.prod_mem_iff.mp h'`. Conclude with `absurd hk (hi k)`.
-/
theorem mem_of_forall_eval_eq_zero {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P)
    {h : MRing ι ℂ} (hv : ∀ z ∈ zPts P, eval z h = 0) : h ∈ P := by
  have hpr := hP.isPrime
  choose i hi using hP.relevant
  have hg : h * ∏ k, (X ⟨k, i k⟩ : MRing ι ℂ) ∈ P := by
    rw [← MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := ℂ) P]
    intro x hx
    have hx' : ∀ f ∈ P, eval x f = 0 := fun f hf => hx f hf
    show eval x (h * ∏ k, (X ⟨k, i k⟩ : MRing ι ℂ)) = 0
    by_cases hz : ∀ k, x ⟨k, i k⟩ ≠ 0
    · rw [map_mul, hv x ⟨fun k => ⟨i k, hz k⟩, hx'⟩, zero_mul]
    · push Not at hz
      obtain ⟨k, hk⟩ := hz
      rw [map_mul, map_prod]
      exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ k) (by rw [eval_X, hk]))
  rcases hpr.mem_or_mem hg with h' | h'
  · exact h'
  · obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h'
    exact absurd hk (hi k)

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[Set.not_nonempty_iff_eq_empty]`. Establish `h1 : (1 : MRing ι ℂ) ∈ P` using `mem_of_forall_eval_eq_zero hP fun z hz => by rw [hne] at hz; exact absurd hz (Set.notMem_empty z)`. Conclude with `hP.isPrime.ne_top ((Ideal.eq_top_iff_one P).mpr h1)`.
-/
theorem zPts_nonempty {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P) : (zPts P).Nonempty := by
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne
  have h1 : (1 : MRing ι ℂ) ∈ P :=
    mem_of_forall_eval_eq_zero hP fun z hz => by rw [hne] at hz; exact absurd hz (Set.notMem_empty z)
  exact hP.isPrime.ne_top ((Ideal.eq_top_iff_one P).mpr h1)

/- English proof (translation)
Use `hP.1.isPrime` as an intermediate fact. Establish `hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0`. Rewrite using `[relDim_of_isProjVar hP]`. Both sides reduce to the same expression. Take `⟨hfd, -⟩` from `IntNumBase.full ℂ K ι P hP.1 hrel`.

Establish `hbot : homFracDegZero P = ⊥` using `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _`. Use `set Q := MRing ι ℂ ⧸ P`. Use `set F := FractionRing Q`. Establish `hinj : Function.Injective (algebraMap Q F)` using `IsFractionRing.injective Q F`. Use `set a : F := algebraMap Q F (Ideal.Quotient.mk P (X ⟨k, i'⟩))`.

Use `set b : F := algebraMap Q F (Ideal.Quotient.mk P (X ⟨k, i⟩))`. Establish `hb : b ≠ 0`. Introduce `h0`. Rewrite `h0` using `[← map_zero (algebraMap Q F)]`. Conclude with `hi (Ideal.Quotient.eq_zero_iff_mem.mp (hinj h0))`.

Establish `hmem : a / b ∈ homFracDegZero P` using `IntermediateField.subset_adjoin _ _ ⟨blockWeight ι ⟨k, i⟩, X ⟨k, i'⟩, X ⟨k, i⟩, isWeightedHomogeneous_X ℂ (blockWeight ι) ⟨k, i'⟩, isWeightedHomogeneous_X ℂ (blockWeight ι) ⟨k, i⟩, hi, rfl⟩`. Rewrite `hmem` using `[hbot]`. Take `⟨c, hc⟩` from `IntermediateField.mem_bot.mp hmem`. Use `⟨c, Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_)⟩` and prove the remaining obligations. Establish `hC : algebraMap Q F (Ideal.Quotient.mk P (C c)) = algebraMap ℂ F c`.

Rewrite using `[IsScalarTower.algebraMap_apply ℂ Q F]`. Both sides reduce to the same expression. Rewrite using `[map_zero, map_sub, map_sub, map_mul, map_mul, hC, hc]`. Use `show a - a / b * b = 0`. Rewrite using `[div_mul_cancel₀ a hb, sub_self]`.
-/
theorem exists_sub_mem_of_isProjVar_zero {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P 0) (k : K)
    {i : ι k} (hi : (X ⟨k, i⟩ : MRing ι ℂ) ∉ P) (i' : ι k) :
    ∃ c : ℂ, (X ⟨k, i'⟩ - C c * X ⟨k, i⟩ : MRing ι ℂ) ∈ P := by
  have := hP.1.isPrime
  have hrel : GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = 0 := by
    rw [relDim_of_isProjVar hP]
    rfl
  obtain ⟨hfd, -⟩ := IntNumBase.full ℂ K ι P hP.1 hrel
  have hbot : homFracDegZero P = ⊥ := IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _
  set Q := MRing ι ℂ ⧸ P
  set F := FractionRing Q
  have hinj : Function.Injective (algebraMap Q F) := IsFractionRing.injective Q F
  set a : F := algebraMap Q F (Ideal.Quotient.mk P (X ⟨k, i'⟩))
  set b : F := algebraMap Q F (Ideal.Quotient.mk P (X ⟨k, i⟩))
  have hb : b ≠ 0 := by
    intro h0
    rw [← map_zero (algebraMap Q F)] at h0
    exact hi (Ideal.Quotient.eq_zero_iff_mem.mp (hinj h0))
  have hmem : a / b ∈ homFracDegZero P :=
    IntermediateField.subset_adjoin _ _ ⟨blockWeight ι ⟨k, i⟩, X ⟨k, i'⟩, X ⟨k, i⟩,
      isWeightedHomogeneous_X ℂ (blockWeight ι) ⟨k, i'⟩,
      isWeightedHomogeneous_X ℂ (blockWeight ι) ⟨k, i⟩, hi, rfl⟩
  rw [hbot] at hmem
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hmem
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp (hinj ?_)⟩
  have hC : algebraMap Q F (Ideal.Quotient.mk P (C c)) = algebraMap ℂ F c := by
    rw [IsScalarTower.algebraMap_apply ℂ Q F]
    rfl
  rw [map_zero, map_sub, map_sub, map_mul, map_mul, hC, hc]
  show a - a / b * b = 0
  rw [div_mul_cancel₀ a hb, sub_self]

/- English proof (translation)
Use `choose i hi using hP.1.relevant`. Use `choose c hc using fun (k : K) (i' : ι k) => exists_sub_mem_of_isProjVar_zero hP k (hi k) i'`. Establish `key : ∀ w ∈ zPts P, (∀ q : Σ k, ι k, w q = c q.1 q.2 * w ⟨q.1, i q.1⟩) ∧ ∀ k, w ⟨k, i k⟩ ≠ 0`. Introduce `w hw`. Establish `hq : ∀ q : Σ k, ι k, w q = c q.1 q.2 * w ⟨q.1, i q.1⟩`.

Introduce `q`. Establish `h0` using `hw.2 _ (hc q.1 q.2)`. Rewrite `h0` using `[map_sub, map_mul, eval_X, eval_X, eval_C, sub_eq_zero]`. Conclude with `h0`. Use `⟨hq, fun k h0 => ?_⟩` and prove the remaining obligations.

Take `⟨i', hi'⟩` from `hw.1 k`. Conclude with `hi' (by rw [hq ⟨k, i'⟩, h0, mul_zero])`. Take `⟨hzq, hz0⟩` from `key z hz`. Take `⟨hzq', hz0'⟩` from `key z' hz'`. Use `⟨fun k => z ⟨k, i k⟩ / z' ⟨k, i k⟩, fun k => div_ne_zero (hz0 k) (hz0' k), funext fun q => ?_⟩` and prove the remaining obligations.

Rewrite using `[hzq q, hzq' q]`. Clear denominators, using `[hz0' q.1]` for the nonvanishing conditions.
-/
theorem sameOrbit_of_isProjVar_zero {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P 0) {z z' : MCone ι}
    (hz : z ∈ zPts P) (hz' : z' ∈ zPts P) : ReciprocityTheory.AnForm.R.SameOrbit z z' := by
  choose i hi using hP.1.relevant
  choose c hc using fun (k : K) (i' : ι k) => exists_sub_mem_of_isProjVar_zero hP k (hi k) i'
  have key : ∀ w ∈ zPts P, (∀ q : Σ k, ι k, w q = c q.1 q.2 * w ⟨q.1, i q.1⟩) ∧
      ∀ k, w ⟨k, i k⟩ ≠ 0 := by
    intro w hw
    have hq : ∀ q : Σ k, ι k, w q = c q.1 q.2 * w ⟨q.1, i q.1⟩ := by
      intro q
      have h0 := hw.2 _ (hc q.1 q.2)
      rw [map_sub, map_mul, eval_X, eval_X, eval_C, sub_eq_zero] at h0
      exact h0
    refine ⟨hq, fun k h0 => ?_⟩
    obtain ⟨i', hi'⟩ := hw.1 k
    exact hi' (by rw [hq ⟨k, i'⟩, h0, mul_zero])
  obtain ⟨hzq, hz0⟩ := key z hz
  obtain ⟨hzq', hz0'⟩ := key z' hz'
  refine ⟨fun k => z ⟨k, i k⟩ / z' ⟨k, i k⟩, fun k => div_ne_zero (hz0 k) (hz0' k), funext fun q => ?_⟩
  rw [hzq q, hzq' q]
  field_simp [hz0' q.1]

/- English proof (translation)
Introduce `hzD`. Take `⟨f, hfD, hfP⟩` from `Set.not_subset.mp hDP`. Establish `hcomp : ∃ b : K → ℕ, weightedHomogeneousComponent (blockWeight ι) b f ∉ P`. Assume the negation of the conclusion as `hall`. Use `push Not at hall`.

Apply `hfP` to reduce the goal to its premises. Rewrite using `[← sum_weightedHomogeneousComponent (blockWeight ι) f, finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]`. Conclude with `Ideal.sum_mem _ fun b _ => hall b`. Take `⟨b, hb⟩` from `hcomp`. Apply `hb` to reduce the goal to its premises.

Use `mem_of_forall_eval_eq_zero hP.1 fun w hw => ?_` and prove the remaining obligations. Take `⟨d, -, rfl⟩` from `sameOrbit_of_isProjVar_zero hP hw hz`. Establish `h` using `eval_tsmul_of_isMultiHomog (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f) d z`. Rewrite using `[show (fun q : Σ k, ι k => d q.1 * z q) = tsmul d z from rfl, h, hzD.2 _ (hD f hfD b), mul_zero]`.
-/
theorem not_mem_conePts_of_isProjVar_zero {P D : Ideal (MRing ι ℂ)} (hP : IsProjVar P 0)
    (hD : IsMultiHomogIdeal D) (hDP : ¬ D ≤ P) {z : MCone ι} (hz : z ∈ zPts P) :
    z ∉ ReciprocityTheory.AnForm.R.conePts D := by
  intro hzD
  obtain ⟨f, hfD, hfP⟩ := Set.not_subset.mp hDP
  have hcomp : ∃ b : K → ℕ, weightedHomogeneousComponent (blockWeight ι) b f ∉ P := by
    by_contra hall
    push Not at hall
    apply hfP
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    exact Ideal.sum_mem _ fun b _ => hall b
  obtain ⟨b, hb⟩ := hcomp
  apply hb
  refine mem_of_forall_eval_eq_zero hP.1 fun w hw => ?_
  obtain ⟨d, -, rfl⟩ := sameOrbit_of_isProjVar_zero hP hw hz
  have h := eval_tsmul_of_isMultiHomog
    (weightedHomogeneousComponent_isWeightedHomogeneous (w := blockWeight ι) b f) d z
  rw [show (fun q : Σ k, ι k => d q.1 * z q) = tsmul d z from rfl, h, hzD.2 _ (hD f hfD b), mul_zero]

end Algebra

section Resolution

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨z, hz⟩` from `zPts_nonempty hP.1`. Take `⟨i₀, x₀, hx₀, -⟩` from `R.R.surj z hz (not_mem_conePts_of_isProjVar_zero hP R.homog R.not_le hz)`. Use `⟨x₀, fun x => ?_⟩` and prove the remaining obligations. Take `⟨i, hx⟩` from `R.R.cover x`. Establish `hy` using `R.R.lift_mem i x hx`.

Conclude with `R.R.inj i i₀ x hx x₀ hx₀ (not_mem_conePts_of_isProjVar_zero hP R.homog R.not_le hy) (sameOrbit_of_isProjVar_zero hP hy (R.R.lift_mem i₀ x₀ hx₀))`.
-/
theorem Res.eq_of_isProjVar_zero {P : Ideal (MRing ι ℂ)} (hP : IsProjVar P 0) (R : Res ι P 0) :
    ∃ x₀ : R.R.M, ∀ x, x = x₀ := by
  obtain ⟨z, hz⟩ := zPts_nonempty hP.1
  obtain ⟨i₀, x₀, hx₀, -⟩ :=
    R.R.surj z hz (not_mem_conePts_of_isProjVar_zero hP R.homog R.not_le hz)
  refine ⟨x₀, fun x => ?_⟩
  obtain ⟨i, hx⟩ := R.R.cover x
  have hy := R.R.lift_mem i x hx
  exact R.R.inj i i₀ x hx x₀ hx₀ (not_mem_conePts_of_isProjVar_zero hP R.homog R.not_le hy)
    (sameOrbit_of_isProjVar_zero hP hy (R.R.lift_mem i₀ x₀ hx₀))

end Resolution

section Point

variable {X : Type*} [TopologicalSpace X]

/- English proof (translation)
Take `⟨j₀, hj₀⟩` from `A.cover x₀`. Establish `hpart : Nonempty (ChartPartition A)`. Use `⟨⟨fun j _ => if j = j₀ then 1 else 0, fun j k => contDiffOn_const, fun j x => ?_, fun j => ?_, fun x => by simp⟩⟩` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> norm_num`. Distinguish the cases in `hj : j = j₀`.

Substitute `hj` using the available equality. Introduce `x _`. Rewrite using `[hX x]`. Conclude with `hj₀`. Establish `h0 : (fun _ : X => if j = j₀ then (1 : ℝ) else 0) = 0`.

Use function extensionality and compare the values at `x`. Simplify using `[hj]`. Rewrite using `[h0, tsupport_zero]`. Conclude with `Set.empty_subset _`. Establish `hdens : ∀ j y, locDens A Φ j y = 1`.

Introduce `j y`. Simplify using `[locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]`. Establish `hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1`. Simplify using `[Measure.real, volume_pi]`. Rewrite using `[ReciprocityTheory.AnForm.M.mInt, dif_pos hpart]`.

Use `set Q := hpart.some`. Establish `hterm : ∀ j, ∫ y in (A.chart j).target, Q.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y = Q.χ j x₀`. Introduce `j`. Distinguish the cases in `hT : (default : Fin 0 → ℂ) ∈ (A.chart j).target`. Establish `hU : (A.chart j).target = Set.univ` using `Set.eq_univ_of_forall fun y => Subsingleton.elim default y ▸ hT`.

Rewrite using `[hU, Measure.restrict_univ, integral_unique, hvol, one_smul, hdens, mul_one, mul_one]`. Conclude with `congrArg (Q.χ j) (hX _)`. Establish `hE : (A.chart j).target = ∅` using `Set.eq_empty_of_forall_notMem fun y hy => hT (Subsingleton.elim y default ▸ hy)`. Establish `hx : x₀ ∉ (A.chart j).source` using `fun h => by`. Use `(A.chart j).map_source h` as an intermediate fact.

Rewrite `this` using `[hE]`. Conclude with `this`. Rewrite using `[hE, Measure.restrict_empty, integral_zero_measure, image_eq_zero_of_notMem_tsupport fun h => hx (Q.tsupport_subset j h)]`. Use `show ∑ j, ∫ y in (A.chart j).target, Q.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y = 1`. Simplify using `only [hterm]`.

Conclude with `Q.sum_eq_one x₀`.
-/
theorem mInt_one_of_dim_zero (A : FinHolAtlas 0 X) (x₀ : X) (hX : ∀ x, x = x₀)
    (Φ : Fin 0 → LocPot X) : mInt A Φ (fun _ => 1) = 1 := by
  classical
  obtain ⟨j₀, hj₀⟩ := A.cover x₀
  have hpart : Nonempty (ChartPartition A) := by
    refine ⟨⟨fun j _ => if j = j₀ then 1 else 0, fun j k => contDiffOn_const, fun j x => ?_,
      fun j => ?_, fun x => by simp⟩⟩
    · split_ifs <;> norm_num
    · by_cases hj : j = j₀
      · subst hj
        intro x _
        rw [hX x]
        exact hj₀
      · have h0 : (fun _ : X => if j = j₀ then (1 : ℝ) else 0) = 0 := by
          funext x
          simp [hj]
        rw [h0, tsupport_zero]
        exact Set.empty_subset _
  have hdens : ∀ j y, locDens A Φ j y = 1 := by
    intro j y
    simp [locDens, ReciprocityTheory.AnForm.maDens, ReciprocityTheory.AnForm.mdisc_zero]
  have hvol : (volume : Measure (Fin 0 → ℂ)).real Set.univ = 1 := by
    simp [Measure.real, volume_pi]
  rw [ReciprocityTheory.AnForm.M.mInt, dif_pos hpart]
  set Q := hpart.some
  have hterm : ∀ j, ∫ y in (A.chart j).target, Q.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y =
      Q.χ j x₀ := by
    intro j
    by_cases hT : (default : Fin 0 → ℂ) ∈ (A.chart j).target
    · have hU : (A.chart j).target = Set.univ :=
        Set.eq_univ_of_forall fun y => Subsingleton.elim default y ▸ hT
      rw [hU, Measure.restrict_univ, integral_unique, hvol, one_smul, hdens, mul_one, mul_one]
      exact congrArg (Q.χ j) (hX _)
    · have hE : (A.chart j).target = ∅ :=
        Set.eq_empty_of_forall_notMem fun y hy => hT (Subsingleton.elim y default ▸ hy)
      have hx : x₀ ∉ (A.chart j).source := fun h => by
        have := (A.chart j).map_source h
        rw [hE] at this
        exact this
      rw [hE, Measure.restrict_empty, integral_zero_measure,
        image_eq_zero_of_notMem_tsupport fun h => hx (Q.tsupport_subset j h)]
  show ∑ j, ∫ y in (A.chart j).target, Q.χ j ((A.chart j).symm y) * 1 * locDens A Φ j y = 1
  simp only [hterm]
  exact Q.sum_eq_one x₀

end Point

/- English proof (translation)
Introduce `K _ _ ι _ P φ hP hR`. Unfold `zInt`. Rewrite using `[dif_pos hR]`. Take `⟨x₀, hx₀⟩` from `Res.eq_of_isProjVar_zero hP hR.some`. Conclude with `mInt_one_of_dim_zero hR.some.atlas x₀ hx₀ _`.
-/
theorem ZIntPoint.proof : ZIntPoint.Statement := by
  intro K _ _ ι _ P φ hP hR
  unfold zInt
  rw [dif_pos hR]
  obtain ⟨x₀, hx₀⟩ := Res.eq_of_isProjVar_zero hP hR.some
  exact mInt_one_of_dim_zero hR.some.atlas x₀ hx₀ _

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
