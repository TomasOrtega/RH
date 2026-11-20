import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.EvalBasis
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelDiagonalIntegrableHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiInvTop
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiVecExHolds
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiSeenA
import Development.DiscreteGroups.PiInvariants.CompactSupportTwists.PiClosT

open UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi DiscreteGroups.T1.G

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc PositivityTheory.Rg.BcB.E1
open scoped ENNReal

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section Meas

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
The claim follows from `(GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const`.
-/
private theorem continuous_ac' : Continuous (ac E n) :=
  (GlobalTheory.OneRep.SplitTwist.continuous_splitCentre.comp (continuous_id.div_const _)).prodMk continuous_const

/- English proof (translation)
Establish `hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1` using `continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)`. Use `haveI := borelSpace_H (E := E) (n := n)`. Use `letI : MeasurableSpace (GA E n) := borel _`. Use `haveI : BorelSpace (GA E n) := ⟨rfl⟩`. Conclude with `(redBasic E n).2.2.comp hc.measurable`.
-/
private theorem measurable_reduced_size : Measurable (r0 : H E n 0 → ℝ) := by
  have hc : Continuous fun x : H E n 0 => (ac E n (-ldet x) * x).1 :=
    continuous_fst.comp ((continuous_ac'.comp continuous_ldet.neg).mul continuous_id)
  haveI := borelSpace_H (E := E) (n := n)
  letI : MeasurableSpace (GA E n) := borel _
  haveI : BorelSpace (GA E n) := ⟨rfl⟩
  exact (redBasic E n).2.2.comp hc.measurable

/- English proof (translation)
Use `haveI := borelSpace_H (E := E) (n := n)`. Use `haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'`. Establish `hm : MeasurableSet Ω` using `hΩ.measurableSet`. Use `Measurable.ennreal_tsum fun γ => ?_` and prove the remaining obligations. Establish `hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x` using `(continuous_inv.mul continuous_const).mul continuous_id`.

Conclude with `(measurable_one.indicator hm).comp hc.measurable`.
-/
private theorem measurable_cnt {Ω : Set (H E n 0)} (hΩ : IsCompact Ω) :
    Measurable (cnt (ratH E n 0) Ω) := by
  haveI := borelSpace_H (E := E) (n := n)
  haveI : Countable (ratH E n 0) := DiscreteGroups.T1.G.Dcy.countable_ratH'
  have hm : MeasurableSet Ω := hΩ.measurableSet
  refine Measurable.ennreal_tsum fun γ => ?_
  have hc : Continuous fun x : H E n 0 => x⁻¹ * (γ : H E n 0) * x :=
    (continuous_inv.mul continuous_const).mul continuous_id
  exact (measurable_one.indicator hm).comp hc.measurable

end Meas

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

/- English proof (translation)
Introduce `hF hB hS hD E _ _ _ n ι _ s`. Use `haveI := borelSpace_H (E := E) (n := n)`. Take `⟨p, hp⟩` from `hF E n ι s`. Take `⟨Ω, hΩ, hC⟩` from `hB E n ι s`. Use `choose Cb hCb0 hCb using fun b => hC (p.x b)`.

Use `choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ`. Use `⟨Finset.univ.sup Nb, fun L hL => ?_⟩` and prove the remaining obligations. Use `choose Db hDb0 hDb using fun b => hNb b L hL`. Use `⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b), fun m R ρ hR hφ A hA => ?_⟩` and prove the remaining obligations. Use `set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef`.

Establish `hSm : MeasurableSet S` using `((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter (measurableSet_le measurable_const measurable_reduced_size)`. Use `set f : p.B → H E n 0 → ℝ≥0∞ := fun b => S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf`. Establish `hfm : ∀ b, Measurable (f b)` using `fun b => by`. Use `Measurable.indicator ?_ hSm` and prove the remaining obligations. Use `Measurable.mul ?_ (measurable_cnt hΩ)` and prove the remaining obligations.

Conclude with `(((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable`. Establish `hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤ ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x`. Introduce `x`. Distinguish the cases in `hxA : x ∈ A`. Rewrite using `[Set.indicator_of_mem hxA]`.

Distinguish the cases in `hx : |ldet x| ≤ R`. Establish `hxS : x ∈ S` using `⟨hx, hA x hxA hx⟩`. Rewrite using `[hp m x x]`. Use `(enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)` and prove the remaining obligations. Rewrite using `[enorm_mul, hf]`.

Simplify using `only [Set.indicator_of_mem hxS]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : m.G x x = 0`. Use `hS E n ι s m R hφ x x ?_` and prove the remaining obligations. Establish `h1 : R < |ldet x|` using `not_le.mp hx`.

Establish `h2 : |ldet x + ldet x| = 2 * |ldet x|`. Rewrite using `[← two_mul, abs_mul, abs_two]`. Rewrite using `[h2]`. Use `abs_nonneg (ldet x)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Simplify using `[h0]`. Rewrite using `[Set.indicator_of_notMem hxA]`. Conclude with `zero_le`. Establish `h1R : (1 : ℝ) ≤ 1 + R` using `by linarith`. Establish `hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤ ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ)))`.

Introduce `b`. Establish `hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb)` using `pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))`. Establish `h2 : ∫⁻ x, f b x ∂s.D.ν ≤ ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ)))`. Use `(hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)` and prove the remaining obligations. Use `hDb0 b` as an intermediate fact.

Establish `he` using `(Real.exp_pos (-(L * ρ))).le`. Use `gcongr`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[lintegral_finset_sum _ fun b _ => (hfm b).const_mul _]`. Conclude with `Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)`. Use `_ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := Finset.sum_le_sum fun b _ => hT b`.

Use `_ = _ := by`. Rewrite using `[← ENNReal.ofReal_sum_of_nonneg]`. Use `congr 1`. Simplify using `only [Finset.sum_mul]`. Introduce `b _`.

Use `mul_nonneg (hCb0 b) (hDb0 b)` as an intermediate fact. Establish `he` using `(Real.exp_pos (-(L * ρ))).le`. Establish `hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb)` using `by positivity`. Check the signs of the components of the expression.
-/
theorem UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi.tailInt_of_bounds :
    GFac → GBound → Supp → DomInt → TailInt := by
  intro hF hB hS hD E _ _ _ n ι _ s
  haveI := borelSpace_H (E := E) (n := n)
  obtain ⟨p, hp⟩ := hF E n ι s
  obtain ⟨Ω, hΩ, hC⟩ := hB E n ι s
  choose Cb hCb0 hCb using fun b => hC (p.x b)
  choose Nb hNb using fun b => hD E n s.pos s.D s.π s.fix (p.w b) (p.mem b) Ω hΩ
  refine ⟨Finset.univ.sup Nb, fun L hL => ?_⟩
  choose Db hDb0 hDb using fun b => hNb b L hL
  refine ⟨∑ b, Cb b * Db b, Finset.sum_nonneg fun b _ => mul_nonneg (hCb0 b) (hDb0 b),
    fun m R ρ hR hφ A hA => ?_⟩
  set S : Set (H E n 0) := {x | |ldet x| ≤ R ∧ ρ ≤ r0 x} with hSdef
  have hSm : MeasurableSet S :=
    ((isClosed_le (continuous_abs.comp continuous_ldet) continuous_const).measurableSet).inter
      (measurableSet_le measurable_const measurable_reduced_size)
  set f : p.B → H E n 0 → ℝ≥0∞ := fun b =>
    S.indicator (fun x => ‖(p.w b).1 x.1‖ₑ * cnt (ratH E n 0) Ω x) with hf
  have hfm : ∀ b, Measurable (f b) := fun b => by
    refine Measurable.indicator ?_ hSm
    refine Measurable.mul ?_ (measurable_cnt hΩ)
    exact (((continuous_of_mem s.π (p.mem b)).comp continuous_fst).enorm).measurable
  have hpt : ∀ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ≤
      ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x := by
    intro x
    by_cases hxA : x ∈ A
    · rw [Set.indicator_of_mem hxA]
      by_cases hx : |ldet x| ≤ R
      · have hxS : x ∈ S := ⟨hx, hA x hxA hx⟩
        rw [hp m x x]
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
        rw [enorm_mul, hf]
        simp only [Set.indicator_of_mem hxS]
        calc ‖(p.w b).1 x.1‖ₑ * ‖m.G (ac E n (ldet x) * p.x b) x‖ₑ
            ≤ ‖(p.w b).1 x.1‖ₑ * (ENNReal.ofReal (Cb b * ‖m.U‖) * cnt (ratH E n 0) Ω x) := by
              gcongr; exact hCb b m _ x
          _ = _ := by ring
      · have h0 : m.G x x = 0 := by
          refine hS E n ι s m R hφ x x ?_
          have h1 : R < |ldet x| := not_le.mp hx
          have h2 : |ldet x + ldet x| = 2 * |ldet x| := by
            rw [← two_mul, abs_mul, abs_two]
          rw [h2]
          have := abs_nonneg (ldet x)
          linarith
        simp [h0]
    · rw [Set.indicator_of_notMem hxA]
      exact zero_le
  have h1R : (1 : ℝ) ≤ 1 + R := by linarith
  have hT : ∀ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν ≤
      ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
    intro b
    have hpow : (1 + R) ^ Nb b ≤ (1 + R) ^ (Finset.univ.sup Nb) :=
      pow_le_pow_right₀ h1R (Finset.le_sup (Finset.mem_univ b))
    have h2 : ∫⁻ x, f b x ∂s.D.ν ≤
        ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by
      refine (hDb b R ρ hR).trans (ENNReal.ofReal_le_ofReal ?_)
      have := hDb0 b
      have he := (Real.exp_pos (-(L * ρ))).le
      gcongr
    calc _ ≤ ENNReal.ofReal (Cb b * ‖m.U‖) *
          ENNReal.ofReal (Db b * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) := by gcongr
      _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (hCb0 b) (norm_nonneg _))]
        congr 1
        ring
  calc ∫⁻ x, A.indicator (fun x => ‖m.G x x‖ₑ) x ∂s.D.ν
      ≤ ∫⁻ x, ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * f b x ∂s.D.ν := lintegral_mono hpt
    _ = ∑ b, ENNReal.ofReal (Cb b * ‖m.U‖) * ∫⁻ x, f b x ∂s.D.ν := by
        rw [lintegral_finset_sum _ fun b _ => (hfm b).const_mul _]
        exact Finset.sum_congr rfl fun b _ => lintegral_const_mul _ (hfm b)
    _ ≤ ∑ b, ENNReal.ofReal (Cb b * Db b * ‖m.U‖ * (1 + R) ^ (Finset.univ.sup Nb) * Real.exp (-(L * ρ))) :=
        Finset.sum_le_sum fun b _ => hT b
    _ = _ := by
        rw [← ENNReal.ofReal_sum_of_nonneg]
        · congr 1
          simp only [Finset.sum_mul]
        · intro b _
          have := mul_nonneg (hCb0 b) (hDb0 b)
          have he := (Real.exp_pos (-(L * ρ))).le
          have hp1 : 0 ≤ (1 + R) ^ (Finset.univ.sup Nb) := by positivity
          positivity

end
