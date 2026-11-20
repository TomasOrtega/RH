import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabS

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def TestEx {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  ∃ Φ : V → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ ∧ ∃ z, Φ (-z) ≠ 0

/- English proof (translation)
Take `⟨hHμ, hμi⟩` from `hμ`. Take `⟨hHν, hνi⟩` from `hν`. Use `haveI := hHμ`. Use `haveI := hHν`. Take `⟨Φ, hc, hcs, hi, z, hz⟩` from `hT`.

Take `⟨c, hνμ⟩ : ∃ c : NNReal, ν = c • μ` from `by first`. Consider the case `exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩`. Consider the case `exact ⟨_, Measure.isAddHaarMeasure_eq_smul ν μ⟩`. Establish `e1` using `hμi Φ hc hcs hi z`. Establish `hsm : ∀ w : ℂ, c • w = ((c : ℝ) : ℂ) * w`.

Introduce `w`. Use `first`. Consider the case `rw [NNReal.smul_def, Complex.real_smul]`. Consider the case `simp [NNReal.smul_def]`. Establish `hTν : ∀ y, ∫ x, Φ x * χ x y ∂ν = ((c : ℝ) : ℂ) * ∫ x, Φ x * χ x y ∂μ`.

Introduce `y`. Rewrite using `[hνμ, integral_smul_nnreal_measure, hsm]`. Establish `hiν : Integrable (fun y => ∫ x, Φ x * χ x y ∂ν) ν`. Repeatedly rewrite using `[hTν]`. Rewrite using `[hνμ]`.

Use `first`. Consider the case `exact (hi.const_mul _).smul_measure_nnreal`. Consider the case `exact (hi.const_mul _).smul_measure ENNReal.coe_ne_top`. Establish `e2` using `hνi Φ hc hcs hiν z`. Rewrite `e2` using `[hTν]`.

Rewrite `e2` using `[hνμ, integral_smul_nnreal_measure, hsm]`. Rewrite `e2` using `[mul_assoc, integral_const_mul]`. Rewrite `e2` using `[e1]`. Establish `h4 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1`. Establish `h3 : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * Φ (-z) = 0` using `by linear_combination e2`.

Break down `mul_eq_zero.1 h3 with h | h` into its components or cases. Conclude with `sub_eq_zero.1 h`. Conclude with `absurd h hz`. Establish `h5 : (c : ℝ) * (c : ℝ) = 1` using `by exact_mod_cast h4`. Establish `h6 : (c : ℝ) = 1` using `by nlinarith [c.coe_nonneg]`.

Establish `h7 : c = 1` using `by exact_mod_cast h6`. Rewrite using `[hνμ, h7, one_smul]`.
-/
theorem eq_of_testEx {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (hT : TestEx μ χ) : μ = ν := by
  obtain ⟨hHμ, hμi⟩ := hμ
  obtain ⟨hHν, hνi⟩ := hν
  haveI := hHμ
  haveI := hHν
  obtain ⟨Φ, hc, hcs, hi, z, hz⟩ := hT
  obtain ⟨c, hνμ⟩ : ∃ c : NNReal, ν = c • μ := by
    first
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩
    | exact ⟨_, Measure.isAddHaarMeasure_eq_smul ν μ⟩
  have e1 := hμi Φ hc hcs hi z
  have hsm : ∀ w : ℂ, c • w = ((c : ℝ) : ℂ) * w := by
    intro w
    first
    | rw [NNReal.smul_def, Complex.real_smul]
    | simp [NNReal.smul_def]
  have hTν : ∀ y, ∫ x, Φ x * χ x y ∂ν = ((c : ℝ) : ℂ) * ∫ x, Φ x * χ x y ∂μ := by
    intro y
    rw [hνμ, integral_smul_nnreal_measure, hsm]
  have hiν : Integrable (fun y => ∫ x, Φ x * χ x y ∂ν) ν := by
    simp_rw [hTν]
    rw [hνμ]
    first
    | exact (hi.const_mul _).smul_measure_nnreal
    | exact (hi.const_mul _).smul_measure ENNReal.coe_ne_top
  have e2 := hνi Φ hc hcs hiν z
  simp_rw [hTν] at e2
  rw [hνμ, integral_smul_nnreal_measure, hsm] at e2
  simp_rw [mul_assoc, integral_const_mul] at e2
  rw [e1] at e2
  have h4 : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) = 1 := by
    have h3 : (((c : ℝ) : ℂ) * ((c : ℝ) : ℂ) - 1) * Φ (-z) = 0 := by linear_combination e2
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hz
  have h5 : (c : ℝ) * (c : ℝ) = 1 := by exact_mod_cast h4
  have h6 : (c : ℝ) = 1 := by nlinarith [c.coe_nonneg]
  have h7 : c = 1 := by exact_mod_cast h6
  rw [hνμ, h7, one_smul]

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)

include hχ in

/- English proof (translation)
Distinguish the cases in `hy : y ∈ ann χ (L : Set V)`. Rewrite using `[Set.indicator_of_mem hy]`. Establish `hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) = (L : Set V).indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ L`.

Simplify using `[Set.indicator_apply, hx, hy x hx]`. Simplify using `[Set.indicator_apply, hx]`. Rewrite using `[hfun, integral_indicator_const _ hLo.measurableSet]`. Simplify using `[Measure.real]`. Rewrite using `[Set.indicator_apply, if_neg hy]`.

Simplify using `only [ann, Set.mem_setOf_eq, not_forall] at hy`. Take `⟨x0, hx0, hne⟩` from `hy`. Use `set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf`. Establish `key : ∫ x, f (x0 + x) ∂μ = ∫ x, f x ∂μ` using `integral_add_left_eq_self (μ := μ) f x0`. Establish `hshift : ∀ x, f (x0 + x) = χ x0 y * f x`.

Introduce `x`. Simplify using `only [hf]`. Rewrite using `[hχ x x0 y]`. Distinguish the cases in `hx : x ∈ L`. Establish `hx' : x0 + x ∈ L` using `L.add_mem hx0 hx`.

Simplify using `[Set.indicator_apply, hx, hx']`. Establish `hx' : x0 + x ∉ L` using `fun h => hx (by simpa using L.sub_mem h hx0)`. Simplify using `[Set.indicator_apply, hx, hx']`. Rewrite `key` using `[hshift, integral_const_mul]`. Establish `h2 : (χ x0 y - 1) * ∫ x, f x ∂μ = 0` using `by rw [sub_mul, key, one_mul, sub_self]`.

Break down `mul_eq_zero.1 h2 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h) hne`. Conclude with `h`.
-/
theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ (L : Set V)
  · rw [Set.indicator_of_mem hy]
    have hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ L
      · simp [Set.indicator_apply, hx, hy x hx]
      · simp [Set.indicator_apply, hx]
    rw [hfun, integral_indicator_const _ hLo.measurableSet]
    simp [Measure.real]
  · rw [Set.indicator_apply, if_neg hy]
    simp only [ann, Set.mem_setOf_eq, not_forall] at hy
    obtain ⟨x0, hx0, hne⟩ := hy
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have key : ∫ x, f (x0 + x) ∂μ = ∫ x, f x ∂μ := integral_add_left_eq_self (μ := μ) f x0
    have hshift : ∀ x, f (x0 + x) = χ x0 y * f x := by
      intro x
      simp only [hf]
      rw [hχ x x0 y]
      by_cases hx : x ∈ L
      · have hx' : x0 + x ∈ L := L.add_mem hx0 hx
        simp [Set.indicator_apply, hx, hx']
      · have hx' : x0 + x ∉ L := fun h => hx (by simpa using L.sub_mem h hx0)
        simp [Set.indicator_apply, hx, hx']
    simp_rw [hshift, integral_const_mul] at key
    have h2 : (χ x0 y - 1) * ∫ x, f x ∂μ = 0 := by rw [sub_mul, key, one_mul, sub_self]
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd (sub_eq_zero.1 h) hne
    · exact h

include hχ in

/- English proof (translation)
Establish `hLcl : IsClosed (L : Set V)` using `hLc.isClosed`. Use `⟨(L : Set V).indicator (fun _ => (1 : ℂ)), ?_, ?_, ?_, ⟨0, ?_⟩⟩` and prove the remaining obligations. Use `first`. Consider the case `exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const`. Consider the case `exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn`.

Conclude with `HasCompactSupport.intro hLc (fun x hx => by simp [Set.indicator_apply, hx])`. Establish `hT : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) = (ann χ (L : Set V)).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ))`. Use function extensionality and compare the values at `y`. Conclude with `transform_indicator μ χ hχ L hLo y`. Rewrite using `[hT]`.

Establish `hfin : μ (ann χ (L : Set V)) < ⊤` using `(measure_mono hAK).trans_lt hK.measure_lt_top`. Use `IntegrableOn.integrable_indicator ?_ hA.measurableSet` and prove the remaining obligations. Use `first`. Consider the case `exact integrableOn_const.2 (Or.inr hfin)`. Consider the case `exact integrableOn_const hfin.ne`.

Consider the case `exact integrableOn_const_iff.2 (Or.inr hfin)`. Simplify using `[Set.indicator_apply, L.zero_mem]`.
-/
theorem testEx_of_lattice (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hA : IsClosed (ann χ L)) (K : Set V) (hK : IsCompact K) (hAK : ann χ L ⊆ K) :
    TestEx μ χ := by
  classical
  have hLcl : IsClosed (L : Set V) := hLc.isClosed
  refine ⟨(L : Set V).indicator (fun _ => (1 : ℂ)), ?_, ?_, ?_, ⟨0, ?_⟩⟩
  · first
    | exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const
    | exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn
  · exact HasCompactSupport.intro hLc (fun x hx => by simp [Set.indicator_apply, hx])
  · have hT : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) =
        (ann χ (L : Set V)).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) := by
      funext y
      exact transform_indicator μ χ hχ L hLo y
    rw [hT]
    have hfin : μ (ann χ (L : Set V)) < ⊤ := (measure_mono hAK).trans_lt hK.measure_lt_top
    refine IntegrableOn.integrable_indicator ?_ hA.measurableSet
    first
    | exact integrableOn_const.2 (Or.inr hfin)
    | exact integrableOn_const hfin.ne
    | exact integrableOn_const_iff.2 (Or.inr hfin)
  · simp [Set.indicator_apply, L.zero_mem]

end Lattice

def AnnAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (χ : V → V → ℂ) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsClosed (ann χ L) ∧
    ∃ K, IsCompact K ∧ ann χ L ⊆ K

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

/- English proof (translation)
Establish `hLcl : IsClosed (L : Set V)` using `hLc.isClosed`. Establish `hind : Continuous ((L : Set V).indicator (fun _ => (1 : ℂ)))` using `by first`. Consider the case `exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const`. Consider the case `exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn`. Establish `hfin : μ (L : Set V) < ⊤` using `hLc.measure_lt_top`.

Establish `hint : Integrable ((L : Set V).indicator (fun _ => (1 : ℂ))) μ`. Use `IntegrableOn.integrable_indicator ?_ hLo.measurableSet` and prove the remaining obligations. Use `first`. Consider the case `exact integrableOn_const.2 (Or.inr hfin)`. Consider the case `exact integrableOn_const hfin.ne`.

Consider the case `exact integrableOn_const_iff.2 (Or.inr hfin)`. Distinguish the cases in `hL : ∀ t, t ∈ L`. Use `haveI : IsFiniteMeasure μ := ⟨(measure_mono (fun x _ => hL x)).trans_lt hfin⟩`. Use `⟨fun _ => 1, continuous_const, HasCompactSupport.intro hLc (fun x hx => absurd (hL x) hx), ?_, ⟨0, one_ne_zero⟩⟩` and prove the remaining obligations. Simplify using `only [hχ, mul_one]`.

Conclude with `integrable_const _`. Use `push_neg at hL`. Take `⟨t, ht⟩` from `hL`. Use `set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg`. Establish `hcg : Continuous fun x => g (-t + x)` using `hind.comp' (continuous_add_left (-t))`.

Use `⟨fun x => g x - g (-t + x), hind.sub hcg, ?_, ?_, ⟨0, ?_⟩⟩` and prove the remaining obligations. Use `HasCompactSupport.intro (hLc.union (hLc.image (continuous_add_left t))) ?_` and prove the remaining obligations. Introduce `x hx`. Establish `h1 : x ∉ L` using `fun h => hx (Or.inl h)`. Establish `h2 : -t + x ∉ L` using `fun h => hx (Or.inr ⟨-t + x, h, by abel⟩)`.

Simplify using `[hg, Set.indicator_apply, h1, h2]`. Establish `h0 : ∀ y, ∫ x, (g x - g (-t + x)) * χ x y ∂μ = 0`. Introduce `y`. Simplify using `only [hχ, mul_one]`. Rewrite using `[integral_sub hint (hint.comp_add_left (-t)), integral_add_left_eq_self (μ := μ) g (-t), sub_self]`.

Simplify using `only [h0]`. Conclude with `integrable_zero _ _ _`. Establish `hn : -t ∉ L` using `fun h => ht (by simpa using L.neg_mem h)`. Simplify using `[hg, Set.indicator_apply, hn, ht, L.zero_mem]`.
-/
theorem testEx_of_trivial (hχ : ∀ x y, χ x y = 1) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) : TestEx μ χ := by
  classical
  have hLcl : IsClosed (L : Set V) := hLc.isClosed
  have hind : Continuous ((L : Set V).indicator (fun _ => (1 : ℂ))) := by
    first
    | exact IsClopen.continuous_indicator ⟨hLcl, hLo⟩ continuous_const
    | exact continuous_indicator (by simp [IsClopen.frontier_eq ⟨hLcl, hLo⟩]) continuous_const.continuousOn
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hint : Integrable ((L : Set V).indicator (fun _ => (1 : ℂ))) μ := by
    refine IntegrableOn.integrable_indicator ?_ hLo.measurableSet
    first
    | exact integrableOn_const.2 (Or.inr hfin)
    | exact integrableOn_const hfin.ne
    | exact integrableOn_const_iff.2 (Or.inr hfin)
  by_cases hL : ∀ t, t ∈ L
  · haveI : IsFiniteMeasure μ := ⟨(measure_mono (fun x _ => hL x)).trans_lt hfin⟩
    refine ⟨fun _ => 1, continuous_const, HasCompactSupport.intro hLc (fun x hx => absurd (hL x) hx), ?_, ⟨0, one_ne_zero⟩⟩
    simp only [hχ, mul_one]
    exact integrable_const _
  · push_neg at hL
    obtain ⟨t, ht⟩ := hL
    set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg
    have hcg : Continuous fun x => g (-t + x) := hind.comp' (continuous_add_left (-t))
    refine ⟨fun x => g x - g (-t + x), hind.sub hcg, ?_, ?_, ⟨0, ?_⟩⟩
    · refine HasCompactSupport.intro (hLc.union (hLc.image (continuous_add_left t))) ?_
      intro x hx
      have h1 : x ∉ L := fun h => hx (Or.inl h)
      have h2 : -t + x ∉ L := fun h => hx (Or.inr ⟨-t + x, h, by abel⟩)
      simp [hg, Set.indicator_apply, h1, h2]
    · have h0 : ∀ y, ∫ x, (g x - g (-t + x)) * χ x y ∂μ = 0 := by
        intro y
        simp only [hχ, mul_one]
        rw [integral_sub hint (hint.comp_add_left (-t)), integral_add_left_eq_self (μ := μ) g (-t), sub_self]
      simp only [h0]
      exact integrable_zero _ _ _
    · have hn : -t ∉ L := fun h => ht (by simpa using L.neg_mem h)
      simp [hg, Set.indicator_apply, hn, ht, L.zero_mem]

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

/- English proof (translation)
Establish `hr0 : r0 ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)`. Distinguish the cases in `ht0 : t = 0`. Conclude with `⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩`.

Break down `(v.adicCompletionIntegers F).mem_or_inv_mem (t / r0) with h | h` into its components or cases. Use `⟨t / r0, h, ?_⟩ show r0 * (t / r0) = t` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises.

Establish `h1` using `ht _ h`. Establish `e : (t / r0)⁻¹ * t = r0` using `by field_simp`. Rewrite `h1` using `[e]`. Then use the resulting hypothesis.
-/
theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  have hr0 : r0 ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)
  by_cases ht0 : t = 0
  · exact ⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩
  rcases (v.adicCompletionIntegers F).mem_or_inv_mem (t / r0) with h | h
  · refine ⟨t / r0, h, ?_⟩
    show r0 * (t / r0) = t
    field_simp
  · exfalso
    apply h0
    have h1 := ht _ h
    have e : (t / r0)⁻¹ * t = r0 := by field_simp
    rwa [e] at h1

/- English proof (translation)
Take `⟨L, hLc, hLo, hst, hdual⟩` from `hD`. Take `⟨K, hK, hsub⟩` from `hdual r0`. Use `⟨L, hLc, hLo, ?_, K, hK, ?_⟩` and prove the remaining obligations. Establish `hE : ann (fun x y => ψ0 (B x y)) (L : Set V) = ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1}`. Use extensionality with `y`.

Simplify using `[ann]`. Rewrite using `[hE]`. Conclude with `isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))`. Introduce `y hy`. Use `hsub (fun x hx => ?_)` and prove the remaining obligations.

Use `mem_of_psi v ψ0 r0 (B x y) h0 (fun s hs => ?_)` and prove the remaining obligations. Take `⟨x', hx', hB'⟩` from `hst s hs x hx`. Rewrite using `[← hB' y]`. Conclude with `hy x' hx'`.
-/
theorem annAt_of_dual {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v)
    (ψ0 : Fv F v → ℂ) (hψ : Continuous ψ0) (hB : ∀ x, Continuous (B x)) (r0 : Fv F v)
    (h0 : ψ0 r0 ≠ 1) (hD : DualAt v B) : AnnAt (fun x y => ψ0 (B x y)) := by
  obtain ⟨L, hLc, hLo, hst, hdual⟩ := hD
  obtain ⟨K, hK, hsub⟩ := hdual r0
  refine ⟨L, hLc, hLo, ?_, K, hK, ?_⟩
  · have hE : ann (fun x y => ψ0 (B x y)) (L : Set V) =
        ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1} := by
      ext y
      simp [ann]
    rw [hE]
    exact isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))
  · intro y hy
    refine hsub (fun x hx => ?_)
    refine mem_of_psi v ψ0 r0 (B x y) h0 (fun s hs => ?_)
    obtain ⟨x', hx', hB'⟩ := hst s hs x hx
    rw [← hB' y]
    exact hy x' hx'

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
/- English proof (translation)
Unfold `singleV`. Use `first`. Consider the case `exact RestrictedProduct.single_add _ v r s`. Consider the case `(ext w`. Distinguish the cases in `hw : w = v`.

Substitute `hw` using the available equality. Simplify using `[RestrictedProduct.single]`. Simplify using `[RestrictedProduct.single, hw])`.
-/
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  unfold singleV
  first
  | exact RestrictedProduct.single_add _ v r s
  | (ext w
     by_cases hw : w = v
     · subst hw; simp [RestrictedProduct.single]
     · simp [RestrictedProduct.single, hw])

/- English proof (translation)
Establish `e : pairA F 0 (singleV F v (r + s)) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s)`. Rewrite using `[singleV_add]`. Rewrite using `[show (pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) : AF F) = pairA F (0 + 0) (singleV F v r + singleV F v s) from rfl, add_zero]`. Use `show ψ (pairA F 0 (singleV F v (r + s))) = ψ (pairA F 0 (singleV F v r)) * ψ (pairA F 0 (singleV F v s))`. Rewrite using `[e, AddChar.map_add_eq_mul]`.
-/
theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  have e : pairA F 0 (singleV F v (r + s)) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := by
    rw [singleV_add]
    rw [show (pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) : AF F) =
      pairA F (0 + 0) (singleV F v r + singleV F v s) from rfl, add_zero]
  show ψ (pairA F 0 (singleV F v (r + s))) =
    ψ (pairA F 0 (singleV F v r)) * ψ (pairA F 0 (singleV F v s))
  rw [e, AddChar.map_add_eq_mul]

/- English proof (translation)
Establish `e : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0`. Rewrite using `[show (pairA F r 0 + pairA F s 0 : AF F) = pairA F (r + s) (0 + 0) from rfl, add_zero]`. Use `show ψ (pairA F (r + s) 0) = ψ (pairA F r 0) * ψ (pairA F s 0)`. Rewrite using `[e, AddChar.map_add_eq_mul]`.
-/
theorem psiInf_add (ψ : AddChar (AF F) ℂ) (r s : Ainf F) :
    psiInf F ψ (r + s) = psiInf F ψ r * psiInf F ψ s := by
  have e : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0 := by
    rw [show (pairA F r 0 + pairA F s 0 : AF F) = pairA F (r + s) (0 + 0) from rfl, add_zero]
  show ψ (pairA F (r + s) 0) = ψ (pairA F r 0) * ψ (pairA F s 0)
  rw [e, AddChar.map_add_eq_mul]

/- English proof (translation)
Establish `hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))` using `Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite`. Set `s0 : Fv F v → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))))` to `fun y => ⟨Pi.single v y, Filter.eventually_principal.2 fun w hw => by`. Rewrite using `[Pi.single_eq_of_ne (by simpa using hw)]`. Conclude with `zero_mem _⟩`. Establish `hc : Continuous s0`.

Rewrite using `[RestrictedProduct.continuous_rng_of_principal_iff_forall]`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Conclude with `continuous_id.congr fun y => (Pi.single_eq_same _ _).symm`.

Conclude with `(continuous_const (y := (0 : Fv F w))).congr fun y => (Pi.single_eq_of_ne hw y).symm`. Establish `e : singleV F v = fun y => RestrictedProduct.inclusion _ _ hS (s0 y)`. Use function extensionality and compare the values at `y`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `j`.

Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `(RestrictedProduct.continuous_inclusion hS).comp hc`.
-/
theorem continuous_singleV (v : HeightOneSpectrum (𝓞 F)) : Continuous (singleV F v) := by
  classical
  have hS : Filter.cofinite ≤ Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
    Filter.le_principal_iff.2 (Set.finite_singleton v).compl_mem_cofinite
  let s0 : Fv F v → RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (Filter.principal ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) := fun y =>
    ⟨Pi.single v y, Filter.eventually_principal.2 fun w hw => by
      rw [Pi.single_eq_of_ne (by simpa using hw)]
      exact zero_mem _⟩
  have hc : Continuous s0 := by
    rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
    intro w
    by_cases hw : w = v
    · subst hw
      exact continuous_id.congr fun y => (Pi.single_eq_same _ _).symm
    · exact (continuous_const (y := (0 : Fv F w))).congr fun y => (Pi.single_eq_of_ne hw y).symm
  have e : singleV F v = fun y => RestrictedProduct.inclusion _ _ hS (s0 y) := by
    funext y
    apply RestrictedProduct.ext
    intro j
    rfl
  rw [e]
  exact (RestrictedProduct.continuous_inclusion hS).comp hc

/- English proof (translation)
Unfold `psiV`. Use `first`. Consider the case `exact hψ.comp (continuous_const.prodMk (continuous_singleV (F := F) v))`. Consider the case `exact hψ.comp (continuous_const.prod_mk (continuous_singleV (F := F) v))`.
-/
theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  first
  | exact hψ.comp (continuous_const.prodMk (continuous_singleV (F := F) v))
  | exact hψ.comp (continuous_const.prod_mk (continuous_singleV (F := F) v))

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Use `first`. Consider the case `simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Consider the case `simp [BR, hR, Formalism.UG.hform, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  first
  | simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  | simp [BR, hR, Formalism.UG.hform, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Use `first`. Consider the case `simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]`. Consider the case `simp [pairHerm, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]`.
-/
theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  first
  | simp only [pairHerm, AddSubgroup.coe_add, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]
  | simp [pairHerm, Matrix.add_apply, add_mul, Finset.sum_add_distrib, map_add, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

/- English proof (translation)
Use `first`. Consider the case `exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))`. Consider the case `exact IsModuleTopology.continuous_of_linearMap _`. Consider the case `exact LinearMap.continuous_of_finiteDimensional _`. Consider the case `fun_prop`.
-/
theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap (Algebra.trace R (R ⊗[F] E))
  | exact IsModuleTopology.continuous_of_linearMap _
  | exact LinearMap.continuous_of_finiteDimensional _
  | fun_prop

/- English proof (translation)
Establish `ht` using `continuous_trace_tens (F := F) (E := E) R`. Unfold `BR hR Formalism.UG.hform`. Use `first`. Consider the case `exact continuous_finset_sum _ fun a _ => ht.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))`. Consider the case `fun_prop`.
-/
theorem continuous_BR_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Continuous (BR R σ J X) := by
  have ht := continuous_trace_tens (F := F) (E := E) R
  unfold BR hR Formalism.UG.hform
  first
  | exact continuous_finset_sum _ fun a _ => ht.comp (continuous_finset_sum _ fun i _ =>
      continuous_finset_sum _ fun j _ => continuous_const.mul ((continuous_apply j).comp (continuous_apply a)))
  | fun_prop

/- English proof (translation)
Establish `ht` using `continuous_trace_tens (F := F) (E := E) R`. Unfold `pairHerm`. Use `first`. Consider the case `exact continuous_const.mul (ht.comp (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => continuous_const.mul ((continuous_apply a).comp ((continuous_apply b).comp continuous_subtype_val))))`. Consider the case `fun_prop`.
-/
theorem continuous_pairHerm_right (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) :
    Continuous (pairHerm R σ n S) := by
  have ht := continuous_trace_tens (F := F) (E := E) R
  unfold pairHerm
  first
  | exact continuous_const.mul (ht.comp (continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      continuous_const.mul ((continuous_apply a).comp ((continuous_apply b).comp continuous_subtype_val))))
  | fun_prop

end ContY

end SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW SdUniqW

def SdTestInf : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ →
    (∀ μ, SdW F E σ M J (Ainf F) (psiInf F ψ) a μ →
      TestEx μ (fun X Y => psiInf F ψ (BR (Ainf F) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Ainf F) (psiInf F ψ) a ν →
      TestEx ν (fun S T => psiInf F ψ (pairHerm (Ainf F) σ a S T)))

def SdTestV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ μ, SdW F E σ M J (Fv F v) (psiV F ψ v) a μ →
      TestEx μ (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y))) ∧
    (∀ ν, SdHerm F E σ (Fv F v) (psiV F ψ v) a ν →
      TestEx ν (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T)))

def AnnV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ ψ, IsCharAF F ψ → ∀ v : HeightOneSpectrum (𝓞 F),
    AnnAt (V := Fin a → Fin M → Fv F v ⊗[F] E) (fun X Y => psiV F ψ v (BR (Fv F v) σ J X Y)) ∧
    AnnAt (V := HermR (Fv F v) σ a) (fun S T => psiV F ψ v (pairHerm (Fv F v) σ a S T))

def DualLatV : Prop := InCtx fun F E _ _ _ _ _ σ M J a _X0 _hT =>
  ∀ v : HeightOneSpectrum (𝓞 F),
    DualAt v (BR (Fv F v) σ J (n := a)) ∧ DualAt v (pairHerm (Fv F v) σ a)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Use `secondCountable_Fv F v` as an intermediate fact. Use `locallyCompact_Fv F v` as an intermediate fact. Take `⟨hDW, hDH⟩` from `h F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v`.

Distinguish the cases in `hψv : ∃ r, psiV F ψ v r ≠ 1`. Take `⟨r0, h0⟩` from `hψv`. Establish `hc` using `continuous_psiV ψ hψ.1 v`. Take `⟨L, hLc, hLo, hA, K, hK, hAK⟩` from `annAt_of_dual v _ _ hc (fun X => continuous_BR_right (Fv F v) σ J X) r0 h0 hDW`. Take `⟨L', hLc', hLo', hA', K', hK', hAK'⟩` from `annAt_of_dual v _ _ hc (fun S => continuous_pairHerm_right (Fv F v) σ a S) r0 h0 hDH`.

Use `⟨fun μ hμ => ?_, fun ν hν => ?_⟩` and prove the remaining obligations. Use `hμ.1` as an intermediate fact. Conclude with `testEx_of_lattice μ _ (fun X T Y => by rw [BR_add, psiV_add]) L hLc hLo hA K hK hAK`. Use `hν.1` as an intermediate fact. Conclude with `testEx_of_lattice ν _ (fun S T U => by rw [pairHerm_add, psiV_add]) L' hLc' hLo' hA' K' hK' hAK'`.

Simplify using `only [not_exists, not_not] at hψv`. Take `⟨L, hLc, hLo, -⟩` from `hDW`. Take `⟨L', hLc', hLo', -⟩` from `hDH`. Use `⟨fun μ hμ => ?_, fun ν hν => ?_⟩` and prove the remaining obligations. Use `hμ.1` as an intermediate fact.

Conclude with `testEx_of_trivial μ _ (fun _ _ => hψv _) L hLc hLo`. Use `hν.1` as an intermediate fact. Conclude with `testEx_of_trivial ν _ (fun _ _ => hψv _) L' hLc' hLo'`.
-/
theorem sdTestV_of_dual (h : DualLatV) : SdTestV := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hDW, hDH⟩ := h F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet v
  by_cases hψv : ∃ r, psiV F ψ v r ≠ 1
  · obtain ⟨r0, h0⟩ := hψv
    have hc := continuous_psiV ψ hψ.1 v
    obtain ⟨L, hLc, hLo, hA, K, hK, hAK⟩ :=
      annAt_of_dual v _ _ hc (fun X => continuous_BR_right (Fv F v) σ J X) r0 h0 hDW
    obtain ⟨L', hLc', hLo', hA', K', hK', hAK'⟩ :=
      annAt_of_dual v _ _ hc (fun S => continuous_pairHerm_right (Fv F v) σ a S) r0 h0 hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_lattice μ _ (fun X T Y => by rw [BR_add, psiV_add]) L hLc hLo
        hA K hK hAK
    · have := hν.1
      exact testEx_of_lattice ν _ (fun S T U => by rw [pairHerm_add, psiV_add]) L'
        hLc' hLo' hA' K' hK' hAK'
  · simp only [not_exists, not_not] at hψv
    obtain ⟨L, hLc, hLo, -⟩ := hDW
    obtain ⟨L', hLc', hLo', -⟩ := hDH
    refine ⟨fun μ hμ => ?_, fun ν hν => ?_⟩
    · have := hμ.1
      exact testEx_of_trivial μ _ (fun _ _ => hψv _) L hLc hLo
    · have := hν.1
      exact testEx_of_trivial ν _ (fun _ _ => hψv _) L' hLc' hLo'

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Take `⟨hIW, hIH⟩` from `hI F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ`. Establish `: SecondCountableTopology (HermR (Ainf F) σ a)`. Establish `: SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))`.

Use the proof step `Topology.IsInducing.subtypeVal.secondCountableTopology`. Use `⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hIW μ1 e1), fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hIH ν1 e1), fun v => ?_⟩` and prove the remaining obligations. Use `secondCountable_Fv F v` as an intermediate fact. Use `locallyCompact_Fv F v` as an intermediate fact. Take `⟨hVW, hVH⟩` from `hV F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v`.

Establish `: SecondCountableTopology (HermR (Fv F v) σ a)`. Establish `: SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E))` using `inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))`. Use the proof step `Topology.IsInducing.subtypeVal.secondCountableTopology`. Conclude with `⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hVW μ1 e1), fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hVH ν1 e1)⟩`.
-/
theorem sdUniq_of (hI : SdTestInf) (hV : SdTestV) : SdUniq := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  obtain ⟨hIW, hIH⟩ := hI F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ
  have : SecondCountableTopology (HermR (Ainf F) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Ainf F ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Ainf F ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  refine ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hIW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hIH ν1 e1), fun v => ?_⟩
  have := secondCountable_Fv F v
  have := locallyCompact_Fv F v
  obtain ⟨hVW, hVH⟩ := hV F E σ hCM M J hJ h1 h2 a h3 h4 X0 hT hdet ψ hψ v
  have : SecondCountableTopology (HermR (Fv F v) σ a) :=
    have : SecondCountableTopology (Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) :=
      inferInstanceAs (SecondCountableTopology (Fin a → Fin a → Fv F v ⊗[F] E))
    Topology.IsInducing.subtypeVal.secondCountableTopology
  exact ⟨fun μ1 μ2 e1 e2 => eq_of_testEx e1 e2 (hVW μ1 e1),
    fun ν1 ν2 e1 e2 => eq_of_testEx e1 e2 (hVH ν1 e1)⟩

/- English proof (translation)
The claim follows from `sdUniq_of hI (sdTestV_of_dual hD)`.
-/
theorem sdUniq_of_dual (hI : SdTestInf) (hD : DualLatV) : SdUniq := sdUniq_of hI (sdTestV_of_dual hD)

end PI.VolStabS
