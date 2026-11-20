import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.SdUniq

noncomputable section

namespace PI.VolStabSW

namespace VolAAW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes SdUniqW

def CondAA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ᶠ v in cofinite, ∀ t : Fv F v,
      (∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (s * t) = 1) ↔ t ∈ v.adicCompletionIntegers F

section Vol

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]

/- English proof (translation)
Use `hμ.1` as an intermediate fact. Use `set c : ℝ := μ.real (L : Set V) with hc`. Establish `hcl : IsClopen (L : Set V)` using `⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩`. Use `set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ`. Establish `hΦc : Continuous Φ`.

Rewrite using `[hΦ, ← Set.piecewise_eq_indicator]`. Conclude with `continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const`. Establish `hΦs : HasCompactSupport Φ` using `HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _`. Establish `hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y`. Introduce `y`.

Rewrite using `[hΦ, transform_indicator μ χ hχ L hLo y, hA]`. Establish `hfin : μ (L : Set V) < ⊤` using `hLc.measure_lt_top`. Establish `hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ`. Establish `e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ))`. Use function extensionality and compare the values at `hT`.

Rewrite using `[e, integrable_indicator_iff hLo.measurableSet]`. Conclude with `integrableOn_const hfin.ne`. Establish `h0` using `hμ.2 Φ hΦc hΦs hI 0`. Establish `e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0)`. Use function extensionality and compare the values at `y`.

Rewrite using `[hT y]`. Apply the tactic sequence `by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]`. Rewrite `h0` using `[e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA, Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero, Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)]`. Establish `h1 : c * c = 1` using `by exact_mod_cast h0`. Establish `hc0 : 0 ≤ c` using `measureReal_nonneg`.

Establish `hc1 : c = 1` using `by nlinarith`. Rewrite `hc1` using `[hc, measureReal_def, ENNReal.toReal_eq_one_iff]`. Conclude with `hc1`.
-/
theorem vol_one_of_ann {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) (hA : ann χ (L : Set V) = L) :
    μ (L : Set V) = 1 := by
  classical
  have := hμ.1
  set c : ℝ := μ.real (L : Set V) with hc
  have hcl : IsClopen (L : Set V) := ⟨AddSubgroup.isClosed_of_isOpen L hLo, hLo⟩
  set Φ : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hΦ
  have hΦc : Continuous Φ := by
    rw [hΦ, ← Set.piecewise_eq_indicator]
    exact continuous_const.piecewise (by simp [hcl.frontier_eq]) continuous_const
  have hΦs : HasCompactSupport Φ :=
    HasCompactSupport.intro hLc fun x hx => Set.indicator_of_notMem hx _
  have hT : ∀ y, ∫ x, Φ x * χ x y ∂μ = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) y := by
    intro y
    rw [hΦ, transform_indicator μ χ hχ L hLo y, hA]
  have hfin : μ (L : Set V) < ⊤ := hLc.measure_lt_top
  have hI : Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ := by
    have e : (fun y => ∫ x, Φ x * χ x y ∂μ) = (L : Set V).indicator (fun _ => ((c : ℝ) : ℂ)) :=
      funext hT
    rw [e, integrable_indicator_iff hLo.measurableSet]
    exact integrableOn_const hfin.ne
  have h0 := hμ.2 Φ hΦc hΦs hI 0
  have e1 : (fun y => (∫ x, Φ x * χ x y ∂μ) * χ y 0) = fun y => ((c : ℝ) : ℂ) * (Φ y * χ y 0) := by
    funext y
    rw [hT y]
    by_cases hy : y ∈ (L : Set V) <;> simp [hΦ, hy]
  rw [e1, integral_const_mul, hΦ, transform_indicator μ χ hχ L hLo 0, hA,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem), neg_zero,
    Set.indicator_of_mem (SetLike.mem_coe.2 L.zero_mem)] at h0
  have h1 : c * c = 1 := by exact_mod_cast h0
  have hc0 : 0 ≤ c := measureReal_nonneg
  have hc1 : c = 1 := by nlinarith
  rw [hc, measureReal_def, ENNReal.toReal_eq_one_iff] at hc1
  exact hc1

end Vol

section Ann

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`. Rewrite using `[← hD]`. Introduce `x hx`.

Rewrite using `[← hC]`. Introduce `s hs'`. Take `⟨x', hx', h⟩` from `hs s hs' x hx`. Rewrite using `[← h y]`. Conclude with `hy x' hx'`.

Introduce `hy`. Rewrite `hy` using `[← hD]`. Introduce `x hx`. Establish `ht` using `(hC _).2 (hy x hx) 1 (one_mem _)`. Simplify using `using ht`.
-/
theorem ann_eq {V : Type} (ψ0 : Fv F v → ℂ) (B : V → V → Fv F v) (L : Set V)
    (hC : ∀ t : Fv F v, (∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) ↔
      t ∈ v.adicCompletionIntegers F)
    (hs : ∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y)
    (hD : {y | ∀ x ∈ L, B x y ∈ v.adicCompletionIntegers F} = L) :
    ann (fun x y => ψ0 (B x y)) L = L := by
  ext y
  constructor
  · intro hy
    rw [← hD]
    intro x hx
    rw [← hC]
    intro s hs'
    obtain ⟨x', hx', h⟩ := hs s hs' x hx
    rw [← h y]
    exact hy x' hx'
  · intro hy
    rw [← hD] at hy
    intro x hx
    have ht := (hC _).2 (hy x hx) 1 (one_mem _)
    simpa using ht

/- English proof (translation)
Establish `hfin` using `HeightOneSpectrum.Support.finite (𝓞 F) f`. Use `hfin.eventually_cofinite_notMem.mono fun v hv => ?_` and prove the remaining obligations. Simplify using `only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `: Valued.v ((f : v.adicCompletion F)) = v.valuation F f` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f`.

Conclude with `(this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)`.
-/
theorem ev_int (f : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) f ∈ (v.adicCompletionIntegers F) := by
  have hfin := HeightOneSpectrum.Support.finite (𝓞 F) f
  refine hfin.eventually_cofinite_notMem.mono fun v hv => ?_
  simp only [HeightOneSpectrum.Support, Set.mem_setOf_eq, not_lt] at hv
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have : Valued.v ((f : v.adicCompletion F)) = v.valuation F f :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v f
  exact (this ▸ hv : Valued.v ((f : v.adicCompletion F)) ≤ 1)

/- English proof (translation)
The claim follows from `Filter.eventually_all.2 fun i => ev_int (f i)`.
-/
theorem ev_int_all {ι : Type} [Finite ι] (f : ι → F) :
    ∀ᶠ v in cofinite, ∀ i, algebraMap F (Fv F v) (f i) ∈ (v.adicCompletionIntegers F) :=
  Filter.eventually_all.2 fun i => ev_int (f i)

end Ann

end VolAAW

end PI.VolStabSW
