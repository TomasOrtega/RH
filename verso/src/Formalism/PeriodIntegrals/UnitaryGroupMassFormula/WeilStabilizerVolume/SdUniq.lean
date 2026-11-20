import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.RestrProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensFibV
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace PI.VolStabW

namespace SdUniqW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW

def TestEx {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (χ : V → V → ℂ) : Prop :=
  ∃ Φ : V → ℂ, Continuous Φ ∧ HasCompactSupport Φ ∧
    Integrable (fun y => ∫ x, Φ x * χ x y ∂μ) μ ∧ ∃ z, Φ (-z) ≠ 0

/- English proof (translation)
Unfold `SelfDual at hμ hν`. Take `⟨hμH, hμI⟩` from `hμ`. Take `⟨hνH, hνI⟩` from `hν`. Take `⟨Φ, hc, hs, hi, z, hz⟩` from `hT`. Take `⟨c, rfl⟩ : ∃ c : NNReal, ν = c • μ` from `by first`.

Consider the case `exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩`. Consider the case `exact ⟨_, Measure.isAddHaarMeasure_eq_smul_of_regular ν μ⟩`. Consider the case `exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular ν μ⟩`. Consider the case `exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_innerRegular ν μ⟩`. Establish `h1` using `hμI Φ hc hs hi z`.

Establish `hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ)`. Simplify using `only [integral_smul_nnreal_measure, NNReal.smul_def]`. Conclude with `(hi.smul (c : ℝ)).smul_measure_nnreal`. Establish `h2` using `hνI Φ hc hs hi' z`. Rewrite `h2` using `[integral_smul_nnreal_measure, NNReal.smul_def, smul_mul_assoc, integral_smul, h1, smul_smul]`.

Establish `h3 : ((c : ℝ) * c - 1) • Φ (-z) = 0` using `by rw [sub_smul, one_smul, h2, sub_self]`. Break down `smul_eq_zero.1 h3 with h | h` into its components or cases. Establish `hx : (c : ℝ) = 1`. Break down `mul_self_eq_one_iff.1 (sub_eq_zero.1 h) with h' | h'` into its components or cases. Conclude with `h'`.

Combine the linear relations using `[c.2]`. Establish `hc1 : c = 1` using `by exact_mod_cast hx`. Rewrite using `[hc1, one_smul]`. Conclude with `absurd h hz`.
-/
theorem eq_of_testEx {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (hT : TestEx μ χ) : μ = ν := by
  unfold SelfDual at hμ hν
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  obtain ⟨Φ, hc, hs, hi, z, hz⟩ := hT
  obtain ⟨c, rfl⟩ : ∃ c : NNReal, ν = c • μ := by
    first
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩
    | exact ⟨_, Measure.isAddHaarMeasure_eq_smul_of_regular ν μ⟩
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular ν μ⟩
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_innerRegular ν μ⟩
  have h1 := hμI Φ hc hs hi z
  have hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp only [integral_smul_nnreal_measure, NNReal.smul_def]
    exact (hi.smul (c : ℝ)).smul_measure_nnreal
  have h2 := hνI Φ hc hs hi' z
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_mul_assoc, integral_smul, h1,
    smul_smul] at h2
  have h3 : ((c : ℝ) * c - 1) • Φ (-z) = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · have hx : (c : ℝ) = 1 := by
      rcases mul_self_eq_one_iff.1 (sub_eq_zero.1 h) with h' | h'
      · exact h'
      · linarith [c.2]
    have hc1 : c = 1 := by exact_mod_cast hx
    rw [hc1, one_smul]
  · exact absurd h hz

def ann {V : Type} (χ : V → V → ℂ) (L : Set V) : Set V := {y | ∀ x ∈ L, χ x y = 1}

section Lattice

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (L : AddSubgroup V)

include hχ in

/- English proof (translation)
Distinguish the cases in `hy : y ∈ ann χ L`. Rewrite using `[Set.indicator_of_mem hy]`. Establish `hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) = (L : Set V).indicator (fun _ => (1 : ℂ))`. Use function extensionality and compare the values at `x`. Distinguish the cases in `hx : x ∈ (L : Set V)`.

Rewrite using `[Set.indicator_of_mem hx, hy x hx, one_mul]`. Simplify using `[hx]`. Rewrite using `[hfun, integral_indicator_const _ hLo.measurableSet]`. Simplify using the standard rewrite rules. Establish `hy' : ∃ x0 ∈ (L : Set V), χ x0 y ≠ 1`.

Simplify `hy` using `[ann]`. Take `⟨x0, hx0, hne⟩` from `hy'`. Rewrite using `[Set.indicator_of_notMem hy]`. Use `set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf`. Establish `hshift : ∀ x, f (x0 + x) = χ x0 y * f x`.

Introduce `x`. Establish `hmem : x0 + x ∈ (L : Set V) ↔ x ∈ (L : Set V)` using `L.add_mem_cancel_left hx0`. Distinguish the cases in `hx : x ∈ (L : Set V)`. Simplify using `only [hf, Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx, hχ]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hx' : x0 + x ∉ (L : Set V)` using `fun h => hx (hmem.1 h)`. Simplify using `[hf, hx, hx']`. Establish `hI : ∫ x, f x ∂μ = χ x0 y * ∫ x, f x ∂μ`. Rewrite using `[← integral_const_mul]`. Repeatedly rewrite using `[← hshift]`.

Conclude with `(integral_add_left_eq_self (fun x => f x) x0).symm`. Establish `h1 : (1 - χ x0 y) * ∫ x, f x ∂μ = 0`. Rewrite using `[sub_mul, one_mul, ← hI, sub_self]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h).symm hne`.

Conclude with `h`.
-/
theorem transform_indicator (hLo : IsOpen (L : Set V)) (y : V) :
    ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) y := by
  classical
  by_cases hy : y ∈ ann χ L
  · rw [Set.indicator_of_mem hy]
    have hfun : (fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y) =
        (L : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext x
      by_cases hx : x ∈ (L : Set V)
      · rw [Set.indicator_of_mem hx, hy x hx, one_mul]
      · simp [hx]
    rw [hfun, integral_indicator_const _ hLo.measurableSet]
    simp
  · have hy' : ∃ x0 ∈ (L : Set V), χ x0 y ≠ 1 := by
      simpa [ann] using hy
    obtain ⟨x0, hx0, hne⟩ := hy'
    rw [Set.indicator_of_notMem hy]
    set f : V → ℂ := fun x => (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y with hf
    have hshift : ∀ x, f (x0 + x) = χ x0 y * f x := by
      intro x
      have hmem : x0 + x ∈ (L : Set V) ↔ x ∈ (L : Set V) :=
        L.add_mem_cancel_left hx0
      by_cases hx : x ∈ (L : Set V)
      · simp only [hf, Set.indicator_of_mem (hmem.2 hx), Set.indicator_of_mem hx, hχ]
        ring
      · have hx' : x0 + x ∉ (L : Set V) := fun h => hx (hmem.1 h)
        simp [hf, hx, hx']
    have hI : ∫ x, f x ∂μ = χ x0 y * ∫ x, f x ∂μ := by
      rw [← integral_const_mul]
      simp_rw [← hshift]
      exact (integral_add_left_eq_self (fun x => f x) x0).symm
    have h1 : (1 - χ x0 y) * ∫ x, f x ∂μ = 0 := by
      rw [sub_mul, one_mul, ← hI, sub_self]
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h

include hχ in

/- English proof (translation)
Use `⟨(L : Set V).indicator (fun _ => (1 : ℂ)), IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const, HasCompactSupport.intro hLc (fun x hx => by simp [hx]), ?_, ⟨0, by simp⟩⟩` and prove the remaining obligations. Establish `hfun : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) = (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ))`. Use function extensionality and compare the values at `fun y => transform_indicator μ χ hχ L hLo y`. Rewrite using `[hfun]`. Conclude with `(integrable_indicator_iff hA.measurableSet).2 (continuousOn_const.integrableOn_compact (hK.of_isClosed_subset hA hAK))`.
-/
theorem testEx_of_lattice (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hA : IsClosed (ann χ L)) (K : Set V) (hK : IsCompact K) (hAK : ann χ L ⊆ K) :
    TestEx μ χ := by
  classical
  refine ⟨(L : Set V).indicator (fun _ => (1 : ℂ)),
    IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const,
    HasCompactSupport.intro hLc (fun x hx => by simp [hx]), ?_, ⟨0, by simp⟩⟩
  have hfun : (fun y => ∫ x, (L : Set V).indicator (fun _ => (1 : ℂ)) x * χ x y ∂μ) =
      (ann χ L).indicator (fun _ => ((μ.real (L : Set V) : ℝ) : ℂ)) :=
    funext fun y => transform_indicator μ χ hχ L hLo y
  rw [hfun]
  exact (integrable_indicator_iff hA.measurableSet).2
    (continuousOn_const.integrableOn_compact (hK.of_isClosed_subset hA hAK))

end Lattice

def AnnAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (χ : V → V → ℂ) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧ IsClosed (ann χ L) ∧
    ∃ K, IsCompact K ∧ ann χ L ⊆ K

section Triv

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (χ : V → V → ℂ)

/- English proof (translation)
Use `set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg`. Establish `gc : Continuous g` using `IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const`. Establish `gs : HasCompactSupport g` using `HasCompactSupport.intro hLc (fun x hx => by simp [hg, hx])`. Distinguish the cases in `hall : ∀ t, t ∈ L`. Use `⟨g, gc, gs, ?_, ⟨0, by simp [hg]⟩⟩` and prove the remaining obligations.

Establish `huniv : (L : Set V) = Set.univ` using `Set.eq_univ_of_forall hall`. Use `haveI : CompactSpace V := ⟨huniv ▸ hLc⟩`. Simplify using `only [hχ, mul_one]`. Conclude with `integrable_const _`. Use `push_neg at hall`.

Take `⟨t, ht⟩` from `hall`. Establish `gc' : Continuous (fun x => g (x - t))` using `gc.comp (continuous_sub_right t)`. Establish `gs' : HasCompactSupport (fun x => g (x - t))` using `gs.comp_homeomorph (Homeomorph.subRight t)`. Use `⟨fun x => g x - g (x - t), gc.sub gc', gs.sub gs', ?_, ⟨0, ?_⟩⟩` and prove the remaining obligations. Establish `h0 : ∀ y, ∫ x, (g x - g (x - t)) * χ x y ∂μ = 0`.

Introduce `y`. Simplify using `only [hχ, mul_one]`. Rewrite using `[integral_sub (gc.integrable_of_hasCompactSupport gs) (gc'.integrable_of_hasCompactSupport gs'), integral_sub_right_eq_self, sub_self]`. Simplify using `only [h0]`. Conclude with `integrable_zero _ _ _`.

Simplify using `[hg, ht]`.
-/
theorem testEx_of_trivial (hχ : ∀ x y, χ x y = 1) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V)) : TestEx μ χ := by
  classical
  set g : V → ℂ := (L : Set V).indicator (fun _ => (1 : ℂ)) with hg
  have gc : Continuous g :=
    IsClopen.continuous_indicator ⟨L.isClosed_of_isOpen hLo, hLo⟩ continuous_const
  have gs : HasCompactSupport g := HasCompactSupport.intro hLc (fun x hx => by simp [hg, hx])
  by_cases hall : ∀ t, t ∈ L
  · refine ⟨g, gc, gs, ?_, ⟨0, by simp [hg]⟩⟩
    have huniv : (L : Set V) = Set.univ := Set.eq_univ_of_forall hall
    haveI : CompactSpace V := ⟨huniv ▸ hLc⟩
    simp only [hχ, mul_one]
    exact integrable_const _
  · push_neg at hall
    obtain ⟨t, ht⟩ := hall
    have gc' : Continuous (fun x => g (x - t)) := gc.comp (continuous_sub_right t)
    have gs' : HasCompactSupport (fun x => g (x - t)) :=
      gs.comp_homeomorph (Homeomorph.subRight t)
    refine ⟨fun x => g x - g (x - t), gc.sub gc', gs.sub gs', ?_, ⟨0, ?_⟩⟩
    · have h0 : ∀ y, ∫ x, (g x - g (x - t)) * χ x y ∂μ = 0 := by
        intro y
        simp only [hχ, mul_one]
        rw [integral_sub (gc.integrable_of_hasCompactSupport gs)
          (gc'.integrable_of_hasCompactSupport gs'), integral_sub_right_eq_self, sub_self]
      simp only [h0]
      exact integrable_zero _ _ _
    · simp [hg, ht]

end Triv

section Nontriv

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

def DualAt {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v) : Prop :=
  ∃ L : AddSubgroup V, IsCompact (L : Set V) ∧ IsOpen (L : Set V) ∧
    (∀ s ∈ v.adicCompletionIntegers F, ∀ x ∈ L, ∃ x' ∈ L, ∀ y, B x' y = s * B x y) ∧
    ∀ c : Fv F v, ∃ K, IsCompact K ∧
      {y | ∀ x ∈ L, B x y ∈ (fun s => c * s) '' (v.adicCompletionIntegers F : Set (Fv F v))} ⊆ K

/- English proof (translation)
Distinguish the cases in `ht0 : t = 0`. Conclude with `⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩`. Establish `hr : r0 ≠ 0`. Introduce and unpack `rfl`. Conclude with `h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)`.

Distinguish the cases in `hle : Valued.v r0 ≤ Valued.v t`. It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises. Establish `hs : r0 / t ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]`.

Conclude with `(div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0))).2 hle`. Establish `h2` using `ht _ hs`. Rewrite `h2` using `[div_mul_cancel₀ _ ht0]`. Then use the resulting hypothesis. Use `push_neg at hle`. Use `⟨t / r0, ?_, by field_simp⟩` and prove the remaining obligations.

Rewrite using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]`. Conclude with `(div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr))).2 hle.le`.
-/
theorem mem_of_psi (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_cases ht0 : t = 0
  · exact ⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩
  have hr : r0 ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)
  by_cases hle : Valued.v r0 ≤ Valued.v t
  · exfalso
    apply h0
    have hs : r0 / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0))).2 hle
    have h2 := ht _ hs
    rwa [div_mul_cancel₀ _ ht0] at h2
  · push_neg at hle
    refine ⟨t / r0, ?_, by field_simp⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr))).2 hle.le

/- English proof (translation)
Take `⟨L, hLc, hLo, hst, hK⟩` from `hD`. Take `⟨K, hKc, hKsub⟩` from `hK r0`. Use `⟨L, hLc, hLo, ?_, K, hKc, ?_⟩` and prove the remaining obligations. Establish `hset : ann (fun x y => ψ0 (B x y)) (L : Set V) = ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1}`. Use extensionality with `y`.

Simplify using `[ann]`. Rewrite using `[hset]`. Conclude with `isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))`. Introduce `y hy`. Use `hKsub (fun x hx => ?_)` and prove the remaining obligations.

Apply `mem_of_psi v ψ0 r0 (B x y) h0` to reduce the goal to its premises. Introduce `s hs`. Take `⟨x', hx', hB'⟩` from `hst s hs x hx`. Rewrite using `[← hB' y]`. Conclude with `hy x' hx'`.
-/
theorem annAt_of_dual {V : Type} [AddCommGroup V] [TopologicalSpace V] (B : V → V → Fv F v)
    (ψ0 : Fv F v → ℂ) (hψ : Continuous ψ0) (hB : ∀ x, Continuous (B x)) (r0 : Fv F v)
    (h0 : ψ0 r0 ≠ 1) (hD : DualAt v B) : AnnAt (fun x y => ψ0 (B x y)) := by
  obtain ⟨L, hLc, hLo, hst, hK⟩ := hD
  obtain ⟨K, hKc, hKsub⟩ := hK r0
  refine ⟨L, hLc, hLo, ?_, K, hKc, ?_⟩
  · have hset : ann (fun x y => ψ0 (B x y)) (L : Set V) =
        ⋂ x ∈ (L : Set V), (fun y => ψ0 (B x y)) ⁻¹' {1} := by
      ext y
      simp [ann]
    rw [hset]
    exact isClosed_biInter fun x _ => isClosed_singleton.preimage (hψ.comp (hB x))
  · intro y hy
    refine hKsub (fun x hx => ?_)
    apply mem_of_psi v ψ0 r0 (B x y) h0
    intro s hs
    obtain ⟨x', hx', hB'⟩ := hst s hs x hx
    rw [← hB' y]
    exact hy x' hx'

end Nontriv

section Add

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

open Classical in
/- English proof (translation)
Unfold `singleV`. Apply `RestrictedProduct.ext` to reduce the goal to its premises. Introduce `w`. Use `show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w`. Rewrite using `[Pi.single_add]`.

Both sides reduce to the same expression.
-/
theorem singleV_add (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    singleV F v (r + s) = singleV F v r + singleV F v s := by
  unfold singleV
  apply RestrictedProduct.ext
  intro w
  show Pi.single v (r + s) w = Pi.single v r w + Pi.single v s w
  rw [Pi.single_add]
  rfl

/- English proof (translation)
Unfold `psiV`. Establish `h : pairA F 0 (singleV F v r + singleV F v s) = pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s)` using `Prod.ext (add_zero _).symm rfl`. Rewrite using `[singleV_add, h, AddChar.map_add_eq_mul]`.
-/
theorem psiV_add (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (r s : Fv F v) :
    psiV F ψ v (r + s) = psiV F ψ v r * psiV F ψ v s := by
  unfold psiV
  have h : pairA F 0 (singleV F v r + singleV F v s) =
      pairA F 0 (singleV F v r) + pairA F 0 (singleV F v s) := Prod.ext (add_zero _).symm rfl
  rw [singleV_add, h, AddChar.map_add_eq_mul]

/- English proof (translation)
Unfold `psiInf`. Establish `h : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0` using `Prod.ext rfl (add_zero _).symm`. Rewrite using `[h, AddChar.map_add_eq_mul]`.
-/
theorem psiInf_add (ψ : AddChar (AF F) ℂ) (r s : Ainf F) :
    psiInf F ψ (r + s) = psiInf F ψ r * psiInf F ψ s := by
  unfold psiInf
  have h : pairA F (r + s) 0 = pairA F r 0 + pairA F s 0 := Prod.ext rfl (add_zero _).symm
  rw [h, AddChar.map_add_eq_mul]

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
Unfold `psiV`. Conclude with `hψ.comp (show Continuous fun r => pairA F 0 (singleV F v r) from continuous_const.prodMk (continuous_singleV v))`.
-/
theorem continuous_psiV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (psiV F ψ v) := by
  unfold psiV
  exact hψ.comp (show Continuous fun r => pairA F 0 (singleV F v r) from
    continuous_const.prodMk (continuous_singleV v))

variable (R : Type) [CommRing R] [Algebra F R]

/- English proof (translation)
Simplify using `only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`.
-/
theorem BR_add (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X T Y : Fin n → Fin M → R ⊗[F] E) : BR R σ J (T + X) Y = BR R σ J T Y + BR R σ J X Y := by
  simp only [BR, hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `pairHerm`. Simplify using `[Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]`.
-/
theorem pairHerm_add (σ : E →ₐ[F] E) (n : ℕ) (S T U : HermR R σ n) :
    pairHerm R σ n (T + S) U = pairHerm R σ n T U + pairHerm R σ n S U := by
  unfold pairHerm
  simp [Matrix.add_apply, add_mul, Finset.sum_add_distrib, mul_add]

end Add

section ContY

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

/- English proof (translation)
Use `first`. Consider the case `exact IsModuleTopology.continuous_of_linearMap _`. Consider the case `exact LinearMap.continuous_of_finiteDimensional _`. Consider the case `(unfold Algebra.trace; done)`.
-/
theorem continuous_trace_tens : Continuous (Algebra.trace R (R ⊗[F] E)) := by
  first
  | exact IsModuleTopology.continuous_of_linearMap _
  | exact LinearMap.continuous_of_finiteDimensional _
  | (unfold Algebra.trace; done)

/- English proof (translation)
Unfold `BR hR`. Use `continuous_finset_sum _ fun a _ => (continuous_trace_tens R).comp ?_` and prove the remaining obligations. Unfold `Formalism.UG.hform`. Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply j).comp (continuous_apply a))`.
-/
theorem continuous_BR_right (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (X : Fin n → Fin M → R ⊗[F] E) : Continuous (BR R σ J X) := by
  unfold BR hR
  refine continuous_finset_sum _ fun a _ => (continuous_trace_tens R).comp ?_
  unfold Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact continuous_const.mul ((continuous_apply j).comp (continuous_apply a))

/- English proof (translation)
Unfold `pairHerm`. Use `continuous_const.mul ((continuous_trace_tens R).comp ?_)` and prove the remaining obligations. Use `continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_` and prove the remaining obligations. Conclude with `continuous_const.mul ((continuous_apply a).comp ((continuous_apply b).comp continuous_subtype_val))`.
-/
theorem continuous_pairHerm_right (σ : E →ₐ[F] E) (n : ℕ) (S : HermR R σ n) :
    Continuous (pairHerm R σ n S) := by
  unfold pairHerm
  refine continuous_const.mul ((continuous_trace_tens R).comp ?_)
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact continuous_const.mul
    ((continuous_apply a).comp ((continuous_apply b).comp continuous_subtype_val))

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
theorem sdUniq_of_dual (hI : SdTestInf) (hD : DualLatV) : SdUniq :=
  sdUniq_of hI (sdTestV_of_dual hD)

end PI.VolStabW
