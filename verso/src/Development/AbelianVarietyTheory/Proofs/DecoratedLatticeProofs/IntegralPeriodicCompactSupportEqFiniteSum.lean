import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.PeriodicIntegral

/- English proof (translation)
Establish `hmem : (ϖ : k) ∈ 𝒪[k]`. Rewrite using `[Valuation.mem_integer_iff]`. Conclude with `((h ϖ).2 le_rfl).le`. Use `⟨⟨ϖ, hmem⟩, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[IsDiscreteValuationRing.irreducible_iff_uniformizer]`.

Use extensionality with `y`. Rewrite using `[Ideal.mem_span_singleton, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one, h]`. Conclude with `Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := ⟨(ϖ : k), hmem⟩)`.
-/
theorem exists_irreducible_of_isUnif {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {ϖ : kˣ} (h : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    ∃ p : 𝒪[k], Irreducible p ∧ (p : k) = ϖ := by
  have hmem : (ϖ : k) ∈ 𝒪[k] := by
    rw [Valuation.mem_integer_iff]; exact ((h ϖ).2 le_rfl).le
  refine ⟨⟨ϖ, hmem⟩, ?_, rfl⟩
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  ext y
  rw [Ideal.mem_span_singleton, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one, h]
  exact Valuation.Integers.le_iff_dvd (Valuation.integer.integers (valuation k)) (x := y) (y := ⟨(ϖ : k), hmem⟩)

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ν hν ϖ hϖ A B T hT hU I _ _ F hF hper`. Use `haveI := hν.1`. Use `haveI := secondCountable k`. Use `haveI := t2Space k`. Take `⟨p, hp, hpϖ⟩` from `exists_irreducible_of_isUnif hϖ`.

Establish `hnabs : nabs k ϖ = (resCard k : ℝ)⁻¹` using `nabs_uniformiser hp hpϖ.symm`. Use `set u : kˣ := ϖ ^ B with hu`. Set `S : k → Set k` to `fun t => (fun x => -t + x) ⁻¹' cball u`. Set `box : (I → k) → Set (I → k)` to `fun t => Set.univ.pi fun i => S (t i)`. Set `P` to `Fintype.piFinset fun _ : I => T`.

Establish `hmemS : ∀ t x, x ∈ S t ↔ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)`. Introduce `t x`. Simplify using `[S, cball, u, sub_eq_neg_add]`. Establish `hmemBox : ∀ t x, x ∈ box t ↔ ∀ i, valuation k (x i - t i) ≤ valuation k ((ϖ : k) ^ B)`. Introduce `t x`.

Simplify using `only [box, Set.mem_univ_pi, hmemS]`. Establish `hshift : ∀ x t, x ∈ box t → F t = F x`. Introduce `x t hx`. Use `hper x (t - x) (fun i => by` as an intermediate fact. Rewrite using `[Pi.sub_apply, ← Valuation.map_neg, neg_sub]`.

Conclude with `(hmemBox t x).1 hx i)`. Simplify using `using this`. Establish `hdec : ∀ x, F x = ∑ t ∈ P, (box t).indicator (fun _ => F t) x`. Introduce `x`. Distinguish the cases in `h0 : F x = 0`.

Rewrite using `[h0]`. Use `symm`. Use `Finset.sum_eq_zero fun t _ => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ box t`. Rewrite using `[Set.indicator_of_mem hx, hshift x t hx, h0]`.

Rewrite using `[Set.indicator_of_notMem hx]`. Establish `hbig` using `hF x h0`. Establish `hex` using `fun i => hU (x i) (hbig i)`. Use `choose s hs hsu using hex`. Establish `hsP : s ∈ P` using `Fintype.mem_piFinset.2 fun i => (hs i).1`.

Establish `hxs : x ∈ box s` using `(hmemBox s x).2 fun i => (hs i).2`. Rewrite using `[Finset.sum_eq_single s, Set.indicator_of_mem hxs, hshift x s hxs]`. Introduce `t htP hts`. Rewrite using `[Set.indicator_of_notMem]`. Introduce `hxt`.

Apply `hts` to reduce the goal to its premises. Use function extensionality and compare the values at `i`. Conclude with `hsu i (t i) ⟨Fintype.mem_piFinset.1 htP i, (hmemBox t x).1 hxt i⟩`. Introduce `h`. Conclude with `absurd hsP h`.

Establish `hmeasS : ∀ t, MeasurableSet (S t)` using `fun t => measurable_const_add (-t) (isOpen_cball u).measurableSet`. Establish `hmeasBox : ∀ t, MeasurableSet (box t)` using `fun t => MeasurableSet.univ_pi fun i => hmeasS (t i)`. Establish `hνS : ∀ t, ν (S t) = (distribHaarChar k u : ℝ≥0∞)`. Introduce `t`. Simplify using `only [S]`.

Rewrite using `[measure_preimage_add, measure_cball, hν.2, mul_one]`. Establish `hμbox : ∀ t, (Measure.pi fun _ : I => ν) (box t) = (distribHaarChar k u : ℝ≥0∞) ^ Fintype.card I`. Introduce `t`. Simplify using `only [box]`. Rewrite using `[Measure.pi_pi]`.

Simplify using `[hνS]`. Establish `hnu : nabs k u = nabs k ϖ ^ B` using `by simp [u, nabs, map_pow]`. Establish `hreal : ∀ t, (Measure.pi fun _ : I => ν).real (box t) = ((resCard k : ℝ)⁻¹ ^ B) ^ Fintype.card I`. Introduce `t`. Rewrite using `[Measure.real, hμbox, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hnabs, ← hnu]`.

Both sides reduce to the same expression. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use function extensionality and compare the values at `x`. Conclude with `hdec x`.

Use `_ = ∑ t ∈ P, ∫ x, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by`. Use `integral_finset_sum P fun t _ => ?_` and prove the remaining obligations. Use `IntegrableOn.integrable_indicator ?_ (hmeasBox t)` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hμbox]; simp)`. Use `_ = ∑ t ∈ P, (Measure.pi fun _ : I => ν).real (box t) • F t := by`.

Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Conclude with `integral_indicator_const (F t) (hmeasBox t)`. Use `_ = _ := by`. Simplify using `only [hreal, Complex.real_smul, ← Finset.mul_sum]`. Use `push_cast`.

Rewrite using `[inv_pow]`.
-/
theorem integral_eq_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (ϖ : kˣ), GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ → ∀ (A B : ℕ) (T : Finset k), (∀ t ∈ T, valuation k t ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x : k, valuation k x ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k) → ∃! t, t ∈ T ∧ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B)) → ∀ (I : Type) [Fintype I] [DecidableEq I] (F : (I → k) → ℂ), (∀ x, F x ≠ 0 → ∀ i, valuation k (x i) ≤ valuation k (((ϖ ^ A)⁻¹ : kˣ) : k)) → (∀ x y, (∀ i, valuation k (y i) ≤ valuation k ((ϖ : k) ^ B)) → F (x + y) = F x) → ∫ x, F x ∂(Measure.pi fun _ : I => ν) = (((resCard k : ℂ) ^ B)⁻¹) ^ Fintype.card I * ∑ t ∈ Fintype.piFinset (fun _ : I => T), F t := by
  intro k _ _ _ _ _ _ ν hν ϖ hϖ A B T hT hU I _ _ F hF hper
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  obtain ⟨p, hp, hpϖ⟩ := exists_irreducible_of_isUnif hϖ
  have hnabs : nabs k ϖ = (resCard k : ℝ)⁻¹ := nabs_uniformiser hp hpϖ.symm
  set u : kˣ := ϖ ^ B with hu
  let S : k → Set k := fun t => (fun x => -t + x) ⁻¹' cball u
  let box : (I → k) → Set (I → k) := fun t => Set.univ.pi fun i => S (t i)
  let P := Fintype.piFinset fun _ : I => T
  have hmemS : ∀ t x, x ∈ S t ↔ valuation k (x - t) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp [S, cball, u, sub_eq_neg_add]
  have hmemBox : ∀ t x, x ∈ box t ↔ ∀ i, valuation k (x i - t i) ≤ valuation k ((ϖ : k) ^ B) := by
    intro t x; simp only [box, Set.mem_univ_pi, hmemS]
  have hshift : ∀ x t, x ∈ box t → F t = F x := by
    intro x t hx
    have := hper x (t - x) (fun i => by
      rw [Pi.sub_apply, ← Valuation.map_neg, neg_sub]; exact (hmemBox t x).1 hx i)
    simpa using this
  have hdec : ∀ x, F x = ∑ t ∈ P, (box t).indicator (fun _ => F t) x := by
    intro x
    by_cases h0 : F x = 0
    · rw [h0]; symm
      refine Finset.sum_eq_zero fun t _ => ?_
      by_cases hx : x ∈ box t
      · rw [Set.indicator_of_mem hx, hshift x t hx, h0]
      · rw [Set.indicator_of_notMem hx]
    · have hbig := hF x h0
      have hex := fun i => hU (x i) (hbig i)
      choose s hs hsu using hex
      have hsP : s ∈ P := Fintype.mem_piFinset.2 fun i => (hs i).1
      have hxs : x ∈ box s := (hmemBox s x).2 fun i => (hs i).2
      rw [Finset.sum_eq_single s, Set.indicator_of_mem hxs, hshift x s hxs]
      · intro t htP hts
        rw [Set.indicator_of_notMem]
        intro hxt
        apply hts
        funext i
        exact hsu i (t i) ⟨Fintype.mem_piFinset.1 htP i, (hmemBox t x).1 hxt i⟩
      · intro h; exact absurd hsP h
  have hmeasS : ∀ t, MeasurableSet (S t) := fun t =>
    measurable_const_add (-t) (isOpen_cball u).measurableSet
  have hmeasBox : ∀ t, MeasurableSet (box t) := fun t => MeasurableSet.univ_pi fun i => hmeasS (t i)
  have hνS : ∀ t, ν (S t) = (distribHaarChar k u : ℝ≥0∞) := by
    intro t; simp only [S]; rw [measure_preimage_add, measure_cball, hν.2, mul_one]
  have hμbox : ∀ t, (Measure.pi fun _ : I => ν) (box t) = (distribHaarChar k u : ℝ≥0∞) ^ Fintype.card I := by
    intro t; simp only [box]; rw [Measure.pi_pi]; simp [hνS]
  have hnu : nabs k u = nabs k ϖ ^ B := by simp [u, nabs, map_pow]
  have hreal : ∀ t, (Measure.pi fun _ : I => ν).real (box t) = ((resCard k : ℝ)⁻¹ ^ B) ^ Fintype.card I := by
    intro t
    rw [Measure.real, hμbox, ENNReal.toReal_pow, ENNReal.coe_toReal, ← hnabs, ← hnu]
    rfl
  calc ∫ x, F x ∂(Measure.pi fun _ : I => ν)
        = ∫ x, ∑ t ∈ P, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          congr 1; funext x; exact hdec x
    _ = ∑ t ∈ P, ∫ x, (box t).indicator (fun _ => F t) x ∂(Measure.pi fun _ : I => ν) := by
          refine integral_finset_sum P fun t _ => ?_
          refine IntegrableOn.integrable_indicator ?_ (hmeasBox t)
          exact integrableOn_const (by rw [hμbox]; simp)
    _ = ∑ t ∈ P, (Measure.pi fun _ : I => ν).real (box t) • F t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          exact integral_indicator_const (F t) (hmeasBox t)
    _ = _ := by
          simp only [hreal, Complex.real_smul, ← Finset.mul_sum]
          push_cast
          rw [inv_pow]

end GlobalTheory.PeriodicIntegral
