import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH HeckeM heckeAct)
open scoped Classical

namespace PositivityTheory.Rg.BcB.CG

/- English proof (translation)
Simplify using `[finH, map_mul]`.
-/
theorem finH_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ} (g h : Hf E a b) :
    finH (g * h) = finH g * finH h := by
  simp [finH, map_mul]

/- English proof (translation)
Introduce `E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU`. Use `set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK`. Establish `hKc : IsCompact K` using `isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2`. Set `C : Hf E a b ⧸ U → Set (Hf E a b)` to `fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))`. Establish `hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q`.

Introduce `q h`. Use `show q.out⁻¹ * h ∈ U ↔ _`. Rewrite using `[← QuotientGroup.eq]`. Simplify using `only [Quotient.out_eq]`. Conclude with `eq_comm`.

Establish `hCo : ∀ q, IsOpen (C q)` using `fun q => hUo.preimage (continuous_const.mul continuous_id)`. Establish `hCm : ∀ q, MeasurableSet (C q)` using `fun q => (hCo q).measurableSet`. Establish `hCf : ∀ q, ν (C q) ≠ ⊤`. Introduce `q`. Use `show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤`.

Rewrite using `[measure_preimage_mul]`. Conclude with `hUc.measure_lt_top.ne`. Take `⟨t, ht⟩` from `hKc.elim_finite_subcover C hCo (by`. Introduce `h _`. Conclude with `Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)`.

Establish `hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t)`. Introduce `h x y hne`. Establish `hhK : h ∈ K` using `Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩`. Take `⟨q, hq⟩` from `Set.mem_iUnion.1 (ht hhK)`. Take `⟨hqt, hq⟩` from `Set.mem_iUnion.1 hq`.

Rewrite using `[(hCmem q h).1 hq]` and apply the resulting hypothesis. Use `⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j hij`. Simplify using `[hij]`. Introduce `p q x y`.

Simplify using the standard rewrite rules. Introduce `f hf`. Use function extensionality and compare the values at `i X`. Simplify using `only [convF, heckeAct]`. Rewrite using `[Fintype.sum_prod_type]`.

Simplify using `only`. Rewrite using `[Finset.sum_eq_single i.1 (fun p _ hp => by`. Use `Finset.sum_eq_zero fun z _ => ?_` and prove the remaining obligations. Rewrite using `[if_neg (Ne.symm hp)]`. Use the proof step `simp) (by simp)]`.

Use `Finset.sum_congr rfl fun z _ => ?_` and prove the remaining obligations. Simplify using `only [if_true]`. Rewrite using `[← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]`. Use `set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ`. Establish `hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h`.

Introduce `h u hu`. Simplify using `only [hΦ]`. Rewrite using `[finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]`. Establish `hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h`. Introduce `h`.

Establish `h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U` using `(hCmem _ h).2 rfl`. Combine the equalities or inequalities in the displayed calculation. Establish `hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h`. Use function extensionality and compare the values at `h`. Rewrite using `[Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]`.

Rewrite using `[Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]`. Introduce `q _ hq`. Rewrite using `[Set.indicator_of_notMem]`. Introduce `hc`. Conclude with `hq ((hCmem q h).1 hc).symm`.

Introduce `hmem`. Rewrite using `[Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]`. Assume the negation of the conclusion as `hne`. Apply `hmem` to reduce the goal to its premises. Use `hin h i.2 z ?_` and prove the remaining obligations.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Simplify using `only [hΦ, h0, zero_mul]`. Rewrite using `[hpt, integral_finsetSum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Rewrite using `[integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]`. Simplify using `only [hΦ, Complex.real_smul, Measure.real]`. Expand and normalize the polynomial expressions, which then agree. Introduce `q _`. Conclude with `(integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))`.
-/
theorem finHecke : FinHecke := by
  intro E _ _ _ a b _ _ ν _ A κ _ _ ψ U hψ hUo hUc hψU

  set K : Set (Hf E a b) := ⋃ x, ⋃ y, tsupport (ψ x y) with hK
  have hKc : IsCompact K := isCompact_iUnion fun x => isCompact_iUnion fun y => (hψ x y).2

  let C : Hf E a b ⧸ U → Set (Hf E a b) := fun q => (fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))
  have hCmem : ∀ q h, h ∈ C q ↔ (QuotientGroup.mk h : Hf E a b ⧸ U) = q := by
    intro q h
    show q.out⁻¹ * h ∈ U ↔ _
    rw [← QuotientGroup.eq]
    simp only [Quotient.out_eq]
    exact eq_comm
  have hCo : ∀ q, IsOpen (C q) := fun q => hUo.preimage (continuous_const.mul continuous_id)
  have hCm : ∀ q, MeasurableSet (C q) := fun q => (hCo q).measurableSet
  have hCf : ∀ q, ν (C q) ≠ ⊤ := by
    intro q
    show ν ((fun h => q.out⁻¹ * h) ⁻¹' (U : Set (Hf E a b))) ≠ ⊤
    rw [measure_preimage_mul]
    exact hUc.measure_lt_top.ne
  obtain ⟨t, ht⟩ := hKc.elim_finite_subcover C hCo (by
    intro h _
    exact Set.mem_iUnion.2 ⟨QuotientGroup.mk h, (hCmem _ h).2 rfl⟩)
  have hin : ∀ h, (∀ x y, ψ x y h ≠ 0 → (QuotientGroup.mk h : Hf E a b ⧸ U) ∈ t) := by
    intro h x y hne
    have hhK : h ∈ K := Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨y, subset_tsupport _ hne⟩⟩
    obtain ⟨q, hq⟩ := Set.mem_iUnion.1 (ht hhK)
    obtain ⟨hqt, hq⟩ := Set.mem_iUnion.1 hq
    rwa [(hCmem q h).1 hq]
  refine ⟨fun i j => if i.1 = j.1 then ∑ q ∈ t, Finsupp.single q.out ((ν (C q)).toReal * ψ i.2 j.2 q.out) else 0,
    ?_, ?_, ?_⟩
  · intro i j hij
    simp [hij]
  · intro p q x y
    simp
  · intro f hf
    funext i X
    simp only [convF, heckeAct]
    rw [Fintype.sum_prod_type]
    simp only
    rw [Finset.sum_eq_single i.1 (fun p _ hp => by
      refine Finset.sum_eq_zero fun z _ => ?_
      rw [if_neg (Ne.symm hp)]
      simp) (by simp)]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp only [if_true]
    rw [← Finsupp.sum_finsetSum_index (fun _ => by simp) (fun _ _ _ => by ring)]
    set Φ : Hf E a b → ℂ := fun h => ψ i.2 z h * f (i.1, z) (X * finH h) with hΦ
    have hΦU : ∀ h, ∀ u ∈ U, Φ (h * u) = Φ h := by
      intro h u hu
      simp only [hΦ]
      rw [finH_mul, ← mul_assoc, hf _ u hu, hψU _ _ u hu h]
    have hΦout : ∀ h, Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out = Φ h := by
      intro h
      have h1 : ((QuotientGroup.mk h : Hf E a b ⧸ U).out)⁻¹ * h ∈ U := (hCmem _ h).2 rfl
      calc Φ (QuotientGroup.mk h : Hf E a b ⧸ U).out
          = Φ ((QuotientGroup.mk h : Hf E a b ⧸ U).out * ((QuotientGroup.mk h : Hf E a b ⧸ U).out⁻¹ * h)) :=
            (hΦU _ _ h1).symm
        _ = Φ h := by rw [mul_inv_cancel_left]
    have hpt : Φ = fun h => ∑ q ∈ t, (C q).indicator (fun _ => Φ q.out) h := by
      funext h
      rw [Finset.sum_eq_single (QuotientGroup.mk h : Hf E a b ⧸ U)]
      · rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
      · intro q _ hq
        rw [Set.indicator_of_notMem]
        intro hc
        exact hq ((hCmem q h).1 hc).symm
      · intro hmem
        rw [Set.indicator_of_mem ((hCmem _ h).2 rfl), hΦout]
        by_contra hne
        apply hmem
        refine hin h i.2 z ?_
        intro h0
        apply hne
        simp only [hΦ, h0, zero_mul]
    rw [hpt, integral_finsetSum]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [integral_indicator_const _ (hCm q), Finsupp.sum_single_index (by simp)]
      simp only [hΦ, Complex.real_smul, Measure.real]
      ring
    · intro q _
      exact (integrable_indicator_iff (hCm q)).2 (integrableOn_const (hCf q))

end PositivityTheory.Rg.BcB.CG

end
