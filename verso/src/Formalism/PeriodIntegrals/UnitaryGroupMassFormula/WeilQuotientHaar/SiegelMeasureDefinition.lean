import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientHaar.HaarMeasureUniqueness

noncomputable section

open MeasureTheory Measure Topology Set
open scoped ENNReal Pointwise

namespace QPK

section SM

variable {G : Type} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Establish `h' : x * c = x * 1` using `by rw [mul_one, mul_comm]; exact h.symm`. Conclude with `(ENNReal.mul_right_inj h0 ht).mp h'`.
-/
lemma eq_one_of_eq_mul {c x : ℝ≥0∞} (h0 : x ≠ 0) (ht : x ≠ ⊤) (h : x = c * x) : c = 1 := by
  have h' : x * c = x * 1 := by rw [mul_one, mul_comm]; exact h.symm
  exact (ENNReal.mul_right_inj h0 ht).mp h'

/- English proof (translation)
Break down `lt_trichotomy c 1 with hlt | heq | hgt` into its components or cases. Establish `h1 : c * c ≤ c * 1` using `by gcongr`. Rewrite `h1` using `[mul_one]`. Conclude with `absurd h (ne_of_lt (lt_of_le_of_lt h1 hlt))`. Conclude with `heq`.

Establish `h1 : c * 1 ≤ c * c` using `by gcongr`. Rewrite `h1` using `[mul_one]`. Conclude with `absurd h (ne_of_gt (lt_of_lt_of_le hgt h1))`.
-/
lemma eq_one_of_mul_self {c : ℝ≥0∞} (h : c * c = 1) : c = 1 := by
  rcases lt_trichotomy c 1 with hlt | heq | hgt
  · have h1 : c * c ≤ c * 1 := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_lt (lt_of_le_of_lt h1 hlt))
  · exact heq
  · have h1 : c * 1 ≤ c * c := by gcongr
    rw [mul_one] at h1
    exact absurd h (ne_of_gt (lt_of_lt_of_le hgt h1))

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Apply `h0` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]`. Apply `measure_iUnion_null` to reduce the goal to its premises.

Introduce `n`. Assume the negation of the conclusion as `hn`. Conclude with `(measure_spanningSets_lt_top μ n).ne (hc _ hn)`.
-/
lemma exists_pos_fin (μ : Measure G) [SigmaFinite μ] (h0 : μ ≠ 0) :
    ∃ A : Set G, μ A ≠ 0 ∧ μ A ≠ ⊤ := by
  by_contra hc
  push_neg at hc
  apply h0
  rw [← Measure.measure_univ_eq_zero, ← iUnion_spanningSets μ]
  apply measure_iUnion_null
  intro n
  by_contra hn
  exact (measure_spanningSets_lt_top μ n).ne (hc _ hn)

/- English proof (translation)
Take `⟨hsf, hne, hKc, hL⟩` from `hμ`. Establish `hmeas : Measurable (fun x : G => x⁻¹)` using `measurable_inv`. Establish `hKm : MeasurableSet K` using `hc.measurableSet`. Establish `hpre : (fun x : G => x⁻¹) ⁻¹' K = K`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `hK.2.2 _ h`. Rewrite `h2` using `[inv_inv]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `hK.2.2 _ h`. Establish `hpreC : (fun x : G => x⁻¹) ⁻¹' Kᶜ = Kᶜ`. Rewrite using `[Set.preimage_compl, hpre]`. Establish `hν : InvOn (μ.map (fun x => x⁻¹)) K`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(MeasurableEquiv.inv G).sigmaFinite_map`. Conclude with `(Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne`. Rewrite using `[Measure.map_apply hmeas hKm.compl, hpreC, hKc]`. Introduce `t ht`.

Rewrite using `[Measure.map_map (measurable_const_mul t) hmeas]`. Establish `e : (fun x : G => t * x) ∘ (fun x => x⁻¹) = (fun x => x⁻¹) ∘ (fun x => x * t⁻¹)`. Use function extensionality and compare the values at `x`. Simplify using `[mul_inv_rev]`. Rewrite using `[e, ← Measure.map_map hmeas (measurable_mul_const t⁻¹), hR t⁻¹ (hK.2.2 t ht)]`.

Take `⟨c, hc0, hct, hceq⟩` from `haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩`. Establish `hinv2 : (μ.map (fun x : G => x⁻¹)).map (fun x => x⁻¹) = μ`. Rewrite using `[Measure.map_map hmeas hmeas]`. Establish `e : (fun x : G => x⁻¹) ∘ (fun x => x⁻¹) = id`. Use function extensionality and compare the values at `x`.

Simplify using the standard rewrite rules. Rewrite using `[e, Measure.map_id]`. Establish `hμc : μ = (c * c) • μ`. Establish `h2` using `hinv2`. Rewrite `h2` using `[hceq, Measure.map_smul, hceq, smul_smul]`.

Conclude with `h2.symm`. Use `haveI := hsf`. Take `⟨A, hA0, hAt⟩` from `exists_pos_fin μ hne`. Establish `h3 : μ A = (c * c) * μ A`. Establish `h4` using `congrArg (fun m : Measure G => m A) hμc`.

Simplify `h4` using `only [Measure.smul_apply, smul_eq_mul]`. Establish `hcc : c * c = 1` using `eq_one_of_eq_mul hA0 hAt h3`. Rewrite using `[hceq, eq_one_of_mul_self hcc, one_smul]`.
-/
lemma map_inv_eq_self (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hR : ∀ s ∈ K, μ.map (fun x => x * s) = μ) :
    μ.map (fun x => x⁻¹) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x⁻¹) := measurable_inv
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x⁻¹) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.2 _ h
      rwa [inv_inv] at h2
    · intro h
      exact hK.2.2 _ h
  have hpreC : (fun x : G => x⁻¹) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x⁻¹)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.inv G).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x⁻¹) = (fun x => x⁻¹) ∘ (fun x => x * t⁻¹) := by
        funext x
        simp [mul_inv_rev]
      rw [e, ← Measure.map_map hmeas (measurable_mul_const t⁻¹), hR t⁻¹ (hK.2.2 t ht)]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hinv2 : (μ.map (fun x : G => x⁻¹)).map (fun x => x⁻¹) = μ := by
    rw [Measure.map_map hmeas hmeas]
    have e : (fun x : G => x⁻¹) ∘ (fun x => x⁻¹) = id := by
      funext x
      simp
    rw [e, Measure.map_id]
  have hμc : μ = (c * c) • μ := by
    have h2 := hinv2
    rw [hceq, Measure.map_smul, hceq, smul_smul] at h2
    exact h2.symm
  haveI := hsf
  obtain ⟨A, hA0, hAt⟩ := exists_pos_fin μ hne
  have h3 : μ A = (c * c) * μ A := by
    have h4 := congrArg (fun m : Measure G => m A) hμc
    simpa only [Measure.smul_apply, smul_eq_mul] using h4
  have hcc : c * c = 1 := eq_one_of_eq_mul hA0 hAt h3
  rw [hceq, eq_one_of_mul_self hcc, one_smul]

/- English proof (translation)
Take `⟨hsf, hne, hKc, hL⟩` from `hμ`. Establish `hmeas : Measurable (fun x : G => x * s)` using `measurable_mul_const s`. Establish `hKm : MeasurableSet K` using `hc.measurableSet`. Establish `hpre : (fun x : G => x * s) ⁻¹' K = K`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `hK.2.1 _ h _ (hK.2.2 s hs)`. Rewrite `h2` using `[mul_assoc, mul_inv_cancel, mul_one]`. Then use the resulting hypothesis.

Introduce `h`. Conclude with `hK.2.1 _ h _ hs`. Establish `hpreC : (fun x : G => x * s) ⁻¹' Kᶜ = Kᶜ`. Rewrite using `[Set.preimage_compl, hpre]`. Establish `hν : InvOn (μ.map (fun x => x * s)) K`.

Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(MeasurableEquiv.mulRight s).sigmaFinite_map`. Conclude with `(Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne`. Rewrite using `[Measure.map_apply hmeas hKm.compl, hpreC, hKc]`. Introduce `t ht`.

Rewrite using `[Measure.map_map (measurable_const_mul t) hmeas]`. Establish `e : (fun x : G => t * x) ∘ (fun x => x * s) = (fun x => x * s) ∘ (fun x => t * x)`. Use function extensionality and compare the values at `x`. Simplify using `[mul_assoc]`. Rewrite using `[e, ← Measure.map_map hmeas (measurable_const_mul t), hL t ht]`.

Take `⟨c, hc0, hct, hceq⟩` from `haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩`. Establish `hμK : μ K ≠ 0`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Rewrite using `[← Measure.measure_univ_eq_zero, ← Set.union_compl_self K]`.

Conclude with `measure_union_null h0 hKc`. Establish `h1 : μ K = c * μ K`. Establish `h2` using `congrArg (fun m : Measure G => m K) hceq`. Simplify using `only [Measure.smul_apply, smul_eq_mul] at h2`. Rewrite `h2` using `[Measure.map_apply hmeas hKm, hpre]`. Then use the resulting hypothesis.

Establish `hc1 : c = 1` using `eq_one_of_eq_mul hμK hfin h1`. Rewrite using `[hceq, hc1, one_smul]`.
-/
lemma map_mul_right_eq_self (K : Set G) (hc : IsClosed K) (hK : IsGrp K) (μ : Measure G)
    (hμ : InvOn μ K) (hfin : μ K ≠ ⊤) (s : G) (hs : s ∈ K) :
    μ.map (fun x => x * s) = μ := by
  obtain ⟨hsf, hne, hKc, hL⟩ := hμ
  have hmeas : Measurable (fun x : G => x * s) := measurable_mul_const s
  have hKm : MeasurableSet K := hc.measurableSet
  have hpre : (fun x : G => x * s) ⁻¹' K = K := by
    ext x
    simp only [Set.mem_preimage]
    constructor
    · intro h
      have h2 := hK.2.1 _ h _ (hK.2.2 s hs)
      rwa [mul_assoc, mul_inv_cancel, mul_one] at h2
    · intro h
      exact hK.2.1 _ h _ hs
  have hpreC : (fun x : G => x * s) ⁻¹' Kᶜ = Kᶜ := by
    rw [Set.preimage_compl, hpre]
  have hν : InvOn (μ.map (fun x => x * s)) K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (MeasurableEquiv.mulRight s).sigmaFinite_map
    · exact (Measure.map_ne_zero_iff hmeas.aemeasurable).2 hne
    · rw [Measure.map_apply hmeas hKm.compl, hpreC, hKc]
    · intro t ht
      rw [Measure.map_map (measurable_const_mul t) hmeas]
      have e : (fun x : G => t * x) ∘ (fun x => x * s) = (fun x => x * s) ∘ (fun x => t * x) := by
        funext x
        simp [mul_assoc]
      rw [e, ← Measure.map_map hmeas (measurable_const_mul t), hL t ht]
  obtain ⟨c, hc0, hct, hceq⟩ := haar_measure_uniqueness G K hc hK _ _ hν ⟨hsf, hne, hKc, hL⟩
  have hμK : μ K ≠ 0 := by
    intro h0
    apply hne
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self K]
    exact measure_union_null h0 hKc
  have h1 : μ K = c * μ K := by
    have h2 := congrArg (fun m : Measure G => m K) hceq
    simp only [Measure.smul_apply, smul_eq_mul] at h2
    rwa [Measure.map_apply hmeas hKm, hpre] at h2
  have hc1 : c = 1 := eq_one_of_eq_mul hμK hfin h1
  rw [hceq, hc1, one_smul]

/- English proof (translation)
Establish `hm : Measurable (fun p : G × G => p.2 * p.1)` using `measurable_snd.mul measurable_fst`. Rewrite using `[Measure.map_map hf hm]`. Establish `e : f ∘ (fun p : G × G => p.2 * p.1) = (fun p : G × G => p.2 * p.1) ∘ g` using `funext h`. Rewrite using `[e, ← Measure.map_map hm hg.measurable, hg.map_eq]`.
-/
lemma map_mulSwap_eq (Q : Measure (G × G)) (g : G × G → G × G) (hg : MeasurePreserving g Q Q)
    (f : G → G) (hf : Measurable f) (h : ∀ p : G × G, f (p.2 * p.1) = (g p).2 * (g p).1) :
    (Q.map (fun p : G × G => p.2 * p.1)).map f = Q.map (fun p : G × G => p.2 * p.1) := by
  have hm : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  rw [Measure.map_map hf hm]
  have e : f ∘ (fun p : G × G => p.2 * p.1) = (fun p : G × G => p.2 * p.1) ∘ g := funext h
  rw [e, ← Measure.map_map hm hg.measurable, hg.map_eq]

end SM

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ N H hNc hHc hN hH hnorm hU μN μH hμN hfN hpN hμH hfH hpH hconj`. Establish `: SigmaFinite μN` using `hμN.1`. Establish `: SigmaFinite μH` using `hμH.1`. Establish `: IsFiniteMeasureOnCompacts μN` using `hfN`. Establish `: IsFiniteMeasureOnCompacts μH` using `hfH`.

Establish `hHcl : IsClosed H` using `hHc.isClosed`. Establish `hRH : ∀ s ∈ H, μH.map (fun x => x * s) = μH` using `fun s hs => map_mul_right_eq_self H hHcl hH μH hμH hHc.measure_lt_top.ne s hs`. Establish `hRN : ∀ s ∈ N, μN.map (fun x => x * s) = μN` using `hU μN hμN.1 hμN.2.1 hμN.2.2.1 hμN.2.2.2`. Establish `hIH` using `map_inv_eq_self H hHcl hH μH hμH hRH`. Establish `hIN` using `map_inv_eq_self N hNc hN μN hμN hRN`.

Establish `hm' : Measurable (fun p : G × G => p.2 * p.1)` using `measurable_snd.mul measurable_fst`. Establish `hM : mulMap μN μH = (μH.prod μN).map (fun p : G × G => p.2 * p.1)`. Establish `hm1 : Measurable (fun p : G × G => p.1 * p.2)` using `measurable_fst.mul measurable_snd`. Unfold `mulMap`. Rewrite using `[← Measure.prod_swap (μ := μH) (ν := μN), Measure.map_map hm1 measurable_swap]`.

Both sides reduce to the same expression. Establish `hHae : ∀ᵐ k ∂μH, k ∈ H`. Rewrite using `[ae_iff]`. Conclude with `hμH.2.2.1`. Establish `hNae : ∀ᵐ n ∂μN, n ∈ N`.

Rewrite using `[ae_iff]`. Conclude with `hμN.2.2.1`. Establish `hae : ∀ᵐ p ∂(μH.prod μN), p ∈ H ×ˢ N` using `((Measure.quasiMeasurePreserving_fst.ae hHae).and (Measure.quasiMeasurePreserving_snd.ae hNae)).mono fun p hp => Set.mem_prod.2 hp`. Establish `hnull : (μH.prod μN) (H ×ˢ N)ᶜ = 0`. Rewrite `hae` using `[ae_iff]`.

Conclude with `hae`. Establish `hSeq : prodSet N H = N * H`. Use extensionality with `x`. Simplify using `only [prodSet, Set.mem_mul, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨m, hm, h, hh, rfl⟩`. Conclude with `⟨m, hm, h, hh, rfl⟩`. Introduce and unpack `⟨m, hm, h, hh, rfl⟩`. Conclude with `⟨m, hm, h, hh, rfl⟩`. Establish `hScl : IsClosed (prodSet N H)`.

Rewrite using `[hSeq]`. Conclude with `hNc.mul_right_of_isCompact hHc`. Establish `hfin : IsFiniteMeasureOnCompacts (mulMap μN μH)`. Use `⟨fun L hL => ?_⟩` and prove the remaining obligations. Rewrite using `[hM, Measure.map_apply hm' hL.isClosed.measurableSet]`.

Establish `hC : IsCompact (L * H⁻¹)` using `hL.mul hHc.inv`. Establish `hsub : (fun p : G × G => p.2 * p.1) ⁻¹' L ⊆ (H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ`. Introduce `p hp`. Distinguish the cases in `hp2 : p ∈ H ×ˢ N`. Use `left`.

Use `⟨hp2.1, ?_⟩` and prove the remaining obligations. Conclude with `Set.mem_mul.2 ⟨p.2 * p.1, hp, p.1⁻¹, Set.inv_mem_inv.2 hp2.1, by group⟩`. Use `right`. Conclude with `hp2`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpos : PosOn (mulMap μN μH) (prodSet N H)`. Introduce and unpack `U hUo ⟨x, hxU, a, ha, b, hb, hx⟩`. Rewrite using `[hM, Measure.map_apply hm' hUo.measurableSet]`. Establish `hopen : IsOpen ((fun p : G × G => p.2 * p.1) ⁻¹' U)` using `hUo.preimage (continuous_snd.mul continuous_fst)`. Establish `hmem : (b, a) ∈ (fun p : G × G => p.2 * p.1) ⁻¹' U` using `by show a * b ∈ U`.

Rewrite using `[← hx]`. Conclude with `hxU`. Take `⟨V₁, V₂, hV₁, hV₂, hb1, ha2, hsub⟩` from `isOpen_prod_iff.1 hopen b a hmem`. Introduce `h0`. Establish `h1 : (μH.prod μN) (V₁ ×ˢ V₂) = 0` using `measure_mono_null hsub h0`.

Rewrite `h1` using `[Measure.prod_prod]`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases. Conclude with `hpH V₁ hV₁ ⟨b, hb1, hb⟩ h`. Conclude with `hpN V₂ hV₂ ⟨a, ha2, ha⟩ h`. Establish `hne : mulMap μN μH ≠ 0`.

Establish `h1` using `hpos univ isOpen_univ ⟨1, trivial, 1, hN.1, 1, hH.1, (mul_one 1).symm⟩`. Introduce `h`. Rewrite `h1` using `[h]`. Conclude with `h1 rfl`. Establish `hconc : mulMap μN μH (prodSet N H)ᶜ = 0`.

Rewrite using `[hM, Measure.map_apply hm' hScl.measurableSet.compl]`. Use `measure_mono_null ?_ hnull` and prove the remaining obligations. Introduce `p hp`. Simplify using `only [mem_preimage, mem_compl_iff] at hp`. Rewrite using `[mem_compl_iff]`.

Introduce and unpack `⟨h1, h2⟩`. Conclude with `hp ⟨p.2, h2, p.1, h1, rfl⟩`. Establish `hleft : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => s * x) = mulMap μN μH`. Introduce and unpack `s ⟨a, ha, b, hb, rfl⟩`. Establish `hg : MeasurePreserving (fun p : G × G => (b * p.1, a * (b * p.2 * b⁻¹))) (μH.prod μN) (μH.prod μN)`.

Use `MeasurePreserving.skew_product (f := fun x => b * x) (g := fun _ n => a * (b * n * b⁻¹)) ⟨measurable_const_mul b, hμH.2.2.2 b hb⟩ (((measurable_snd.const_mul b).mul_const b⁻¹).const_mul a) (ae_of_all _ fun _ => ?_)` and prove the remaining obligations. Establish `hcj : Measurable (fun x : G => b * x * b⁻¹)` using `(measurable_const_mul b).mul_const b⁻¹`. Establish `e : μN.map (fun n => a * (b * n * b⁻¹)) = (μN.map (fun x => b * x * b⁻¹)).map (fun x => a * x)`. Rewrite using `[Measure.map_map (measurable_const_mul a) hcj]`. Both sides reduce to the same expression.

Use `show μN.map (fun n => a * (b * n * b⁻¹)) = μN`. Rewrite using `[e, hconj b hb, hμN.2.2.2 a ha]`. Rewrite using `[hM]`. Conclude with `map_mulSwap_eq _ _ hg _ (measurable_const_mul _) (fun p => by simp only; group)`. Establish `hright : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => x * s) = mulMap μN μH`.

Introduce and unpack `s ⟨a, ha, b, hb, rfl⟩`. Establish `hg : MeasurePreserving (fun p : G × G => (p.1 * b, p.2 * (p.1 * a * p.1⁻¹))) (μH.prod μN) (μH.prod μN)`. Use `MeasurePreserving.skew_product (f := fun x => x * b) (g := fun k n => n * (k * a * k⁻¹)) ⟨measurable_mul_const b, hRH b hb⟩ (measurable_snd.mul ((measurable_fst.mul_const a).mul measurable_fst.inv)) (hHae.mono fun k hk => ?_)` and prove the remaining obligations. Conclude with `hRN _ (hnorm k hk a ha)`. Rewrite using `[hM]`.

Conclude with `map_mulSwap_eq _ _ hg _ (measurable_mul_const _) (fun p => by simp only; group)`. Establish `hinv : (mulMap μN μH).map (fun x => x⁻¹) = mulMap μN μH`. Establish `hg : MeasurePreserving (fun p : G × G => (p.1⁻¹, p.1⁻¹ * p.2⁻¹ * p.1)) (μH.prod μN) (μH.prod μN)`. Use `MeasurePreserving.skew_product (f := fun x => x⁻¹) (g := fun k n => k⁻¹ * n⁻¹ * k) ⟨measurable_inv, hIH⟩ ((measurable_fst.inv.mul measurable_snd.inv).mul measurable_fst) (hHae.mono fun k hk => ?_)` and prove the remaining obligations. Establish `hcj : Measurable (fun x : G => k⁻¹ * x * k⁻¹⁻¹)` using `(measurable_const_mul _).mul_const _`.

Establish `e : μN.map (fun n => k⁻¹ * n⁻¹ * k) = (μN.map (fun x => x⁻¹)).map (fun x => k⁻¹ * x * k⁻¹⁻¹)`. Rewrite using `[Measure.map_map hcj measurable_inv]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using the standard rewrite rules.

Use `show μN.map (fun n => k⁻¹ * n⁻¹ * k) = μN`. Rewrite using `[e, hIN, hconj _ (hH.2.2 k hk)]`. Rewrite using `[hM]`. Conclude with `map_mulSwap_eq _ _ hg _ measurable_inv (fun p => by simp only; group)`. Use `hfin` as an intermediate fact.

Conclude with `⟨⟨inferInstance, hne, hconc, hleft⟩, hfin, hpos, hright, hinv⟩`.
-/
theorem siegel_measure_definition : SMeas := by
  intro G _ _ _ _ _ _ _ _ N H hNc hHc hN hH hnorm hU μN μH hμN hfN hpN hμH hfH hpH hconj
  have : SigmaFinite μN := hμN.1
  have : SigmaFinite μH := hμH.1
  have : IsFiniteMeasureOnCompacts μN := hfN
  have : IsFiniteMeasureOnCompacts μH := hfH
  have hHcl : IsClosed H := hHc.isClosed
  have hRH : ∀ s ∈ H, μH.map (fun x => x * s) = μH := fun s hs =>
    map_mul_right_eq_self H hHcl hH μH hμH hHc.measure_lt_top.ne s hs
  have hRN : ∀ s ∈ N, μN.map (fun x => x * s) = μN :=
    hU μN hμN.1 hμN.2.1 hμN.2.2.1 hμN.2.2.2
  have hIH := map_inv_eq_self H hHcl hH μH hμH hRH
  have hIN := map_inv_eq_self N hNc hN μN hμN hRN
  have hm' : Measurable (fun p : G × G => p.2 * p.1) := measurable_snd.mul measurable_fst
  have hM : mulMap μN μH = (μH.prod μN).map (fun p : G × G => p.2 * p.1) := by
    have hm1 : Measurable (fun p : G × G => p.1 * p.2) := measurable_fst.mul measurable_snd
    unfold mulMap
    rw [← Measure.prod_swap (μ := μH) (ν := μN), Measure.map_map hm1 measurable_swap]
    rfl
  have hHae : ∀ᵐ k ∂μH, k ∈ H := by
    rw [ae_iff]
    exact hμH.2.2.1
  have hNae : ∀ᵐ n ∂μN, n ∈ N := by
    rw [ae_iff]
    exact hμN.2.2.1
  have hae : ∀ᵐ p ∂(μH.prod μN), p ∈ H ×ˢ N :=
    ((Measure.quasiMeasurePreserving_fst.ae hHae).and
      (Measure.quasiMeasurePreserving_snd.ae hNae)).mono fun p hp => Set.mem_prod.2 hp
  have hnull : (μH.prod μN) (H ×ˢ N)ᶜ = 0 := by
    rw [ae_iff] at hae
    exact hae
  have hSeq : prodSet N H = N * H := by
    ext x
    simp only [prodSet, Set.mem_mul, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
    · rintro ⟨m, hm, h, hh, rfl⟩
      exact ⟨m, hm, h, hh, rfl⟩
  have hScl : IsClosed (prodSet N H) := by
    rw [hSeq]
    exact hNc.mul_right_of_isCompact hHc

  have hfin : IsFiniteMeasureOnCompacts (mulMap μN μH) := by
    refine ⟨fun L hL => ?_⟩
    rw [hM, Measure.map_apply hm' hL.isClosed.measurableSet]
    have hC : IsCompact (L * H⁻¹) := hL.mul hHc.inv
    have hsub : (fun p : G × G => p.2 * p.1) ⁻¹' L ⊆ (H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ := by
      intro p hp
      by_cases hp2 : p ∈ H ×ˢ N
      · left
        refine ⟨hp2.1, ?_⟩
        exact Set.mem_mul.2 ⟨p.2 * p.1, hp, p.1⁻¹, Set.inv_mem_inv.2 hp2.1, by group⟩
      · right
        exact hp2
    calc (μH.prod μN) ((fun p : G × G => p.2 * p.1) ⁻¹' L)
        ≤ (μH.prod μN) ((H ×ˢ (L * H⁻¹)) ∪ (H ×ˢ N)ᶜ) := measure_mono hsub
      _ ≤ (μH.prod μN) (H ×ˢ (L * H⁻¹)) + (μH.prod μN) (H ×ˢ N)ᶜ := measure_union_le _ _
      _ = μH H * μN (L * H⁻¹) := by rw [hnull, add_zero, Measure.prod_prod]
      _ < ⊤ := ENNReal.mul_lt_top hHc.measure_lt_top hC.measure_lt_top

  have hpos : PosOn (mulMap μN μH) (prodSet N H) := by
    rintro U hUo ⟨x, hxU, a, ha, b, hb, hx⟩
    rw [hM, Measure.map_apply hm' hUo.measurableSet]
    have hopen : IsOpen ((fun p : G × G => p.2 * p.1) ⁻¹' U) :=
      hUo.preimage (continuous_snd.mul continuous_fst)
    have hmem : (b, a) ∈ (fun p : G × G => p.2 * p.1) ⁻¹' U := by
      show a * b ∈ U
      rw [← hx]
      exact hxU
    obtain ⟨V₁, V₂, hV₁, hV₂, hb1, ha2, hsub⟩ := isOpen_prod_iff.1 hopen b a hmem
    intro h0
    have h1 : (μH.prod μN) (V₁ ×ˢ V₂) = 0 := measure_mono_null hsub h0
    rw [Measure.prod_prod] at h1
    rcases mul_eq_zero.1 h1 with h | h
    · exact hpH V₁ hV₁ ⟨b, hb1, hb⟩ h
    · exact hpN V₂ hV₂ ⟨a, ha2, ha⟩ h
  have hne : mulMap μN μH ≠ 0 := by
    have h1 := hpos univ isOpen_univ ⟨1, trivial, 1, hN.1, 1, hH.1, (mul_one 1).symm⟩
    intro h
    rw [h] at h1
    exact h1 rfl
  have hconc : mulMap μN μH (prodSet N H)ᶜ = 0 := by
    rw [hM, Measure.map_apply hm' hScl.measurableSet.compl]
    refine measure_mono_null ?_ hnull
    intro p hp
    simp only [mem_preimage, mem_compl_iff] at hp
    rw [mem_compl_iff]
    rintro ⟨h1, h2⟩
    exact hp ⟨p.2, h2, p.1, h1, rfl⟩

  have hleft : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => s * x) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (b * p.1, a * (b * p.2 * b⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => b * x)
        (g := fun _ n => a * (b * n * b⁻¹)) ⟨measurable_const_mul b, hμH.2.2.2 b hb⟩
        (((measurable_snd.const_mul b).mul_const b⁻¹).const_mul a) (ae_of_all _ fun _ => ?_)
      have hcj : Measurable (fun x : G => b * x * b⁻¹) := (measurable_const_mul b).mul_const b⁻¹
      have e : μN.map (fun n => a * (b * n * b⁻¹)) =
          (μN.map (fun x => b * x * b⁻¹)).map (fun x => a * x) := by
        rw [Measure.map_map (measurable_const_mul a) hcj]
        rfl
      show μN.map (fun n => a * (b * n * b⁻¹)) = μN
      rw [e, hconj b hb, hμN.2.2.2 a ha]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_const_mul _) (fun p => by simp only; group)

  have hright : ∀ s ∈ prodSet N H, (mulMap μN μH).map (fun x => x * s) = mulMap μN μH := by
    rintro s ⟨a, ha, b, hb, rfl⟩
    have hg : MeasurePreserving (fun p : G × G => (p.1 * b, p.2 * (p.1 * a * p.1⁻¹)))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x * b)
        (g := fun k n => n * (k * a * k⁻¹)) ⟨measurable_mul_const b, hRH b hb⟩
        (measurable_snd.mul ((measurable_fst.mul_const a).mul measurable_fst.inv))
        (hHae.mono fun k hk => ?_)
      exact hRN _ (hnorm k hk a ha)
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ (measurable_mul_const _) (fun p => by simp only; group)

  have hinv : (mulMap μN μH).map (fun x => x⁻¹) = mulMap μN μH := by
    have hg : MeasurePreserving (fun p : G × G => (p.1⁻¹, p.1⁻¹ * p.2⁻¹ * p.1))
        (μH.prod μN) (μH.prod μN) := by
      refine MeasurePreserving.skew_product (f := fun x => x⁻¹)
        (g := fun k n => k⁻¹ * n⁻¹ * k) ⟨measurable_inv, hIH⟩
        ((measurable_fst.inv.mul measurable_snd.inv).mul measurable_fst)
        (hHae.mono fun k hk => ?_)
      have hcj : Measurable (fun x : G => k⁻¹ * x * k⁻¹⁻¹) :=
        (measurable_const_mul _).mul_const _
      have e : μN.map (fun n => k⁻¹ * n⁻¹ * k) =
          (μN.map (fun x => x⁻¹)).map (fun x => k⁻¹ * x * k⁻¹⁻¹) := by
        rw [Measure.map_map hcj measurable_inv]
        congr 1
        funext x
        simp
      show μN.map (fun n => k⁻¹ * n⁻¹ * k) = μN
      rw [e, hIN, hconj _ (hH.2.2 k hk)]
    rw [hM]
    exact map_mulSwap_eq _ _ hg _ measurable_inv (fun p => by simp only; group)
  have := hfin
  exact ⟨⟨inferInstance, hne, hconc, hleft⟩, hfin, hpos, hright, hinv⟩

end QPK
