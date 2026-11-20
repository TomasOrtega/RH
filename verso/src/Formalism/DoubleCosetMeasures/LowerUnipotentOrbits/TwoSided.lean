import Formalism.DoubleCosetMeasures.Statement

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory

namespace Formalism.DoubleCosetMeasures.P

/- English proof (translation)
Use `conv_lhs => rw [← Quotient.out_eq q]`. Rewrite using `[Quotient.eq, QuotientGroup.rightRel_apply, ← K.inv_mem_iff, mul_inv_rev, inv_inv]`.
-/
theorem mem_preimage_rightRel_mk {G : Type} [Group G] (K : Subgroup G)
    (q : Quotient (QuotientGroup.rightRel K)) (x : G) :
    Quotient.mk (QuotientGroup.rightRel K) x = q ↔ x * q.out⁻¹ ∈ K := by
  conv_lhs => rw [← Quotient.out_eq q]
  rw [Quotient.eq, QuotientGroup.rightRel_apply, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

/- English proof (translation)
Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Rewrite using `[QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev, inv_inv]`.
-/
theorem mem_preimage_leftQuot_mk {G : Type} [Group G] (K : Subgroup G) (q : G ⧸ K) (y : G) :
    (y : G ⧸ K) = q ↔ q.out⁻¹ * y ∈ K := by
  conv_lhs => rw [← QuotientGroup.out_eq' q]
  rw [QuotientGroup.eq, ← K.inv_mem_iff, mul_inv_rev, inv_inv]

def box {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) : Set (G₁ × G₂) :=
  ((fun x => x * p.1.out⁻¹) ⁻¹' (K₁ : Set G₁)) ×ˢ ((fun y => p.2.out⁻¹ * y) ⁻¹' (K₂ : Set G₂))

def clsTS {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (z : G₁ × G₂) : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) :=
  (Quotient.mk _ z.1, (z.2 : G₂ ⧸ K₂))

/- English proof (translation)
Simplify using `only [box, clsTS, Prod.ext_iff, Set.mem_prod, Set.mem_preimage, SetLike.mem_coe, mem_preimage_rightRel_mk, mem_preimage_leftQuot_mk]`.
-/
theorem mem_box_iff {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) (z : G₁ × G₂) :
    z ∈ box K₁ K₂ p ↔ clsTS K₁ K₂ z = p := by
  simp only [box, clsTS, Prod.ext_iff, Set.mem_prod, Set.mem_preimage, SetLike.mem_coe,
    mem_preimage_rightRel_mk, mem_preimage_leftQuot_mk]

/- English proof (translation)
Simplify using `only [clsTS, Quotient.out_eq, QuotientGroup.out_eq']`.
-/
theorem cls_out {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    (p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂)) :
    clsTS K₁ K₂ (p.1.out, p.2.out) = p := by
  simp only [clsTS, Quotient.out_eq, QuotientGroup.out_eq']

/- English proof (translation)
Establish `h1` using `(mem_preimage_rightRel_mk K₁ (Quotient.mk (QuotientGroup.rightRel K₁) z.1) z.1).1 rfl`. Establish `h2` using `(mem_preimage_leftQuot_mk K₂ (z.2 : G₂ ⧸ K₂) z.2).1 rfl`. Establish `h` using `hf _ h1 _ h2 (Quotient.mk (QuotientGroup.rightRel K₁) z.1).out (z.2 : G₂ ⧸ K₂).out`. Simplify using `only [inv_mul_cancel_right, mul_inv_cancel_left] at h`. Simplify `h` using `[clsTS]`.
-/
theorem inv_eq_cls {G₁ G₂ : Type} [Group G₁] [Group G₂] (K₁ : Subgroup G₁) (K₂ : Subgroup G₂)
    {E : Type} (f : G₁ × G₂ → E)
    (hf : ∀ a ∈ K₁, ∀ b ∈ K₂, ∀ x : G₁, ∀ y : G₂, f (a * x, y * b) = f (x, y)) (z : G₁ × G₂) :
    f z = f ((clsTS K₁ K₂ z).1.out, (clsTS K₁ K₂ z).2.out) := by
  have h1 := (mem_preimage_rightRel_mk K₁ (Quotient.mk (QuotientGroup.rightRel K₁) z.1) z.1).1 rfl
  have h2 := (mem_preimage_leftQuot_mk K₂ (z.2 : G₂ ⧸ K₂) z.2).1 rfl
  have h := hf _ h1 _ h2 (Quotient.mk (QuotientGroup.rightRel K₁) z.1).out (z.2 : G₂ ⧸ K₂).out
  simp only [inv_mul_cancel_right, mul_inv_cancel_left] at h
  simpa [clsTS] using h

/- English proof (translation)
Introduce `G₁ G₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ K₁ K₂ hK₁ hK₂ E _ _ _ f hf hcs`. Use `set g : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) → E := fun p => f (p.1.out, p.2.out) with hg`. Establish `hopen : ∀ p, IsOpen (box K₁ K₂ p)` using `fun p => (hK₁.preimage (continuous_mul_right _)).prod (hK₂.preimage (continuous_mul_left _))`. Establish `hmeas : ∀ p, MeasurableSet (box K₁ K₂ p)` using `fun p => (hK₁.preimage (continuous_mul_right _)).measurableSet.prod (hK₂.preimage (continuous_mul_left _)).measurableSet`. Establish `hfg : ∀ z, f z = g (clsTS K₁ K₂ z)` using `fun z => inv_eq_cls K₁ K₂ f hf z`.

Establish `hfin : (Function.support g).Finite`. Take `⟨t, ht⟩` from `hcs.elim_finite_subcover (fun p => box K₁ K₂ p) hopen (fun z _ => Set.mem_iUnion.2 ⟨clsTS K₁ K₂ z, (mem_box_iff K₁ K₂ _ z).2 rfl⟩)`. Use `t.finite_toSet.subset fun p hp => ?_` and prove the remaining obligations. Establish `hz : ((p.1.out, p.2.out) : G₁ × G₂) ∈ tsupport f` using `subset_tsupport f hp`. Take `⟨i, hi, hzi⟩` from `Set.mem_iUnion₂.1 (ht hz)`.

Establish `hpi` using `(mem_box_iff K₁ K₂ i _).1 hzi`. Rewrite `hpi` using `[cls_out]`. Rewrite using `[hpi]`. Conclude with `hi`. Use `⟨hfin, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `∫ p, f p ∂(μ₁.prod μ₂) = ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂), ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p`. Use `set S := hfin.toFinset with hS`. Establish `hsum : ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂), ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p = ∑ p ∈ S, ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p`. Apply `finsum_eq_sum_of_support_subset` to reduce the goal to its premises. Introduce `p hp`.

Rewrite using `[hS, Set.Finite.coe_toFinset]`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Simplify using `[h]`. Rewrite using `[hsum]`.

Establish `hdecomp : f = fun z => ∑ p ∈ S, (box K₁ K₂ p).indicator (fun _ => g p) z`. Use function extensionality and compare the values at `z`. Establish `hind : ∀ p, (box K₁ K₂ p).indicator (fun _ => g p) z = if clsTS K₁ K₂ z = p then g p else 0`. Introduce `p`. Simplify using `only [Set.indicator, mem_box_iff]`.

Simplify using `only [hind, Finset.sum_ite_eq]`. Rewrite using `[hfg z]`. Use `split_ifs with h`. Both sides reduce to the same expression. Rewrite `h` using `[hS, Set.Finite.mem_toFinset, Function.mem_support, not_not]`.

Conclude with `h`. Establish `hbox : ∀ p, (μ₁.prod μ₂) (box K₁ K₂ p) = μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂)`. Introduce `p`. Rewrite using `[box, Measure.prod_prod, measure_preimage_mul_right, measure_preimage_mul]`. Establish `hpiece : ∀ p, ∫ z, (box K₁ K₂ p).indicator (fun _ => g p) z ∂(μ₁.prod μ₂) = ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p`.

Introduce `p`. Rewrite using `[integral_indicator_const _ (hmeas p), Measure.real, hbox p, ENNReal.toReal_mul]`. Distinguish the cases in `hint : Integrable f (μ₁.prod μ₂)`. Establish `hI : ∀ p ∈ S, Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂)`. Introduce `p _`.

Use `(hint.indicator (hmeas p)).congr (Filter.Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Distinguish the cases in `hz : z ∈ box K₁ K₂ p`. Rewrite using `[Set.indicator_of_mem hz, Set.indicator_of_mem hz, hfg z, (mem_box_iff K₁ K₂ p z).1 hz]`. Rewrite using `[Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]`. Use `conv_lhs => rw [hdecomp]`.

Rewrite using `[integral_finset_sum S hI]`. Conclude with `Finset.sum_congr rfl fun p _ => hpiece p`. Rewrite using `[integral_undef hint]`. Establish `hex : ∃ p ∈ S, ¬ Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂)`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Apply `hint` to reduce the goal to its premises. Rewrite using `[hdecomp]`. Conclude with `integrable_finset_sum S hne`. Take `⟨p, -, hnp⟩` from `hex`.

Establish `htop : μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) = ⊤`. Assume the negation of the conclusion as `hne`. Apply `hnp` to reduce the goal to its premises. Rewrite using `[integrable_indicator_iff (hmeas p)]`. Conclude with `integrableOn_const (by rw [hbox p]; exact hne)`.

Establish `h0 : (μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal = 0`. Rewrite using `[← ENNReal.toReal_mul, htop, ENNReal.toReal_top]`. Simplify using `[h0]`.
-/
theorem intTwoSided : Formalism.DoubleCosetMeasures.IntTwoSided := by
  classical
  intro G₁ G₂ _ _ _ _ _ _ _ _ _ _ μ₁ μ₂ _ _ _ _ K₁ K₂ hK₁ hK₂ E _ _ _ f hf hcs
  set g : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂) → E := fun p => f (p.1.out, p.2.out) with hg
  have hopen : ∀ p, IsOpen (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).prod (hK₂.preimage (continuous_mul_left _))
  have hmeas : ∀ p, MeasurableSet (box K₁ K₂ p) := fun p =>
    (hK₁.preimage (continuous_mul_right _)).measurableSet.prod
      (hK₂.preimage (continuous_mul_left _)).measurableSet
  have hfg : ∀ z, f z = g (clsTS K₁ K₂ z) := fun z => inv_eq_cls K₁ K₂ f hf z
  have hfin : (Function.support g).Finite := by
    obtain ⟨t, ht⟩ := hcs.elim_finite_subcover (fun p => box K₁ K₂ p) hopen
      (fun z _ => Set.mem_iUnion.2 ⟨clsTS K₁ K₂ z, (mem_box_iff K₁ K₂ _ z).2 rfl⟩)
    refine t.finite_toSet.subset fun p hp => ?_
    have hz : ((p.1.out, p.2.out) : G₁ × G₂) ∈ tsupport f := subset_tsupport f hp
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (ht hz)
    have hpi := (mem_box_iff K₁ K₂ i _).1 hzi
    rw [cls_out] at hpi
    rw [hpi]
    exact hi
  refine ⟨hfin, ?_⟩
  change ∫ p, f p ∂(μ₁.prod μ₂) = ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
    ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p
  set S := hfin.toFinset with hS
  have hsum : ∑ᶠ p : Quotient (QuotientGroup.rightRel K₁) × (G₂ ⧸ K₂),
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p =
      ∑ p ∈ S, ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    apply finsum_eq_sum_of_support_subset
    intro p hp
    rw [hS, Set.Finite.coe_toFinset]
    intro h
    apply hp
    simp [h]
  rw [hsum]
  have hdecomp : f = fun z => ∑ p ∈ S, (box K₁ K₂ p).indicator (fun _ => g p) z := by
    funext z
    have hind : ∀ p, (box K₁ K₂ p).indicator (fun _ => g p) z =
        if clsTS K₁ K₂ z = p then g p else 0 := by
      intro p
      simp only [Set.indicator, mem_box_iff]
    simp only [hind, Finset.sum_ite_eq]
    rw [hfg z]
    split_ifs with h
    · rfl
    · rw [hS, Set.Finite.mem_toFinset, Function.mem_support, not_not] at h
      exact h
  have hbox : ∀ p, (μ₁.prod μ₂) (box K₁ K₂ p) = μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) := by
    intro p
    rw [box, Measure.prod_prod, measure_preimage_mul_right, measure_preimage_mul]
  have hpiece : ∀ p, ∫ z, (box K₁ K₂ p).indicator (fun _ => g p) z ∂(μ₁.prod μ₂) =
      ((μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal) • g p := by
    intro p
    rw [integral_indicator_const _ (hmeas p), Measure.real, hbox p, ENNReal.toReal_mul]
  by_cases hint : Integrable f (μ₁.prod μ₂)
  · have hI : ∀ p ∈ S, Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      intro p _
      refine (hint.indicator (hmeas p)).congr (Filter.Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ box K₁ K₂ p
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, hfg z, (mem_box_iff K₁ K₂ p z).1 hz]
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]
    conv_lhs => rw [hdecomp]
    rw [integral_finset_sum S hI]
    exact Finset.sum_congr rfl fun p _ => hpiece p
  · rw [integral_undef hint]
    have hex : ∃ p ∈ S, ¬ Integrable ((box K₁ K₂ p).indicator (fun _ => g p)) (μ₁.prod μ₂) := by
      by_contra hne
      push_neg at hne
      apply hint
      rw [hdecomp]
      exact integrable_finset_sum S hne
    obtain ⟨p, -, hnp⟩ := hex
    have htop : μ₁ (K₁ : Set G₁) * μ₂ (K₂ : Set G₂) = ⊤ := by
      by_contra hne
      apply hnp
      rw [integrable_indicator_iff (hmeas p)]
      exact integrableOn_const (by rw [hbox p]; exact hne)
    have h0 : (μ₁ (K₁ : Set G₁)).toReal * (μ₂ (K₂ : Set G₂)).toReal = 0 := by
      rw [← ENNReal.toReal_mul, htop, ENNReal.toReal_top]
    simp [h0]

end Formalism.DoubleCosetMeasures.P
