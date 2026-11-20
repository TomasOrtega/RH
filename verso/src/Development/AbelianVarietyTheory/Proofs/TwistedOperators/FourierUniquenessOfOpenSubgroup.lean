import Mathlib
open MeasureTheory

namespace GlobalTheory

open MeasureTheory in
/- English proof (translation)
Introduce `H A _ _ _ _ _ μ _ _ χ hs ha0 h0t hadd L hL hsep φ Kc hK hsupp hφL hint`. Assume the negation of the conclusion as `hφ`. Choose the witnesses or unpack the hypotheses as in `⟨t₀, ht₀⟩ : ∃ t, φ t ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Conclude with `hφ (funext h)`. Establish `hχne : ∀ a s, χ a s ≠ 0` using `fun a s h => by`. Use `hs a s (-s)` as an intermediate fact. Rewrite `this` using `[add_neg_cancel, ha0, h, zero_mul]`. Conclude with `one_ne_zero this`.

Use `haveI : DiscreteTopology (H ⧸ L) := QuotientAddGroup.discreteTopology hL`. Establish `hTfin : (QuotientAddGroup.mk '' Kc : Set (H ⧸ L)).Finite` using `(hK.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Set `r : H ⧸ L → H` to `Quotient.out`. Establish `hr : ∀ t : H, ∃ l ∈ L, r (t : H ⧸ L) = t + l` using `fun t => by`. Take `⟨l, hl⟩` from `QuotientAddGroup.mk_out_eq_add L t`.

Conclude with `⟨l, l.2, hl⟩`. Establish `hmkr : ∀ q : H ⧸ L, ((r q : H) : H ⧸ L) = q` using `fun q => Quotient.out_eq q`. Establish `hpre : ∀ q : H ⧸ L, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) : Set H) = (fun h => -r q + h) ⁻¹' (L : Set H)`. Introduce `q`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]`. Use `conv_lhs => rw [← hmkr q]`. Rewrite using `[eq_comm]`. Conclude with `QuotientAddGroup.eq`. Establish `hmeas : ∀ q : H ⧸ L, μ (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) = μ L`.

Introduce `q`. Rewrite using `[hpre, measure_preimage_add]`. Establish `hmset : ∀ q : H ⧸ L, MeasurableSet (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)))`. Introduce `q`. Rewrite using `[hpre]`.

Conclude with `(hL.preimage (continuous_add_left (-r q))).measurableSet`. Establish `hLtop : μ L < ⊤`. Establish `hsub : (QuotientAddGroup.mk ⁻¹' ({(t₀ : H ⧸ L)} : Set (H ⧸ L))) ⊆ Kc`. Introduce `x hx`. Assume the negation of the conclusion as `hxK`.

Establish `hx' : -t₀ + x ∈ L` using `QuotientAddGroup.eq.mp hx.symm`. Use `hφL t₀ _ hx'` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left, hsupp x hxK]`. Conclude with `ht₀ this.symm`. Rewrite using `[← hmeas (t₀ : H ⧸ L)]`.

Conclude with `(measure_mono hsub).trans_lt hK.measure_lt_top`. Establish `hLpos : 0 < μ.real L`. Rewrite using `[measureReal_def]`. Conclude with `ENNReal.toReal_pos (hL.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLtop.ne`. Establish `hχL : ∀ a, (∀ l ∈ L, χ a l = 1) → ∀ t l, l ∈ L → χ a (t + l) = χ a t`.

Introduce `a ha t l hl`. Rewrite using `[hs, ha l hl, mul_one]`. Establish `hsum : ∀ a, (∀ l ∈ L, χ a l = 1) → ∑ q ∈ hTfin.toFinset, χ a (r q) * φ (r q) = 0`. Introduce `a ha`. Establish `hpt : (fun t => χ a t * φ t) = fun t => ∑ q ∈ hTfin.toFinset, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))).indicator (fun _ => χ a (r q) * φ (r q)) t`.

Use function extensionality and compare the values at `t`. Take `⟨l, hl, hrt⟩` from `hr t`. Distinguish the cases in `htT : (t : H ⧸ L) ∈ (QuotientAddGroup.mk '' Kc : Set (H ⧸ L))`. Rewrite using `[Finset.sum_eq_single (t : H ⧸ L)]`. Rewrite using `[Set.indicator_of_mem (show t ∈ QuotientAddGroup.mk ⁻¹' ({(t : H ⧸ L)} : Set (H ⧸ L)) from rfl), hrt, hχL a ha t l hl, hφL t l hl]`.

Introduce `q _ hq`. Conclude with `Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => hq (Set.mem_singleton_iff.mp h).symm) _`. Introduce `h`. Conclude with `absurd (hTfin.mem_toFinset.mpr htT) h`. Establish `htK : t ∉ Kc` using `fun h => htT ⟨t, h, rfl⟩`.

Rewrite using `[hsupp t htK, mul_zero]`. Use `symm`. Use `Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => htT ?_) _` and prove the remaining obligations. Rewrite using `[show (t : H ⧸ L) = q from Set.mem_singleton_iff.mp h]`. Conclude with `hTfin.mem_toFinset.mp hq`.

Establish `hI` using `hint a ha`. Rewrite `hI` using `[hpt, integral_finset_sum]`. Rewrite `hI` using `[integral_indicator_const _ (hmset _), measureReal_def, hmeas, ← measureReal_def]`. Rewrite `hI` using `[← Finset.smul_sum]`. Conclude with `(smul_eq_zero.mp hI).resolve_left hLpos.ne'`.

Introduce `q _`. Use `IntegrableOn.integrable_indicator ?_ (hmset q)` and prove the remaining obligations. Conclude with `integrableOn_const (by rw [hmeas]; exact hLtop.ne)`. Set `A' : AddSubmonoid A` to `{ carrier := {a | ∀ l ∈ L, χ a l = 1} zero_mem' := fun l _ => h0t l add_mem' := fun {a b} ha hb l hl => by rw [hadd, ha l hl, hb l hl, mul_one] }`. Set `f : H ⧸ L → (Multiplicative A' →* ℂ)` to `fun q => { toFun := fun g => χ ((Multiplicative.toAdd g : A') : A) (r q) map_one' := h0t _ map_mul' := fun g g' => hadd _ _ _ }`.

Establish `hfinj : Function.Injective f`. Introduce `q q' hqq`. Assume the negation of the conclusion as `hne`. Establish `hx : r q - r q' ∉ L`. Introduce `hx`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[← hmkr q, ← hmkr q']`. Use `QuotientAddGroup.eq.mpr ?_` and prove the remaining obligations. Use `L.neg_mem hx` as an intermediate fact. Rewrite `this` using `[neg_sub, ← neg_add_eq_sub]`. Then use the resulting hypothesis.

Take `⟨a, ha, hax⟩` from `hsep _ hx`. Establish `hval` using `DFunLike.congr_fun hqq (Multiplicative.ofAdd (⟨a, ha⟩ : A'))`. Express the relevant statement in the definitionally equal form `χ a (r q) = χ a (r q') at hval`. Apply `hax` to reduce the goal to its premises. Establish `e : χ a (r q) = χ a (r q - r q') * χ a (r q')` using `by rw [← hs, sub_add_cancel]`.

Rewrite `e` using `[hval]`. Conclude with `mul_right_cancel₀ (hχne a (r q')) (by rw [one_mul]; exact e.symm)`. Establish `hli : LinearIndependent ℂ (fun q : hTfin.toFinset => (f q : Multiplicative A' → ℂ))` using `(linearIndependent_monoidHom (Multiplicative A') ℂ).comp (fun q : hTfin.toFinset => f q) (hfinj.comp Subtype.val_injective)`. Establish `hzero` using `Fintype.linearIndependent_iff.mp hli (fun q => φ (r q)) (by`. Use function extensionality and compare the values at `g`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Establish `h` using `hsum _ (Multiplicative.toAdd g).2`. Rewrite `h` using `[← Finset.sum_coe_sort]`. Use `Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h` and prove the remaining obligations. Conclude with `mul_comm _ _)`.

Establish `ht₀T : (t₀ : H ⧸ L) ∈ hTfin.toFinset` using `hTfin.mem_toFinset.mpr ⟨t₀, by_contra fun h => ht₀ (hsupp t₀ h), rfl⟩`. Establish `h0` using `hzero ⟨_, ht₀T⟩`. Take `⟨l, hl, hrt⟩` from `hr t₀`. Express the relevant statement in the definitionally equal form `φ (r (t₀ : H ⧸ L)) = 0 at h0`. Rewrite `h0` using `[hrt, hφL t₀ l hl]`.

Conclude with `ht₀ h0`.
-/
theorem _root_.GlobalTheory.fourier_uniqueness_of_openSubgroup : ∀ {H A : Type} [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H] [MeasurableSpace H] [BorelSpace H] (μ : Measure H) [μ.IsAddHaarMeasure] [AddCommGroup A] (χ : A → H → ℂ), (∀ a s t, χ a (s + t) = χ a s * χ a t) → (∀ a, χ a 0 = 1) → (∀ t, χ 0 t = 1) → (∀ a b t, χ (a + b) t = χ a t * χ b t) → ∀ L : AddSubgroup H, IsOpen (L : Set H) → (∀ x, x ∉ L → ∃ a, (∀ l ∈ L, χ a l = 1) ∧ χ a x ≠ 1) → ∀ (φ : H → ℂ) (Kc : Set H), IsCompact Kc → (∀ t, t ∉ Kc → φ t = 0) → (∀ t, ∀ l ∈ L, φ (t + l) = φ t) → (∀ a, (∀ l ∈ L, χ a l = 1) → ∫ t, χ a t * φ t ∂μ = 0) → φ = 0 := by
  intro H A _ _ _ _ _ μ _ _ χ hs ha0 h0t hadd L hL hsep φ Kc hK hsupp hφL hint
  by_contra hφ
  obtain ⟨t₀, ht₀⟩ : ∃ t, φ t ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (funext h)
  have hχne : ∀ a s, χ a s ≠ 0 := fun a s h => by
    have := hs a s (-s)
    rw [add_neg_cancel, ha0, h, zero_mul] at this
    exact one_ne_zero this
  haveI : DiscreteTopology (H ⧸ L) := QuotientAddGroup.discreteTopology hL
  have hTfin : (QuotientAddGroup.mk '' Kc : Set (H ⧸ L)).Finite :=
    (hK.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let r : H ⧸ L → H := Quotient.out
  have hr : ∀ t : H, ∃ l ∈ L, r (t : H ⧸ L) = t + l := fun t => by
    obtain ⟨l, hl⟩ := QuotientAddGroup.mk_out_eq_add L t
    exact ⟨l, l.2, hl⟩
  have hmkr : ∀ q : H ⧸ L, ((r q : H) : H ⧸ L) = q := fun q => Quotient.out_eq q
  have hpre : ∀ q : H ⧸ L, (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) : Set H) =
      (fun h => -r q + h) ⁻¹' (L : Set H) := by
    intro q
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    conv_lhs => rw [← hmkr q]
    rw [eq_comm]
    exact QuotientAddGroup.eq
  have hmeas : ∀ q : H ⧸ L, μ (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) = μ L := by
    intro q
    rw [hpre, measure_preimage_add]
  have hmset : ∀ q : H ⧸ L, MeasurableSet (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))) := by
    intro q
    rw [hpre]
    exact (hL.preimage (continuous_add_left (-r q))).measurableSet
  have hLtop : μ L < ⊤ := by
    have hsub : (QuotientAddGroup.mk ⁻¹' ({(t₀ : H ⧸ L)} : Set (H ⧸ L))) ⊆ Kc := by
      intro x hx
      by_contra hxK
      have hx' : -t₀ + x ∈ L := QuotientAddGroup.eq.mp hx.symm
      have := hφL t₀ _ hx'
      rw [add_neg_cancel_left, hsupp x hxK] at this
      exact ht₀ this.symm
    rw [← hmeas (t₀ : H ⧸ L)]
    exact (measure_mono hsub).trans_lt hK.measure_lt_top
  have hLpos : 0 < μ.real L := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hL.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLtop.ne
  have hχL : ∀ a, (∀ l ∈ L, χ a l = 1) → ∀ t l, l ∈ L → χ a (t + l) = χ a t := by
    intro a ha t l hl
    rw [hs, ha l hl, mul_one]
  have hsum : ∀ a, (∀ l ∈ L, χ a l = 1) →
      ∑ q ∈ hTfin.toFinset, χ a (r q) * φ (r q) = 0 := by
    intro a ha
    have hpt : (fun t => χ a t * φ t) = fun t => ∑ q ∈ hTfin.toFinset,
        (QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L))).indicator
          (fun _ => χ a (r q) * φ (r q)) t := by
      funext t
      obtain ⟨l, hl, hrt⟩ := hr t
      by_cases htT : (t : H ⧸ L) ∈ (QuotientAddGroup.mk '' Kc : Set (H ⧸ L))
      · rw [Finset.sum_eq_single (t : H ⧸ L)]
        · rw [Set.indicator_of_mem (show t ∈ QuotientAddGroup.mk ⁻¹' ({(t : H ⧸ L)} : Set (H ⧸ L)) from rfl), hrt, hχL a ha t l hl, hφL t l hl]
        · intro q _ hq
          exact Set.indicator_of_notMem (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from
            fun h => hq (Set.mem_singleton_iff.mp h).symm) _
        · intro h
          exact absurd (hTfin.mem_toFinset.mpr htT) h
      · have htK : t ∉ Kc := fun h => htT ⟨t, h, rfl⟩
        rw [hsupp t htK, mul_zero]
        symm
        refine Finset.sum_eq_zero fun q hq => Set.indicator_of_notMem
          (show t ∉ QuotientAddGroup.mk ⁻¹' ({q} : Set (H ⧸ L)) from fun h => htT ?_) _
        rw [show (t : H ⧸ L) = q from Set.mem_singleton_iff.mp h]
        exact hTfin.mem_toFinset.mp hq
    have hI := hint a ha
    rw [hpt, integral_finset_sum] at hI
    · simp_rw [integral_indicator_const _ (hmset _), measureReal_def, hmeas,
        ← measureReal_def] at hI
      rw [← Finset.smul_sum] at hI
      exact (smul_eq_zero.mp hI).resolve_left hLpos.ne'
    · intro q _
      refine IntegrableOn.integrable_indicator ?_ (hmset q)
      exact integrableOn_const (by rw [hmeas]; exact hLtop.ne)
  let A' : AddSubmonoid A :=
    { carrier := {a | ∀ l ∈ L, χ a l = 1}
      zero_mem' := fun l _ => h0t l
      add_mem' := fun {a b} ha hb l hl => by rw [hadd, ha l hl, hb l hl, mul_one] }
  let f : H ⧸ L → (Multiplicative A' →* ℂ) := fun q =>
    { toFun := fun g => χ ((Multiplicative.toAdd g : A') : A) (r q)
      map_one' := h0t _
      map_mul' := fun g g' => hadd _ _ _ }
  have hfinj : Function.Injective f := by
    intro q q' hqq
    by_contra hne
    have hx : r q - r q' ∉ L := by
      intro hx
      apply hne
      rw [← hmkr q, ← hmkr q']
      refine QuotientAddGroup.eq.mpr ?_
      have := L.neg_mem hx
      rwa [neg_sub, ← neg_add_eq_sub] at this
    obtain ⟨a, ha, hax⟩ := hsep _ hx
    have hval := DFunLike.congr_fun hqq (Multiplicative.ofAdd (⟨a, ha⟩ : A'))
    change χ a (r q) = χ a (r q') at hval
    apply hax
    have e : χ a (r q) = χ a (r q - r q') * χ a (r q') := by rw [← hs, sub_add_cancel]
    rw [hval] at e
    exact mul_right_cancel₀ (hχne a (r q')) (by rw [one_mul]; exact e.symm)
  have hli : LinearIndependent ℂ
      (fun q : hTfin.toFinset => (f q : Multiplicative A' → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative A') ℂ).comp (fun q : hTfin.toFinset => f q)
      (hfinj.comp Subtype.val_injective)
  have hzero := Fintype.linearIndependent_iff.mp hli (fun q => φ (r q)) (by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have h := hsum _ (Multiplicative.toAdd g).2
    rw [← Finset.sum_coe_sort] at h
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h
    exact mul_comm _ _)
  have ht₀T : (t₀ : H ⧸ L) ∈ hTfin.toFinset :=
    hTfin.mem_toFinset.mpr ⟨t₀, by_contra fun h => ht₀ (hsupp t₀ h), rfl⟩
  have h0 := hzero ⟨_, ht₀T⟩
  obtain ⟨l, hl, hrt⟩ := hr t₀
  change φ (r (t₀ : H ⧸ L)) = 0 at h0
  rw [hrt, hφL t₀ l hl] at h0
  exact ht₀ h0

end GlobalTheory
