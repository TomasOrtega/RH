import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
open GlobalTheory.WeilM

noncomputable section

open scoped Classical Topology

namespace GlobalTheory.CharForm

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]

def cosetInd (U : AddSubgroup X) (q : X ⧸ U) : X → ℂ := fun x => if (x : X ⧸ U) = q then 1 else 0

/- English proof (translation)
Use `haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous QuotientAddGroup.continuous_mk`. Establish `hK : IsCompact ((fun u => q.out + u) '' (U : Set X))` using `hUc.image (continuous_const.add continuous_id)`. Establish `hKc : IsClosed ((fun u => q.out + u) '' (U : Set X))` using `(Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)`.

Use `HasCompactSupport.intro' hK hKc fun x hx => ?_` and prove the remaining obligations. Simplify using `only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]`. Introduce `hxq`. Apply `hx` to reduce the goal to its premises. Use `⟨-q.out + x, ?_, by simp⟩` and prove the remaining obligations.

Rewrite `hxq` using `[← QuotientAddGroup.out_eq' q]`. Conclude with `QuotientAddGroup.eq.mp hxq.symm`.
-/
theorem cosetInd_mem_SB (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X)) (q : X ⧸ U) :
    cosetInd U q ∈ SB X := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  refine ⟨?_, ?_⟩
  · exact (IsLocallyConstant.of_discrete (fun q' : X ⧸ U => if q' = q then (1 : ℂ) else 0)).comp_continuous
      QuotientAddGroup.continuous_mk
  · have hK : IsCompact ((fun u => q.out + u) '' (U : Set X)) := hUc.image (continuous_const.add continuous_id)
    have hKc : IsClosed ((fun u => q.out + u) '' (U : Set X)) :=
      (Homeomorph.addLeft q.out).isClosedMap _ (AddSubgroup.isClosed_of_isOpen U hUo)
    refine HasCompactSupport.intro' hK hKc fun x hx => ?_
    simp only [cosetInd, ite_eq_right_iff, one_ne_zero, imp_false]
    intro hxq
    apply hx
    refine ⟨-q.out + x, ?_, by simp⟩
    rw [← QuotientAddGroup.out_eq' q] at hxq
    exact QuotientAddGroup.eq.mp hxq.symm

/- English proof (translation)
Establish `hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X)` using `fun x => ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)`. Use `choose W hWo _ hWN _ using fun x => H _ (hN x)`. Take `⟨t, -, hcov⟩` from `hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ => ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)`. Establish `hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X)` using `Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)`. Take `⟨U, hUo, hUc, hUN, hUk⟩` from `H _ hNm`.

Use `⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩` and prove the remaining obligations. Establish `hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y`. Introduce `y hy u hu`. Take `⟨x, hxt, hyx⟩` from `Set.mem_iUnion₂.mp (hcov hy)`. Establish `hu' : u ∈ W x` using `Set.mem_iInter₂.mp (hUN hu).2 x hxt`.

Establish `h1 : g (x + (y - x)) = g x` using `hWN x hyx`. Establish `h2 : g (x + (y - x + u)) = g x` using `hWN x ((W x).add_mem hyx hu')`. Rewrite `h1` using `[add_sub_cancel]`. Rewrite `h2` using `[← add_assoc, add_sub_cancel]`. Rewrite using `[h1, h2]`.

Introduce `y u hu`. Distinguish the cases in `hy : y ∈ tsupport g`. Conclude with `hA y hy u hu`. Distinguish the cases in `hyu : y + u ∈ tsupport g`. Use `hA _ hyu (-u) (U.neg_mem hu)` as an intermediate fact.

Rewrite `this` using `[add_neg_cancel_right]`. Conclude with `this.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]`.
-/
theorem exists_periodic {C : Set (X → ℂ)}
    (H : ∀ N ∈ 𝓝 (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) {V : Set X} (hV : V ∈ 𝓝 (0 : X)) :
    ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ V ∧
      (∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) ∧ ∀ x, ∀ u ∈ U, g (x + u) = g x := by
  have hN : ∀ x, {y | g (x + y) = g x} ∈ 𝓝 (0 : X) := fun x =>
    ((hg.1.isOpen_fiber (g x)).preimage (continuous_const_add x)).mem_nhds (by simp)
  choose W hWo _ hWN _ using fun x => H _ (hN x)
  obtain ⟨t, -, hcov⟩ := hg.2.isCompact.elim_nhds_subcover (fun x => {y | y - x ∈ W x}) fun x _ =>
    ((hWo x).preimage (continuous_id.sub continuous_const)).mem_nhds (by simp)
  have hNm : V ∩ ⋂ x ∈ t, (W x : Set X) ∈ 𝓝 (0 : X) :=
    Filter.inter_mem hV ((Filter.biInter_finset_mem t).2 fun x _ => (hWo x).mem_nhds (W x).zero_mem)
  obtain ⟨U, hUo, hUc, hUN, hUk⟩ := H _ hNm
  refine ⟨U, hUo, hUc, fun u hu => (hUN hu).1, hUk, ?_⟩
  have hA : ∀ y ∈ tsupport g, ∀ u ∈ U, g (y + u) = g y := by
    intro y hy u hu
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.mp (hcov hy)
    have hu' : u ∈ W x := Set.mem_iInter₂.mp (hUN hu).2 x hxt
    have h1 : g (x + (y - x)) = g x := hWN x hyx
    have h2 : g (x + (y - x + u)) = g x := hWN x ((W x).add_mem hyx hu')
    rw [add_sub_cancel] at h1
    rw [← add_assoc, add_sub_cancel] at h2
    rw [h1, h2]
  intro y u hu
  by_cases hy : y ∈ tsupport g
  · exact hA y hy u hu
  by_cases hyu : y + u ∈ tsupport g
  · have := hA _ hyu (-u) (U.neg_mem hu)
    rw [add_neg_cancel_right] at this
    exact this.symm
  rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyu]

/- English proof (translation)
Use `haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo`. Establish `hout : ∀ x : X, g ((x : X ⧸ U).out) = g x` using `fun x => by`. Take `⟨h, hh⟩` from `QuotientAddGroup.mk_out_eq_add U x`. Rewrite using `[hh]`. Conclude with `hper x h h.2`.

Establish `hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite` using `(hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete`. Use `set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT`. Establish `hsum : g = ∑ q ∈ T, g q.out • cosetInd U q`. Use function extensionality and compare the values at `x`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]`.

Rewrite using `[Finset.sum_ite_eq]`. Use `split_ifs with hx`. Conclude with `(hout x).symm`. Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `hxs`.

Conclude with `hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))`. Establish `hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0`. Introduce `q hq`. Establish `hx₀ : q.out ∉ U`. Introduce `hm`.

Apply `hq` to reduce the goal to its premises. Rewrite using `[← QuotientAddGroup.out_eq' q]`. Conclude with `(QuotientAddGroup.eq_zero_iff _).mpr hm`. Take `⟨χ, hχC, hχU, hχ1⟩` from `hUk _ hx₀`. Establish `hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q`.

Use function extensionality and compare the values at `x`. Simplify using `only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Use `split_ifs with hxq`. Establish `hm : -q.out + x ∈ U`. Rewrite `hxq` using `[← QuotientAddGroup.out_eq' q]`.

Conclude with `QuotientAddGroup.eq.mp hxq.symm`. Use `hχU _ hm` as an intermediate fact. Rewrite `this` using `[add_neg_cancel_left]`. Then use the resulting hypothesis. Both sides reduce to the same expression. Establish `e` using `ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)`.

Rewrite `e` using `[hmul, map_smul, smul_eq_mul]`. Establish `: (χ q.out - 1) * a (cosetInd U q) = 0` using `by rw [sub_mul, e, one_mul, sub_self]`. Conclude with `(mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)`. Use `conv_lhs => rw [hsum]`. Rewrite using `[map_sum, Finset.sum_eq_single (0 : X ⧸ U)]`.

Rewrite using `[map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]`. Introduce `q _ hq`. Rewrite using `[map_smul, hkill q hq, smul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_insert_self _ _) h`.
-/
theorem apply_eq_of_periodic {C : Set (X → ℂ)} (a : (X → ℂ) →ₗ[ℂ] ℂ)
    (ha : ∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g)
    (U : AddSubgroup X) (hUo : IsOpen (U : Set X)) (hUc : IsCompact (U : Set X))
    (hUk : ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1)
    {g : X → ℂ} (hg : g ∈ SB X) (hper : ∀ x, ∀ u ∈ U, g (x + u) = g x) :
    a g = g 0 * a (cosetInd U 0) := by
  haveI : DiscreteTopology (X ⧸ U) := QuotientAddGroup.discreteTopology hUo
  have hout : ∀ x : X, g ((x : X ⧸ U).out) = g x := fun x => by
    obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add U x
    rw [hh]; exact hper x h h.2
  have hfin : (QuotientAddGroup.mk '' tsupport g : Set (X ⧸ U)).Finite :=
    (hg.2.isCompact.image QuotientAddGroup.continuous_mk).finite_of_discrete
  set T : Finset (X ⧸ U) := insert 0 hfin.toFinset with hT
  have hsum : g = ∑ q ∈ T, g q.out • cosetInd U q := by
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, cosetInd, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    split_ifs with hx
    · exact (hout x).symm
    · apply image_eq_zero_of_notMem_tsupport
      intro hxs
      exact hx (Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr ⟨x, hxs, rfl⟩))
  have hkill : ∀ q : X ⧸ U, q ≠ 0 → a (cosetInd U q) = 0 := by
    intro q hq
    have hx₀ : q.out ∉ U := by
      intro hm
      apply hq
      rw [← QuotientAddGroup.out_eq' q]
      exact (QuotientAddGroup.eq_zero_iff _).mpr hm
    obtain ⟨χ, hχC, hχU, hχ1⟩ := hUk _ hx₀
    have hmul : (fun x => χ x * cosetInd U q x) = χ q.out • cosetInd U q := by
      funext x
      simp only [cosetInd, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      split_ifs with hxq
      · have hm : -q.out + x ∈ U := by
          rw [← QuotientAddGroup.out_eq' q] at hxq
          exact QuotientAddGroup.eq.mp hxq.symm
        have := hχU _ hm
        rwa [add_neg_cancel_left] at this
      · rfl
    have e := ha χ hχC _ (cosetInd_mem_SB U hUo hUc q)
    rw [hmul, map_smul, smul_eq_mul] at e
    have : (χ q.out - 1) * a (cosetInd U q) = 0 := by rw [sub_mul, e, one_mul, sub_self]
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hχ1)
  conv_lhs => rw [hsum]
  rw [map_sum, Finset.sum_eq_single (0 : X ⧸ U)]
  · rw [map_smul, smul_eq_mul, ← QuotientAddGroup.mk_zero, hout]
  · intro q _ hq
    rw [map_smul, hkill q hq, smul_zero]
  · intro h
    exact absurd (Finset.mem_insert_self _ _) h

/- English proof (translation)
Introduce `X _ _ _ C H a ha`. Take `⟨U₀, hU₀o, hU₀c, -, hU₀k⟩` from `H Set.univ Filter.univ_mem`. Use `⟨a (cosetInd U₀ 0), fun g hg => ?_⟩` and prove the remaining obligations. Take `⟨U, hUo, hUc, hUV, hUk, hper⟩` from `exists_periodic H hg (hU₀o.mem_nhds U₀.zero_mem)`. Establish `h1` using `apply_eq_of_periodic a ha U hUo hUc hUk hg hper`.

Establish `h2` using `apply_eq_of_periodic a ha U hUo hUc hUk (cosetInd_mem_SB U₀ hU₀o hU₀c 0) fun x u hu => by`. Establish `: ((u : X) : X ⧸ U₀) = 0` using `(QuotientAddGroup.eq_zero_iff u).mpr (hUV hu)`. Simplify using `only [cosetInd, QuotientAddGroup.mk_add, this, add_zero]`. Establish `h0 : cosetInd U₀ (0 : X ⧸ U₀) 0 = 1` using `by simp [cosetInd]`. Rewrite `h2` using `[h0, one_mul]`.

Rewrite using `[h1, h2, mul_comm]`.
-/
theorem exists_eq_mul_apply_zero : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (C : Set (X → ℂ)),
    (∀ N ∈ nhds (0 : X), ∃ U : AddSubgroup X, IsOpen (U : Set X) ∧ IsCompact (U : Set X) ∧ (U : Set X) ⊆ N ∧
      ∀ x₀ ∉ U, ∃ χ ∈ C, (∀ u ∈ U, χ (x₀ + u) = χ x₀) ∧ χ x₀ ≠ 1) →
    ∀ (a : (X → ℂ) →ₗ[ℂ] ℂ), (∀ χ ∈ C, ∀ g ∈ SB X, a (fun x => χ x * g x) = a g) →
      ∃ c : ℂ, ∀ g ∈ SB X, a g = c * g 0 := by
  intro X _ _ _ C H a ha
  obtain ⟨U₀, hU₀o, hU₀c, -, hU₀k⟩ := H Set.univ Filter.univ_mem
  refine ⟨a (cosetInd U₀ 0), fun g hg => ?_⟩
  obtain ⟨U, hUo, hUc, hUV, hUk, hper⟩ := exists_periodic H hg (hU₀o.mem_nhds U₀.zero_mem)
  have h1 := apply_eq_of_periodic a ha U hUo hUc hUk hg hper
  have h2 := apply_eq_of_periodic a ha U hUo hUc hUk (cosetInd_mem_SB U₀ hU₀o hU₀c 0) fun x u hu => by
    have : ((u : X) : X ⧸ U₀) = 0 := (QuotientAddGroup.eq_zero_iff u).mpr (hUV hu)
    simp only [cosetInd, QuotientAddGroup.mk_add, this, add_zero]
  have h0 : cosetInd U₀ (0 : X ⧸ U₀) 0 = 1 := by simp [cosetInd]
  rw [h0, one_mul] at h2
  rw [h1, h2, mul_comm]

end GlobalTheory.CharForm
