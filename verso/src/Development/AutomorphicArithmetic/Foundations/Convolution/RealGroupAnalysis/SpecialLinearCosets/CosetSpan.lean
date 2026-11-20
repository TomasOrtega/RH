import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.SpecialLinearCosets.GoodU

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.ConvolutionTheory.R2.I
open scoped Classical

/- English proof (translation)
Introduce `G _ _ _ _ hL a ha N hN`. Establish `hlc : IsLocallyConstant a` using `(GroundTheory.LocalField.mem_schwartzBruhat.1 ha).1`. Establish `hcs : HasCompactSupport a` using `(GroundTheory.LocalField.mem_schwartzBruhat.1 ha).2`. Establish `hK : IsCompact (tsupport a)` using `hcs`. Establish `hS : IsOpen {p : G × G | a (p.1 * p.2) = a p.1}`.

Rewrite using `[isOpen_iff_mem_nhds]`. Introduce `p hp`. Establish `hev` using `(IsLocallyConstant.iff_eventually_eq a).1 hlc`. Establish `e1 : ∀ᶠ q : G × G in 𝓝 p, a (q.1 * q.2) = a (p.1 * p.2)` using `((continuous_fst.mul continuous_snd).tendsto p).eventually (hev (p.1 * p.2))`. Establish `e2 : ∀ᶠ q : G × G in 𝓝 p, a q.1 = a p.1` using `(continuous_fst.tendsto p).eventually (hev p.1)`.

Use `filter_upwards [e1, e2] with q h1 h2`. Use `show a (q.1 * q.2) = a q.1`. Rewrite using `[h1, h2]`. Conclude with `hp`. Take `⟨W1, W0, -, hW0, hKW, h1W, hWS⟩` from `generalized_tube_lemma hK (isCompact_singleton (x := (1 : G))) hS (by`.

Introduce and unpack `⟨x, u⟩ ⟨-, hu⟩`. Establish `hu' : u = 1` using `hu`. Substitute `hu'` using the available equality. Use `show a (x * 1) = a x`. Rewrite using `[mul_one])`.

Establish `hN' : N ∩ W0 ∈ 𝓝 (1 : G)` using `Filter.inter_mem hN (hW0.mem_nhds (h1W rfl))`. Take `⟨U, hUo, hUc, hUN⟩` from `hL _ hN'`. Establish `hinv0 : ∀ x ∈ tsupport a, ∀ u ∈ U, a (x * u) = a x` using `fun x hx u hu => hWS (Set.mk_mem_prod (hKW hx) (hUN hu).2)`. Establish `hinv : ∀ x, ∀ u ∈ U, a (x * u) = a x`. Introduce `x u hu`.

Distinguish the cases in `hx : x ∈ tsupport a`. Conclude with `hinv0 x hx u hu`. Distinguish the cases in `hxu : x * u ∈ tsupport a`. Establish `h` using `hinv0 _ hxu u⁻¹ (U.inv_mem hu)`. Rewrite `h` using `[mul_inv_cancel_right]`.

Conclude with `h.symm`. Rewrite using `[image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hx]`. Take `⟨t, -, ht⟩` from `hK.elim_nhds_subcover (fun x => {y : G | x⁻¹ * y ∈ U}) (by`. Introduce `x _`. Establish `ho : IsOpen {y : G | x⁻¹ * y ∈ U}` using `hUo.preimage (continuous_const.mul continuous_id)`.

Use `ho.mem_nhds ?_` and prove the remaining obligations. Use `show x⁻¹ * x ∈ U`. Rewrite using `[inv_mul_cancel]`. Conclude with `U.one_mem)`. Set `r : G → G` to `fun x => Quotient.out (QuotientGroup.mk x : G ⧸ U)`.

Establish `hr : ∀ x, (r x)⁻¹ * x ∈ U` using `fun x => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)`. Establish `h1 : ∀ y ∈ U, ind U y = 1` using `fun y hy => by simp [ind, hy]`. Establish `h0 : ∀ y, y ∉ U → ind U y = 0` using `fun y hy => by simp [ind, hy]`. Use `⟨U, t.image r, a, hUo, hUc, fun x hx => (hUN hx).1, ?_⟩` and prove the remaining obligations. Introduce `x`.

Establish `huniq : ∀ g ∈ t.image r, ∀ g' ∈ t.image r, g⁻¹ * x ∈ U → g'⁻¹ * x ∈ U → g' = g`. Introduce `g hg g' hg' hgx hgx'`. Take `⟨y, -, rfl⟩` from `Finset.mem_image.1 hg`. Take `⟨y', -, rfl⟩` from `Finset.mem_image.1 hg'`. Establish `e : (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk y'`.

Establish `a1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk x` using `QuotientGroup.eq.2 hgx`. Establish `a2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk x` using `QuotientGroup.eq.2 hgx'`. Establish `b1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk y` using `QuotientGroup.out_eq' _`. Establish `b2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk y'` using `QuotientGroup.out_eq' _`. Rewrite using `[← b1, ← b2, a1, a2]`.

Use `show Quotient.out (QuotientGroup.mk y' : G ⧸ U) = Quotient.out (QuotientGroup.mk y : G ⧸ U)`. Rewrite using `[e]`. Distinguish the cases in `h : ∃ g ∈ t.image r, g⁻¹ * x ∈ U`. Take `⟨g, hg, hgx⟩` from `h`. Rewrite using `[Finset.sum_eq_single g, h1 _ hgx, mul_one]`.

Establish `e` using `hinv g _ hgx`. Rewrite `e` using `[mul_inv_cancel_left]`. Conclude with `e`. Introduce `b hb hne`. Rewrite using `[h0, mul_zero]`.

Introduce `hbx`. Conclude with `hne (huniq g hg b hb hgx hbx)`. Introduce `hn`. Conclude with `absurd hg hn`. Establish `hx0 : a x = 0`.

Assume the negation of the conclusion as `hne`. Establish `hxs : x ∈ tsupport a` using `subset_tsupport _ hne`. Take `⟨y, hy, hxy⟩` from `Set.mem_iUnion₂.1 (ht hxs)`. Use `h ⟨r y, Finset.mem_image_of_mem r hy, ?_⟩` and prove the remaining obligations. Establish `e : (r y)⁻¹ * x = ((r y)⁻¹ * y) * (y⁻¹ * x)` using `by group`.

Rewrite using `[e]`. Conclude with `U.mul_mem (hr y) hxy`. Rewrite using `[hx0]`. Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `g hg`. Rewrite using `[h0 _ (fun hgx => h ⟨g, hg, hgx⟩), mul_zero]`.
-/
theorem UpperTheory.ConvolutionTheory.R2.I.cosetSpan :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G], Lgrp G → ∀ a ∈ SB G, ∀ N ∈ 𝓝 (1 : G),
      ∃ (U : Subgroup G) (s : Finset G) (c : G → ℂ), IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ N ∧
        ∀ x, a x = ∑ g ∈ s, c g * ind U (g⁻¹ * x) := by
  intro G _ _ _ _ hL a ha N hN
  have hlc : IsLocallyConstant a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).1
  have hcs : HasCompactSupport a := (GroundTheory.LocalField.mem_schwartzBruhat.1 ha).2
  have hK : IsCompact (tsupport a) := hcs
  have hS : IsOpen {p : G × G | a (p.1 * p.2) = a p.1} := by
    rw [isOpen_iff_mem_nhds]
    intro p hp
    have hev := (IsLocallyConstant.iff_eventually_eq a).1 hlc
    have e1 : ∀ᶠ q : G × G in 𝓝 p, a (q.1 * q.2) = a (p.1 * p.2) :=
      ((continuous_fst.mul continuous_snd).tendsto p).eventually (hev (p.1 * p.2))
    have e2 : ∀ᶠ q : G × G in 𝓝 p, a q.1 = a p.1 :=
      (continuous_fst.tendsto p).eventually (hev p.1)
    filter_upwards [e1, e2] with q h1 h2
    show a (q.1 * q.2) = a q.1
    rw [h1, h2]
    exact hp
  obtain ⟨W1, W0, -, hW0, hKW, h1W, hWS⟩ :=
    generalized_tube_lemma hK (isCompact_singleton (x := (1 : G))) hS (by
      rintro ⟨x, u⟩ ⟨-, hu⟩
      have hu' : u = 1 := hu
      subst hu'
      show a (x * 1) = a x
      rw [mul_one])
  have hN' : N ∩ W0 ∈ 𝓝 (1 : G) := Filter.inter_mem hN (hW0.mem_nhds (h1W rfl))
  obtain ⟨U, hUo, hUc, hUN⟩ := hL _ hN'
  have hinv0 : ∀ x ∈ tsupport a, ∀ u ∈ U, a (x * u) = a x := fun x hx u hu =>
    hWS (Set.mk_mem_prod (hKW hx) (hUN hu).2)
  have hinv : ∀ x, ∀ u ∈ U, a (x * u) = a x := by
    intro x u hu
    by_cases hx : x ∈ tsupport a
    · exact hinv0 x hx u hu
    by_cases hxu : x * u ∈ tsupport a
    · have h := hinv0 _ hxu u⁻¹ (U.inv_mem hu)
      rw [mul_inv_cancel_right] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hxu, image_eq_zero_of_notMem_tsupport hx]
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun x => {y : G | x⁻¹ * y ∈ U}) (by
    intro x _
    have ho : IsOpen {y : G | x⁻¹ * y ∈ U} :=
      hUo.preimage (continuous_const.mul continuous_id)
    refine ho.mem_nhds ?_
    show x⁻¹ * x ∈ U
    rw [inv_mul_cancel]
    exact U.one_mem)
  let r : G → G := fun x => Quotient.out (QuotientGroup.mk x : G ⧸ U)
  have hr : ∀ x, (r x)⁻¹ * x ∈ U := fun x => QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
  have h1 : ∀ y ∈ U, ind U y = 1 := fun y hy => by simp [ind, hy]
  have h0 : ∀ y, y ∉ U → ind U y = 0 := fun y hy => by simp [ind, hy]
  refine ⟨U, t.image r, a, hUo, hUc, fun x hx => (hUN hx).1, ?_⟩
  intro x
  have huniq : ∀ g ∈ t.image r, ∀ g' ∈ t.image r, g⁻¹ * x ∈ U → g'⁻¹ * x ∈ U → g' = g := by
    intro g hg g' hg' hgx hgx'
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hg
    obtain ⟨y', -, rfl⟩ := Finset.mem_image.1 hg'
    have e : (QuotientGroup.mk y : G ⧸ U) = QuotientGroup.mk y' := by
      have a1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx
      have a2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk x := QuotientGroup.eq.2 hgx'
      have b1 : (QuotientGroup.mk (r y) : G ⧸ U) = QuotientGroup.mk y := QuotientGroup.out_eq' _
      have b2 : (QuotientGroup.mk (r y') : G ⧸ U) = QuotientGroup.mk y' := QuotientGroup.out_eq' _
      rw [← b1, ← b2, a1, a2]
    show Quotient.out (QuotientGroup.mk y' : G ⧸ U) = Quotient.out (QuotientGroup.mk y : G ⧸ U)
    rw [e]
  by_cases h : ∃ g ∈ t.image r, g⁻¹ * x ∈ U
  · obtain ⟨g, hg, hgx⟩ := h
    rw [Finset.sum_eq_single g, h1 _ hgx, mul_one]
    · have e := hinv g _ hgx
      rw [mul_inv_cancel_left] at e
      exact e
    · intro b hb hne
      rw [h0, mul_zero]
      intro hbx
      exact hne (huniq g hg b hb hgx hbx)
    · intro hn
      exact absurd hg hn
  · have hx0 : a x = 0 := by
      by_contra hne
      have hxs : x ∈ tsupport a := subset_tsupport _ hne
      obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht hxs)
      refine h ⟨r y, Finset.mem_image_of_mem r hy, ?_⟩
      have e : (r y)⁻¹ * x = ((r y)⁻¹ * y) * (y⁻¹ * x) := by group
      rw [e]
      exact U.mul_mem (hr y) hxy
    rw [hx0]
    symm
    apply Finset.sum_eq_zero
    intro g hg
    rw [h0 _ (fun hgx => h ⟨g, hg, hgx⟩), mul_zero]
