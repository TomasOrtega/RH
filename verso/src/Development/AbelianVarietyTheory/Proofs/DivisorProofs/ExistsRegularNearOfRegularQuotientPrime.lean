import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingOfRegularQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalLocalGeneratorsStatement

open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

open IsLocalRing TensorProduct in
/- English proof (translation)
Take `⟨T, hTc, hT⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ`. Take `⟨U, hUc, hU⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank hm`. Set `L : Finset A` to `U.image Quotient.out`. Establish `hJm : J ≤ maximalIdeal A`. Use `le_maximalIdeal fun h => ?_` and prove the remaining obligations.

Establish `: Subsingleton (A ⧸ J)` using `Ideal.Quotient.subsingleton_iff.mpr h`. Conclude with `not_subsingleton (A ⧸ J) this`. Establish `hL : ∀ l ∈ L, l ∈ maximalIdeal A`. Introduce `l hl`. Take `⟨u, hu, rfl⟩` from `Finset.mem_image.mp hl`.

Establish `hu' : u ∈ maximalIdeal (A ⧸ J)` using `hU ▸ Ideal.subset_span hu`. Introduce `hunit`. Apply `hu'` to reduce the goal to its premises. Use `hunit.map (Ideal.Quotient.mk J)` as an intermediate fact. Rewrite `this` using `[Ideal.Quotient.mk_out]`. Then use the resulting hypothesis.

Establish `hspan : maximalIdeal A = Ideal.span (↑(T ∪ L) : Set A)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `hx' : Ideal.Quotient.mk J x ∈ Ideal.span (Ideal.Quotient.mk J '' (L : Set A))`. Establish `e : Ideal.Quotient.mk J '' (L : Set A) = (U : Set (A ⧸ J))`.

Use extensionality with `u`. Simplify using `[L, Ideal.Quotient.mk_out]`. Rewrite using `[e]`. Express the relevant statement in the definitionally equal form `_ ∈ Submodule.span (A ⧸ J) _`. Rewrite using `[hU]`.

Introduce `hunit`. Take `⟨y, hy⟩` from `hunit.exists_right_inv`. Take `⟨y', rfl⟩` from `Ideal.Quotient.mk_surjective y`. Establish `h1 : x * y' - 1 ∈ J` using `Ideal.Quotient.eq.mp (by simpa using hy)`. Apply `(maximalIdeal.isMaximal A).ne_top` to reduce the goal to its premises.

Rewrite using `[Ideal.eq_top_iff_one]`. Simplify using `using Ideal.sub_mem _ (Ideal.mul_mem_right y' _ hx) (hJm h1)`. Rewrite `hx'` using `[← Ideal.map_span]`. Take `⟨y, hy, hyx⟩` from `Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx'`. Establish `hxy : x - y ∈ J`.

Rewrite using `[← Ideal.Quotient.eq]`. Conclude with `hyx.symm`. Rewrite `hxy` using `[← hT]`. Rewrite using `[Finset.coe_union, Ideal.span_union]`. Use `Submodule.add_mem_sup hxy hy` as an intermediate fact.

Simplify using `using this`. Rewrite using `[Ideal.span_le]`. Introduce `x hx`. Break down `Finset.mem_union.mp hx with hx | hx` into its components or cases. Conclude with `hJm (hT ▸ Ideal.subset_span hx)`.

Conclude with `hL x hx`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hTc, ← hUc]`. Use `gcongr`. Conclude with `Finset.card_image_le`.
-/
private lemma spanFinrank_maximalIdeal_le_add (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)] (hJ : J.FG) (hm : (maximalIdeal (A ⧸ J)).FG) :
    (maximalIdeal A).spanFinrank ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
  classical
  obtain ⟨T, hTc, hT⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hm
  let L : Finset A := U.image Quotient.out
  have hJm : J ≤ maximalIdeal A := by
    refine le_maximalIdeal fun h => ?_
    have : Subsingleton (A ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr h
    exact not_subsingleton (A ⧸ J) this
  have hL : ∀ l ∈ L, l ∈ maximalIdeal A := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hu' : u ∈ maximalIdeal (A ⧸ J) := hU ▸ Ideal.subset_span hu
    intro hunit
    apply hu'
    have := hunit.map (Ideal.Quotient.mk J)
    rwa [Ideal.Quotient.mk_out] at this
  have hspan : maximalIdeal A = Ideal.span (↑(T ∪ L) : Set A) := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.span (Ideal.Quotient.mk J '' (L : Set A)) := by
        have e : Ideal.Quotient.mk J '' (L : Set A) = (U : Set (A ⧸ J)) := by
          ext u; simp [L, Ideal.Quotient.mk_out]
        rw [e]
        change _ ∈ Submodule.span (A ⧸ J) _
        rw [hU]
        intro hunit
        obtain ⟨y, hy⟩ := hunit.exists_right_inv
        obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : x * y' - 1 ∈ J := Ideal.Quotient.eq.mp (by simpa using hy)
        apply (maximalIdeal.isMaximal A).ne_top
        rw [Ideal.eq_top_iff_one]
        simpa using Ideal.sub_mem _ (Ideal.mul_mem_right y' _ hx) (hJm h1)
      rw [← Ideal.map_span] at hx'
      obtain ⟨y, hy, hyx⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx'
      have hxy : x - y ∈ J := by
        rw [← Ideal.Quotient.eq]; exact hyx.symm
      rw [← hT] at hxy
      rw [Finset.coe_union, Ideal.span_union]
      have := Submodule.add_mem_sup hxy hy
      simpa using this
    · rw [Ideal.span_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hJm (hT ▸ Ideal.subset_span hx)
      · exact hL x hx
  calc (maximalIdeal A).spanFinrank ≤ (T ∪ L).card := hspan ▸ _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _
    _ ≤ T.card + L.card := Finset.card_union_le _ _
    _ ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
        rw [hTc, ← hUc]; gcongr; exact Finset.card_image_le

open IsLocalRing TensorProduct in
/- English proof (translation)
Set `P : PrimeSpectrum A` to `⟨I, inferInstance⟩`. Establish `h1 : I.height = Order.height P` using `PrimeSpectrum.height_eq_orderHeight P`. Establish `h2 : ringKrullDim (A ⧸ I) = (Order.coheight P : WithBot ℕ∞)`. Rewrite using `[ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]`. Both sides reduce to the same expression.

Establish `: Nonempty (PrimeSpectrum A)` using `⟨P⟩`. Rewrite using `[h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]`. Use `norm_cast`. Conclude with `le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) P`.
-/
private lemma height_add_ringKrullDim_quotient_le' (A : Type) [CommRing A] (I : Ideal A)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (A ⧸ I) ≤ ringKrullDim A := by
  let P : PrimeSpectrum A := ⟨I, inferInstance⟩
  have h1 : I.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  have h2 : ringKrullDim (A ⧸ I) = (Order.coheight P : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  have : Nonempty (PrimeSpectrum A) := ⟨P⟩
  rw [h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  norm_cast
  exact le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) P

open IsLocalRing TensorProduct in

/- English proof (translation)
Establish `hmfg : (maximalIdeal (Localization.AtPrime p)).FG` using `IsNoetherian.noetherian _`. Take `⟨U, hUc, hU⟩` from `Submodule.FG.exists_span_finset_card_eq_spanFinrank hmfg`. Use `choose f hf using fun u : Localization.AtPrime p => IsLocalization.surj p.primeCompl u`. Set `T : Finset B` to `U.image fun u => (f u).1`. Establish `hTp : ∀ t ∈ T, t ∈ p`.

Introduce `t ht`. Take `⟨u, hu, rfl⟩` from `Finset.mem_image.mp ht`. Rewrite using `[← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hf u]`. Conclude with `Ideal.mul_mem_right _ _ (hU ▸ Ideal.subset_span hu)`. Establish `hTspan : p.map (algebraMap B (Localization.AtPrime p)) = Ideal.span (algebraMap B (Localization.AtPrime p) '' T)`.

Rewrite using `[Localization.AtPrime.map_eq_maximalIdeal]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[← hU]`. Express the relevant statement in the definitionally equal form `Ideal.span _ ≤ _`. Rewrite using `[Ideal.span_le]`.

Introduce `u hu`. Establish `hunit` using `IsLocalization.map_units (Localization.AtPrime p) (f u).2`. Establish `e : u = algebraMap B _ (f u).1 * ↑hunit.unit⁻¹`. Rewrite using `[Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]`. Conclude with `hf u`.

Rewrite using `[e]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(f u).1, Finset.mem_image_of_mem _ hu, rfl⟩)`. Rewrite using `[Ideal.span_le]`. Introduce and unpack `_ ⟨t, ht, rfl⟩`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`.

Conclude with `Ideal.mem_map_of_mem _ (hTp t ht)`. Take `⟨V, hV⟩` from `(IsNoetherian.noetherian p : p.FG)`. Establish `hc : ∀ v ∈ V, ∃ c ∈ p.primeCompl, c * v ∈ Ideal.span (T : Set B)`. Introduce `v hv`. Rewrite using `[← IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p), Ideal.map_span, ← hTspan]`.

Conclude with `Ideal.mem_map_of_mem _ (hV ▸ Ideal.subset_span hv)`. Use `choose! c hcp hcT using hc`. Establish `hg : ∀ x ∈ p, (∏ v ∈ V, c v) * x ∈ Ideal.span (T : Set B)`. Establish `: Ideal.span {∏ v ∈ V, c v} * p ≤ Ideal.span (T : Set B)`. Rewrite using `[← hV, Ideal.span_mul_span', Ideal.span_le]`.

Introduce and unpack `_ ⟨a, ha, v, hv, rfl⟩`. Rewrite using `[Set.mem_singleton_iff.mp ha, ← Finset.prod_erase_mul V c hv]`. Express the relevant statement in the definitionally equal form `(∏ x ∈ V.erase v, c x) * c v * v ∈ Ideal.span (T : Set B)`. Rewrite using `[mul_assoc]`. Conclude with `Ideal.mul_mem_left _ _ (hcT v hv)`.

Conclude with `Ideal.span_singleton_mul_le_iff.mp this`. Use `⟨∏ v ∈ V, c v, p.primeCompl.prod_mem fun v hv => hcp v hv, ?_⟩` and prove the remaining obligations. Introduce `q _ hpq hgq hreg`. Establish `hdisj : Disjoint (q.primeCompl : Set B) p` using `Set.disjoint_left.mpr fun x hxq hxp => hxq (hpq hxp)`. Establish `hI : p.map (algebraMap B (Localization.AtPrime q)) = Ideal.span (algebraMap B (Localization.AtPrime q) '' T)`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `hu : IsUnit (algebraMap B (Localization.AtPrime q) (∏ v ∈ V, c v))` using `IsLocalization.map_units (Localization.AtPrime q) (⟨_, hgq⟩ : q.primeCompl)`. Establish `h2 : algebraMap B (Localization.AtPrime q) ((∏ v ∈ V, c v) * x) ∈ Ideal.span (algebraMap B (Localization.AtPrime q) '' T)`.

Rewrite using `[← Ideal.map_span]`. Conclude with `Ideal.mem_map_of_mem _ (hg x hx)`. Rewrite `h2` using `[map_mul]`. Conclude with `(Ideal.unit_mul_mem_iff_mem _ hu).mp h2`. Rewrite using `[← Ideal.map_span]`.

Conclude with `Ideal.map_mono (Ideal.span_le.mpr fun t ht => hTp t ht)`. Establish `hIprime : (p.map (algebraMap B (Localization.AtPrime q))).IsPrime` using `IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj`. Establish `hIcard : (p.map (algebraMap B (Localization.AtPrime q))).spanFinrank ≤ T.card`. Rewrite using `[hI, ← Finset.coe_image]`. Conclude with `(_root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _).trans Finset.card_image_le`.

Establish `hTcard : (T.card : WithBot ℕ∞) ≤ (p.map (algebraMap B (Localization.AtPrime q))).height`. Establish `h1 : (p.map (algebraMap B (Localization.AtPrime q))).height = p.height`. Rewrite using `[← IsLocalization.height_under q.primeCompl, IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹_› hdisj]`. Establish `h2 : (p.height : WithBot ℕ∞) = (maximalIdeal (Localization.AtPrime p)).spanFinrank`. Rewrite using `[← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp.spanFinrank_maximalIdeal]`.

Rewrite using `[h1, h2]`. Conclude with `(Finset.card_image_le.trans hUc.le)` after adjusting the coercions. Use `hreg.toIsLocalRing` as an intermediate fact. Establish `hA` using `spanFinrank_maximalIdeal_le_add (Localization.AtPrime q) (p.map (algebraMap B (Localization.AtPrime q))) (IsNoetherian.noetherian _) (IsNoetherian.noetherian _)`. Establish `hd` using `hreg.spanFinrank_maximalIdeal`.

Establish `hdim` using `height_add_ringKrullDim_quotient_le' (Localization.AtPrime q) (p.map (algebraMap B (Localization.AtPrime q)))`. Apply `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Conclude with `hA.trans (by omega)` after adjusting the coercions. Use `_ = (T.card : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by push_cast; rw [hd]`.

Use `_ ≤ (p.map (algebraMap B (Localization.AtPrime q))).height + ringKrullDim (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by gcongr`. Use `_ ≤ ringKrullDim (Localization.AtPrime q) := hdim`.
-/
theorem _root_.GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient (B : Type) [CommRing B]
    [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
      IsRegularLocalRing
        (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  have hmfg : (maximalIdeal (Localization.AtPrime p)).FG := IsNoetherian.noetherian _
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hmfg
  choose f hf using fun u : Localization.AtPrime p => IsLocalization.surj p.primeCompl u
  let T : Finset B := U.image fun u => (f u).1
  have hTp : ∀ t ∈ T, t ∈ p := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hf u]
    exact Ideal.mul_mem_right _ _ (hU ▸ Ideal.subset_span hu)
  have hTspan : p.map (algebraMap B (Localization.AtPrime p)) =
      Ideal.span (algebraMap B (Localization.AtPrime p) '' T) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [← hU]
      change Ideal.span _ ≤ _
      rw [Ideal.span_le]
      intro u hu
      have hunit := IsLocalization.map_units (Localization.AtPrime p) (f u).2
      have e : u = algebraMap B _ (f u).1 * ↑hunit.unit⁻¹ := by
        rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]; exact hf u
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(f u).1, Finset.mem_image_of_mem _ hu, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (hTp t ht)
  obtain ⟨V, hV⟩ := (IsNoetherian.noetherian p : p.FG)
  have hc : ∀ v ∈ V, ∃ c ∈ p.primeCompl, c * v ∈ Ideal.span (T : Set B) := by
    intro v hv
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p),
      Ideal.map_span, ← hTspan]
    exact Ideal.mem_map_of_mem _ (hV ▸ Ideal.subset_span hv)
  choose! c hcp hcT using hc
  have hg : ∀ x ∈ p, (∏ v ∈ V, c v) * x ∈ Ideal.span (T : Set B) := by
    have : Ideal.span {∏ v ∈ V, c v} * p ≤ Ideal.span (T : Set B) := by
      rw [← hV, Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, v, hv, rfl⟩
      rw [Set.mem_singleton_iff.mp ha, ← Finset.prod_erase_mul V c hv]
      change (∏ x ∈ V.erase v, c x) * c v * v ∈ Ideal.span (T : Set B)
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ (hcT v hv)
    exact Ideal.span_singleton_mul_le_iff.mp this
  refine ⟨∏ v ∈ V, c v, p.primeCompl.prod_mem fun v hv => hcp v hv, ?_⟩
  intro q _ hpq hgq hreg
  have hdisj : Disjoint (q.primeCompl : Set B) p :=
    Set.disjoint_left.mpr fun x hxq hxp => hxq (hpq hxp)
  have hI : p.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap B (Localization.AtPrime q) (∏ v ∈ V, c v)) :=
        IsLocalization.map_units (Localization.AtPrime q) (⟨_, hgq⟩ : q.primeCompl)
      have h2 : algebraMap B (Localization.AtPrime q) ((∏ v ∈ V, c v) * x) ∈
          Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
        rw [← Ideal.map_span]; exact Ideal.mem_map_of_mem _ (hg x hx)
      rw [map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [← Ideal.map_span]
      exact Ideal.map_mono (Ideal.span_le.mpr fun t ht => hTp t ht)
  have hIprime : (p.map (algebraMap B (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have hIcard : (p.map (algebraMap B (Localization.AtPrime q))).spanFinrank ≤ T.card := by
    rw [hI, ← Finset.coe_image]
    exact (_root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _).trans Finset.card_image_le
  have hTcard : (T.card : WithBot ℕ∞) ≤ (p.map (algebraMap B (Localization.AtPrime q))).height := by
    have h1 : (p.map (algebraMap B (Localization.AtPrime q))).height = p.height := by
      rw [← IsLocalization.height_under q.primeCompl,
        IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹_› hdisj]
    have h2 : (p.height : WithBot ℕ∞) = (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
        hp.spanFinrank_maximalIdeal]
    rw [h1, h2]
    exact_mod_cast (Finset.card_image_le.trans hUc.le)
  have := hreg.toIsLocalRing
  have hA := spanFinrank_maximalIdeal_le_add (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q))) (IsNoetherian.noetherian _)
    (IsNoetherian.noetherian _)
  have hd := hreg.spanFinrank_maximalIdeal
  have hdim := height_add_ringKrullDim_quotient_le' (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q)))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((T.card + (maximalIdeal (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q)))).spanFinrank : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hA.trans (by omega)
    _ = (T.card : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
        push_cast; rw [hd]
    _ ≤ (p.map (algebraMap B (Localization.AtPrime q))).height + ringKrullDim
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
        gcongr
    _ ≤ ringKrullDim (Localization.AtPrime q) := hdim

end GlobalTheory.RegularAscent
