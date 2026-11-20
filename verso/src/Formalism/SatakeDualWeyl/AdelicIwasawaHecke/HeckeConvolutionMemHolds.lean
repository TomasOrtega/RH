import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FiniteCosetsInDoset

noncomputable section

namespace Formalism.UG.P

open Formalism.UG

variable {G : Type} [Group G]

/- English proof (translation)
Unfold `conv`. Use `congr 1`. Use function extensionality and compare the values at `x`. Establish `h` using `hf₂ 1 b (x.out⁻¹ * g)`. Simplify using `only [OneMemClass.coe_one, one_mul] at h`.

Rewrite using `[← mul_assoc, h]`.
-/
theorem conv_mul_right {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₂ : IsBiInv K f₂) (g : G) (b : K) : conv K f₁ f₂ (g * b) = conv K f₁ f₂ g := by
  unfold conv
  congr 1
  funext x
  have h := hf₂ 1 b (x.out⁻¹ * g)
  simp only [OneMemClass.coe_one, one_mul] at h
  rw [← mul_assoc, h]

/- English proof (translation)
Establish `key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c`. Introduce `y`. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K)` using `by conv_lhs => rw [← QuotientGroup.out_eq' y]`.

Both sides reduce to the same expression. Rewrite using `[e, hc]`. Unfold `conv`. Use `(finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_` and prove the remaining obligations. Use `congr 1`.

Use function extensionality and compare the values at `y`. Take `⟨c, hc⟩` from `key y`. Simplify using `only [MulAction.toPerm_apply]`. Rewrite using `[hc, hf₁ a c y.out]`. Establish `e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G)`.

Simplify using `only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]`. Use `group`. Rewrite using `[e2, hf₂]`.
-/
theorem conv_mul_left {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) (a : K) (g : G) :
    conv K f₁ f₂ ((a : G) * g) = conv K f₁ f₂ g := by
  have key : ∀ y : G ⧸ K, ∃ c : K, ((a : G) • y).out = (a : G) * y.out * c := by
    intro y
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * y.out)
    refine ⟨c, ?_⟩
    have e : (a : G) • y = (QuotientGroup.mk ((a : G) * y.out) : G ⧸ K) := by
      conv_lhs => rw [← QuotientGroup.out_eq' y]
      rfl
    rw [e, hc]
  unfold conv
  refine (finsum_comp_equiv (MulAction.toPerm (a : G) : Equiv.Perm (G ⧸ K))).symm.trans ?_
  congr 1
  funext y
  obtain ⟨c, hc⟩ := key y
  simp only [MulAction.toPerm_apply]
  rw [hc, hf₁ a c y.out]
  have e2 : ((a : G) * y.out * c)⁻¹ * ((a : G) * g) = ((c⁻¹ : K) : G) * (y.out⁻¹ * g) * ((1 : K) : G) := by
    simp only [InvMemClass.coe_inv, OneMemClass.coe_one, mul_one]
    group
  rw [e2, hf₂]

/- English proof (translation)
Introduce `a b g`. Rewrite using `[conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]`.
-/
theorem conv_biInv {k : Type} [CommRing k] (K : Subgroup G) (f₁ f₂ : G → k)
    (hf₁ : IsBiInv K f₁) (hf₂ : IsBiInv K f₂) : IsBiInv K (conv K f₁ f₂) := by
  intro a b g
  rw [conv_mul_right K f₁ f₂ hf₂ ((a : G) * g) b, conv_mul_left K f₁ f₂ hf₁ hf₂ a g]

/- English proof (translation)
Establish `hX` using `finite_support_cosets hK hs₁`. Take `⟨S₂, hS₂⟩` from `hs₂`. Use `set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0}, ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef`. Establish `hT : T.Finite` using `S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ => (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _`. Use `⟨hT.toFinset, fun g hg => ?_⟩` and prove the remaining obligations.

Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hg (finsum_eq_zero_of_forall_eq_zero h)`. Establish `h1 : f₁ x.out ≠ 0` using `left_ne_zero_of_mul hx`.

Establish `h2 : f₂ (x.out⁻¹ * g) ≠ 0` using `right_ne_zero_of_mul hx`. Take `⟨t, ht, a, b, hab⟩` from `hS₂ _ h2`. Take `⟨c, hc⟩` from `QuotientGroup.mk_out_eq_mul K ((a : G) * t)`. Use `⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩` and prove the remaining obligations. Rewrite using `[Set.Finite.mem_toFinset, hTdef]`.

Simplify using `only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]`. Conclude with `⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩`. Rewrite using `[hc]`. Establish `e : g = x.out * (x.out⁻¹ * g)` using `by group`. Rewrite using `[e, hab]`.

Simplify using `only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]`. Use `group`.
-/
theorem conv_finDosetSupp {k : Type} [CommRing k] {K : Subgroup G} (hK : IsCommensurated K)
    (f₁ f₂ : G → k) (hs₁ : FinDosetSupp K f₁) (hs₂ : FinDosetSupp K f₂) :
    FinDosetSupp K (conv K f₁ f₂) := by
  classical
  have hX := finite_support_cosets hK hs₁
  obtain ⟨S₂, hS₂⟩ := hs₂
  set T : Set G := ⋃ t ∈ (S₂ : Set G), ⋃ x ∈ {x : G ⧸ K | f₁ x.out ≠ 0},
    ⋃ y ∈ {y : G ⧸ K | ∃ a b : K, y.out = (a : G) * t * b}, {x.out * y.out} with hTdef
  have hT : T.Finite :=
    S₂.finite_toSet.biUnion fun t _ => hX.biUnion fun x _ =>
      (finite_cosets_in_doset hK t).biUnion fun y _ => Set.finite_singleton _
  refine ⟨hT.toFinset, fun g hg => ?_⟩
  obtain ⟨x, hx⟩ : ∃ x : G ⧸ K, f₁ x.out * f₂ (x.out⁻¹ * g) ≠ 0 := by
    by_contra h
    push_neg at h
    exact hg (finsum_eq_zero_of_forall_eq_zero h)
  have h1 : f₁ x.out ≠ 0 := left_ne_zero_of_mul hx
  have h2 : f₂ (x.out⁻¹ * g) ≠ 0 := right_ne_zero_of_mul hx
  obtain ⟨t, ht, a, b, hab⟩ := hS₂ _ h2
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K ((a : G) * t)
  refine ⟨x.out * (QuotientGroup.mk ((a : G) * t) : G ⧸ K).out, ?_, 1, c⁻¹ * b, ?_⟩
  · rw [Set.Finite.mem_toFinset, hTdef]
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_setOf_eq]
    exact ⟨t, ht, x, h1, _, ⟨a, c, hc⟩, rfl⟩
  · rw [hc]
    have e : g = x.out * (x.out⁻¹ * g) := by group
    rw [e, hab]
    simp only [OneMemClass.coe_one, one_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
    group

/- English proof (translation)
Introduce `G _ K k _ hK f₁ hf₁ f₂ hf₂`. Establish `h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁` using `hf₁`. Establish `h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂` using `hf₂`. Use `show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)`. Conclude with `⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩`.
-/
theorem hecke_convolution_mem_holds : Formalism.UG.HeckeConvMem := by
  intro G _ K k _ hK f₁ hf₁ f₂ hf₂
  have h1 : IsBiInv K f₁ ∧ FinDosetSupp K f₁ := hf₁
  have h2 : IsBiInv K f₂ ∧ FinDosetSupp K f₂ := hf₂
  show IsBiInv K (conv K f₁ f₂) ∧ FinDosetSupp K (conv K f₁ f₂)
  exact ⟨conv_biInv K f₁ f₂ h1.1 h2.1, conv_finDosetSupp hK f₁ f₂ h1.2 h2.2⟩

/- English proof (translation)
Introduce `G _ K k _ hK a b g`. Use `set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧ x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef`. Establish `hfin : S.Finite`. Use `(finite_cosets_in_doset hK a).subset fun x hx => ?_` and prove the remaining obligations. Take `⟨h, hh, c, hc, e⟩` from `DoubleCoset.mem_doubleCoset.1 hx.1`.

Conclude with `⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩`. Establish `hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = if x ∈ S then 1 else 0`. Introduce `x`. Simplify using `only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]`. Apply the tactic sequence `split_ifs <;> simp_all`.

Use `show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _`. Rewrite using `[finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]`. Rewrite using `[Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]`. Simplify using `[Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]`. Introduce `x hx`.

Rewrite `hx` using `[Function.mem_support]`. Rewrite using `[Set.Finite.coe_toFinset]`. Assume the negation of the conclusion as `h`. Conclude with `hx (if_neg h)`.
-/
theorem convolution_count_holds : Formalism.UG.ConvCount := by
  classical
  intro G _ K k _ hK a b g
  set S : Set (G ⧸ K) := {x : G ⧸ K | x.out ∈ DoubleCoset.doubleCoset a (K : Set G) K ∧
    x.out⁻¹ * g ∈ DoubleCoset.doubleCoset b (K : Set G) K} with hSdef
  have hfin : S.Finite := by
    refine (finite_cosets_in_doset hK a).subset fun x hx => ?_
    obtain ⟨h, hh, c, hc, e⟩ := DoubleCoset.mem_doubleCoset.1 hx.1
    exact ⟨⟨h, hh⟩, ⟨c, hc⟩, e⟩
  have hterm : ∀ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) =
      if x ∈ S then 1 else 0 := by
    intro x
    simp only [dosetInd, Set.indicator_apply, Pi.one_apply, hSdef, Set.mem_setOf_eq]
    split_ifs <;> simp_all
  show ∑ᶠ x : G ⧸ K, dosetInd k K a x.out * dosetInd k K b (x.out⁻¹ * g) = _
  rw [finsum_congr hterm, finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) ?_]
  · rw [Finset.sum_congr rfl (fun x hx => if_pos (hfin.mem_toFinset.1 hx))]
    simp [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hfin]
  · intro x hx
    rw [Function.mem_support] at hx
    rw [Set.Finite.coe_toFinset]
    by_contra h
    exact hx (if_neg h)

end Formalism.UG.P
