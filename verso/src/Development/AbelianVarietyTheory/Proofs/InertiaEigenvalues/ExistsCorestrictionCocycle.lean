import Mathlib

namespace GlobalTheory

open scoped BigOperators

/- English proof (translation)
Establish `h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)`. Rewrite using `[QuotientGroup.out_eq']`. Use `conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Use `QuotientGroup.eq.mp h` as an intermediate fact.

Simplify `this` using `[mul_assoc]`.
-/
theorem corCoc_mem {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    (g • q).out⁻¹ * g * q.out ∈ H := by
  have h : (QuotientGroup.mk (g • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out) := by
    rw [QuotientGroup.out_eq']
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  have := QuotientGroup.eq.mp h
  simpa [mul_assoc] using this

/- English proof (translation)
Introduce `R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc`. Use `haveI : Fintype (G ⧸ H) := Fintype.ofFinite _`. Establish `hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x`. Introduce `a b x`. Rewrite using `[map_mul]`.

Both sides reduce to the same expression. Use `⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)), ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `continuous_finset_sum _ fun q _ => ?_` and prove the remaining obligations. Rewrite using `[continuous_iff_continuousAt]`. Introduce `g₀`.

Establish `hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out` using `by fun_prop`. Establish `hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H` using `hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))`. Establish `h1 : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀`. Use `(hρ _).continuousAt.comp ?_` and prove the remaining obligations. Conclude with `ContinuousAt.comp (g := f) (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q))) hk.continuousAt`.

Use `h1.congr ?_` and prove the remaining obligations. Use `filter_upwards [hn] with g hg`. Establish `: g • q = g₀ • q` using `by conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)] conv_lhs => rw [← QuotientGroup.out_eq' q]`. Use `symm`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)`.

Conclude with `QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)`. Rewrite using `[this]`. Introduce `g h`. Simplify using `only [map_sum]`. Rewrite using `[← Equiv.sum_comp (MulAction.toPerm h) (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Simplify using `only [MulAction.toPerm_apply, mul_smul]`. Establish `e : (g • h • q).out⁻¹ * (g * h) * q.out = ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out)` using `by group`. Rewrite using `[e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add, hmul, hmul]`. Use `congr 3`.

Use `group`. Use `⟨0, fun h hh => ?_⟩` and prove the remaining obligations. Rewrite using `[finsum_eq_sum_of_fintype]`. Simplify using `only [map_zero, sub_zero, add_zero]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Establish `: h • q = q` using `by conv_rhs => rw [← QuotientGroup.out_eq' q] conv_lhs => rw [← QuotientGroup.out_eq' q]`. Use `symm`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)`. Use `QuotientGroup.eq.mpr ?_` and prove the remaining obligations. Use `Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Rewrite using `[this]`. Introduce `Y hY f₀ x h₀ hx`. Use `⟨∑ q : G ⧸ H, (f₀ q.out + ρ q.out x), fun g => ?_⟩` and prove the remaining obligations. Establish `hidx : H.index • f₀ g = ∑ _q : G ⧸ H, f₀ g`.

Rewrite using `[Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]`. Establish `hre : ∑ q : G ⧸ H, (f₀ q.out + ρ q.out x) = ∑ q : G ⧸ H, (f₀ (g • q).out + ρ (g • q).out x)` using `(Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f₀ q.out + ρ q.out x)).symm`. Rewrite using `[hidx, map_sum, hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]`. Use `Y.sum_mem fun q _ => ?_` and prove the remaining obligations. Use `set s' := (g • q).out`.

Use `set s := q.out`. Establish `e : s' * (s'⁻¹ * g * s) = g * s` using `by group`. Establish `a1` using `hY s' _ (hx _ (corCoc_mem H g q))`. Establish `a2` using `h₀ s' (s'⁻¹ * g * s)`. Establish `a3` using `h₀ g s`.

Rewrite `a2` using `[e]`. Express the relevant statement in the definitionally equal form `ρ s' (f (s'⁻¹ * g * s) - f₀ (s'⁻¹ * g * s) - (ρ (s'⁻¹ * g * s) x - x)) ∈ Y at a1`. Rewrite `a1` using `[map_sub, map_sub, map_sub, hmul, e]`. Use `Y.add_mem (Y.sub_mem a1 a2) a3` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Rewrite using `[map_add, hmul]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_corestriction_cocycle : ∀ (R G X : Type) [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup X] [Module R X] [TopologicalSpace X] [IsTopologicalAddGroup X] (ρ : Representation R G X) (H : Subgroup G) [H.Normal] [H.FiniteIndex], IsOpen (H : Set G) → (∀ g, Continuous (ρ g)) → (∀ x, Continuous fun g => ρ g x) → ∀ f : G → X, ContinuousOn f H → (∀ g ∈ H, ∀ h ∈ H, f (g * h) = f g + ρ g (f h)) → ∃ F : G → X, Continuous F ∧ (∀ g h, F (g * h) = F g + ρ g (F h)) ∧ (∃ x, ∀ h ∈ H, F h = (∑ᶠ q : G ⧸ H, ρ q.out (f (q.out⁻¹ * h * q.out))) + (ρ h x - x)) ∧ ∀ (Y : Submodule R X), (∀ g, ∀ y ∈ Y, ρ g y ∈ Y) → ∀ (f₀ : G → X) (x : X), (∀ g h, f₀ (g * h) - (f₀ g + ρ g (f₀ h)) ∈ Y) → (∀ h ∈ H, f h - f₀ h - (ρ h x - x) ∈ Y) → ∃ x', ∀ g, F g - H.index • f₀ g - (ρ g x' - x') ∈ Y := by
  intro R G X _ _ _ _ _ _ _ _ ρ H _ _ hH hρ _ f hf hc
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hmul : ∀ (a b : G) (x : X), ρ a (ρ b x) = ρ (a * b) x := by
    intro a b x
    rw [map_mul]; rfl
  refine ⟨fun g => ∑ q : G ⧸ H, ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out)), ?_, ?_, ?_, ?_⟩
  · refine continuous_finset_sum _ fun q _ => ?_
    rw [continuous_iff_continuousAt]
    intro g₀
    have hk : Continuous fun g : G => (g₀ • q).out⁻¹ * g * q.out := by fun_prop
    have hn : ∀ᶠ g in nhds g₀, (g₀ • q).out⁻¹ * g * q.out ∈ H :=
      hk.continuousAt.preimage_mem_nhds (hH.mem_nhds (corCoc_mem H g₀ q))
    have h1 : ContinuousAt (fun g => ρ (g₀ • q).out (f ((g₀ • q).out⁻¹ * g * q.out))) g₀ := by
      refine (hρ _).continuousAt.comp ?_
      exact ContinuousAt.comp (g := f) (hf.continuousAt (hH.mem_nhds (corCoc_mem H g₀ q)))
        hk.continuousAt
    refine h1.congr ?_
    filter_upwards [hn] with g hg
    have : g • q = g₀ • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' (g₀ • q)]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk (g₀ • q).out : G ⧸ H) = QuotientGroup.mk (g * q.out)
      exact QuotientGroup.eq.mpr (by simpa [mul_assoc] using hg)
    rw [this]
  · intro g h
    simp only [map_sum]
    rw [← Equiv.sum_comp (MulAction.toPerm h)
      (fun q : G ⧸ H => ρ (g • q).out (f ((g • q).out⁻¹ * g * q.out))), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [MulAction.toPerm_apply, mul_smul]
    have e : (g • h • q).out⁻¹ * (g * h) * q.out =
        ((g • h • q).out⁻¹ * g * (h • q).out) * ((h • q).out⁻¹ * h * q.out) := by group
    rw [e, hc _ (corCoc_mem H g (h • q)) _ (corCoc_mem H h q), map_add, hmul, hmul]
    congr 3
    group
  · refine ⟨0, fun h hh => ?_⟩
    rw [finsum_eq_sum_of_fintype]
    simp only [map_zero, sub_zero, add_zero]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : h • q = q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      symm
      change (QuotientGroup.mk q.out : G ⧸ H) = QuotientGroup.mk (h * q.out)
      refine QuotientGroup.eq.mpr ?_
      have := Subgroup.Normal.conj_mem' ‹H.Normal› h hh q.out
      simpa [mul_assoc] using this
    rw [this]
  · intro Y hY f₀ x h₀ hx
    refine ⟨∑ q : G ⧸ H, (f₀ q.out + ρ q.out x), fun g => ?_⟩
    have hidx : H.index • f₀ g = ∑ _q : G ⧸ H, f₀ g := by
      rw [Finset.sum_const, Finset.card_univ, Subgroup.index, Nat.card_eq_fintype_card]
    have hre : ∑ q : G ⧸ H, (f₀ q.out + ρ q.out x) =
        ∑ q : G ⧸ H, (f₀ (g • q).out + ρ (g • q).out x) :=
      (Equiv.sum_comp (MulAction.toPerm g) (fun q : G ⧸ H => f₀ q.out + ρ q.out x)).symm
    rw [hidx, map_sum, hre, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib]
    refine Y.sum_mem fun q _ => ?_
    set s' := (g • q).out
    set s := q.out
    have e : s' * (s'⁻¹ * g * s) = g * s := by group
    have a1 := hY s' _ (hx _ (corCoc_mem H g q))
    have a2 := h₀ s' (s'⁻¹ * g * s)
    have a3 := h₀ g s
    rw [e] at a2
    change ρ s' (f (s'⁻¹ * g * s) - f₀ (s'⁻¹ * g * s) - (ρ (s'⁻¹ * g * s) x - x)) ∈ Y at a1
    rw [map_sub, map_sub, map_sub, hmul, e] at a1
    have := Y.add_mem (Y.sub_mem a1 a2) a3
    convert this using 1
    rw [map_add, hmul]
    abel

end GlobalTheory
