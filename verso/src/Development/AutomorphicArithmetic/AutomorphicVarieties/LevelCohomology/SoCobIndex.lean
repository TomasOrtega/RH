import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X

/- English proof (translation)
Introduce `O Γ _ _ _ _ θ z hz U D hUD hcob`. Take `⟨a, ha, m, hm⟩` from `hcob`. Use `haveI : (U.subgroupOf D).FiniteIndex := ⟨hUD⟩`. Use `haveI : Fintype (D ⧸ U.subgroupOf D) := Fintype.ofFinite _`. Set `T : D ⧸ U.subgroupOf D → O` to `fun q => a * z ((q.out : D) : Γ) - (θ ((q.out : D) : Γ) : O) * m`.

Establish `key : ∀ (g : D) (q : D ⧸ U.subgroupOf D), T (g • q) = a * z (g : Γ) + (θ (g : Γ) : O) * T q`. Introduce `g q`. Establish `e1 : g • q = (QuotientGroup.mk (g * q.out) : D ⧸ U.subgroupOf D)` using `by conv_lhs => rw [← QuotientGroup.out_eq' q]`. Both sides reduce to the same expression. Take `⟨h, hh⟩` from `QuotientGroup.mk_out_eq_mul (U.subgroupOf D) (g * q.out)`.

Establish `hhU : ((h : D) : Γ) ∈ U ⊓ D` using `⟨Subgroup.mem_subgroupOf.1 h.2, (h : D).2⟩`. Establish `hmh` using `hm _ hhU`. Simplify using `only [T]`. Rewrite using `[e1, hh]`. Simplify using `only [Subgroup.coe_mul, map_mul, Units.val_mul]`.

Rewrite using `[hz, hz]`. Simplify using `only [map_mul, Units.val_mul]`. Take the linear combination `(θ (g : Γ) : O) * (θ ((q.out : D) : Γ) : O) * hmh`. Establish `hn : (Fintype.card (D ⧸ U.subgroupOf D) : O) ≠ 0`. Rewrite using `[Nat.cast_ne_zero]`.

Conclude with `Fintype.card_ne_zero`. Use `⟨(Fintype.card (D ⧸ U.subgroupOf D) : O) * a, mul_ne_zero hn ha, -(∑ q, T q), ?_⟩` and prove the remaining obligations. Introduce `g hg`. Establish `hs : ∑ q, T ((MulAction.toPerm (⟨g, hg⟩ : D)) q) = ∑ q, T q` using `Equiv.sum_comp _ T`. Simplify using `only [MulAction.toPerm_apply, key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs`.

Take the linear combination `hs`.
-/
theorem UpperTheory.V.X.So.cobIndex :
    ∀ (O Γ : Type) [CommRing O] [IsDomain O] [CharZero O] [Group Γ] (θ : Γ →* Oˣ) (z : Γ → O), Coc θ z → ∀ U D : Subgroup Γ, U.relIndex D ≠ 0 → CobOn θ z (U ⊓ D) → CobOn θ z D := by
  intro O Γ _ _ _ _ θ z hz U D hUD hcob
  obtain ⟨a, ha, m, hm⟩ := hcob
  haveI : (U.subgroupOf D).FiniteIndex := ⟨hUD⟩
  haveI : Fintype (D ⧸ U.subgroupOf D) := Fintype.ofFinite _
  let T : D ⧸ U.subgroupOf D → O := fun q => a * z ((q.out : D) : Γ) - (θ ((q.out : D) : Γ) : O) * m
  have key : ∀ (g : D) (q : D ⧸ U.subgroupOf D), T (g • q) = a * z (g : Γ) + (θ (g : Γ) : O) * T q := by
    intro g q
    have e1 : g • q = (QuotientGroup.mk (g * q.out) : D ⧸ U.subgroupOf D) := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf D) (g * q.out)
    have hhU : ((h : D) : Γ) ∈ U ⊓ D := ⟨Subgroup.mem_subgroupOf.1 h.2, (h : D).2⟩
    have hmh := hm _ hhU
    simp only [T]
    rw [e1, hh]
    simp only [Subgroup.coe_mul, map_mul, Units.val_mul]
    rw [hz, hz]
    simp only [map_mul, Units.val_mul]
    linear_combination (θ (g : Γ) : O) * (θ ((q.out : D) : Γ) : O) * hmh
  have hn : (Fintype.card (D ⧸ U.subgroupOf D) : O) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  refine ⟨(Fintype.card (D ⧸ U.subgroupOf D) : O) * a, mul_ne_zero hn ha, -(∑ q, T q), ?_⟩
  intro g hg
  have hs : ∑ q, T ((MulAction.toPerm (⟨g, hg⟩ : D)) q) = ∑ q, T q := Equiv.sum_comp _ T
  simp only [MulAction.toPerm_apply, key, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hs
  linear_combination hs
