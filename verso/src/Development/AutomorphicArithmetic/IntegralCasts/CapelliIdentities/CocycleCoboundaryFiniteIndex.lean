import Mathlib

/- English proof (translation)
Introduce `R Q M _ _ _ _ π H f hf hH hu hn`. Use `haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn`. Establish `hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b`. Introduce `a b hab`. Establish `hmem : a⁻¹ * b ∈ H` using `QuotientGroup.eq.mp hab`.

Establish `h1` using `hf a (a⁻¹ * b)`. Rewrite `h1` using `[mul_inv_cancel_left, hH _ hmem, map_zero, add_zero]`. Conclude with `h1.symm`. Set `F : Q ⧸ H → M` to `fun x => f x.out`. Establish `hF : ∀ a : Q, F (a : Q ⧸ H) = f a` using `fun a => hconst _ _ (QuotientGroup.out_eq' _)`.

Establish `hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + π g (F x)`. Introduce `g x`. Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H a`. Establish `h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H)` using `rfl`.

Rewrite using `[h2, hF, hF, hf]`. Establish `hcard : Fintype.card (Q ⧸ H) = H.index`. Rewrite using `[Subgroup.index_eq_card, Nat.card_eq_fintype_card]`. Establish `hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + π g (∑ x, F x)`. Introduce `g`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum, Nat.cast_smul_eq_nsmul]`. Take `⟨c, hc⟩` from `hu.exists_left_inv`. Use `⟨-(c • ∑ x, F x), fun g => ?_⟩` and prove the remaining obligations. Establish `h3 : (H.index : R) • f g = ∑ x, F x - π g (∑ x, F x)` using `eq_sub_of_add_eq (hsum g).symm`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h3, map_neg, map_smul, smul_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.Reformulated.B.CocycleCoboundaryFiniteIndex.coboundary_of_vanishing_on_finite_index :
    ∀ {R Q M : Type} [inst : CommRing R] [inst_1 : Group Q]
    [inst_2 : AddCommGroup M] [inst_3 : _root_.Module R M] (π : Representation R Q M) (H : Subgroup Q) (f : Q → M),
    (∀ (g h : Q), f (g * h) = f g + ((π : Q → M →ₗ[R] M) g : M → M) (f h)) →
      (∀ u ∈ H, f u = (0 : M)) →
        IsUnit (↑H.index : R) →
          H.index ≠ (0 : ℕ) → ∃ (m : M), ∀ (g : Q), f g = ((π : Q → M →ₗ[R] M) g : M → M) m - m := by
  intro R Q M _ _ _ _ π H f hf hH hu hn
  classical
  haveI : Fintype (Q ⧸ H) := Subgroup.fintypeOfIndexNeZero hn
  have hconst : ∀ a b : Q, (a : Q ⧸ H) = (b : Q ⧸ H) → f a = f b := by
    intro a b hab
    have hmem : a⁻¹ * b ∈ H := QuotientGroup.eq.mp hab
    have h1 := hf a (a⁻¹ * b)
    rw [mul_inv_cancel_left, hH _ hmem, map_zero, add_zero] at h1
    exact h1.symm
  let F : Q ⧸ H → M := fun x => f x.out
  have hF : ∀ a : Q, F (a : Q ⧸ H) = f a := fun a =>
    hconst _ _ (QuotientGroup.out_eq' _)
  have hstep : ∀ (g : Q) (x : Q ⧸ H), F (g • x) = f g + π g (F x) := by
    intro g x
    induction x using QuotientGroup.induction_on with
    | H a =>
      have h2 : g • (a : Q ⧸ H) = ((g * a : Q) : Q ⧸ H) := rfl
      rw [h2, hF, hF, hf]
  have hcard : Fintype.card (Q ⧸ H) = H.index := by
    rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  have hsum : ∀ g : Q, ∑ x, F x = (H.index : R) • f g + π g (∑ x, F x) := by
    intro g
    calc ∑ x, F x = ∑ x, F (g • x) := (Equiv.sum_comp (MulAction.toPerm g) F).symm
      _ = ∑ x : Q ⧸ H, (f g + π g (F x)) := Finset.sum_congr rfl fun x _ => hstep g x
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard, map_sum,
          Nat.cast_smul_eq_nsmul]
  obtain ⟨c, hc⟩ := hu.exists_left_inv
  refine ⟨-(c • ∑ x, F x), fun g => ?_⟩
  have h3 : (H.index : R) • f g = ∑ x, F x - π g (∑ x, F x) := eq_sub_of_add_eq (hsum g).symm
  calc f g = c • ((H.index : R) • f g) := by rw [smul_smul, hc, one_smul]
    _ = _ := by
      rw [h3, map_neg, map_smul, smul_sub]
      abel
