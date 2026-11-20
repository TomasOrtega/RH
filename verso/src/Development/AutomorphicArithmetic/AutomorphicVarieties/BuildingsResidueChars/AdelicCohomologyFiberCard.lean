import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Introduce `G _ U U' h hne y`. Use `set e := Subgroup.quotientEquivProdOfLE h with he`. Establish `key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x`. Introduce `x`. Proceed by induction on `x using QuotientGroup.induction_on with`.

Consider the case `H g => rfl`. Establish `e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U')` using `{ toFun := fun x => (e x.1).2 invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩ left_inv := by`. Introduce and unpack `⟨x, hx⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e.symm (y, (e x).2) = x`.

Rewrite using `[← hx, ← key]`. Conclude with `e.symm_apply_apply x`. Use `right_inv := by`. Introduce `b`. Express the relevant statement in the definitionally equal form `(e (e.symm (y, b))).2 = b`.

Rewrite using `[Equiv.apply_symm_apply] }`. Rewrite using `[Cardinal.mk_congr e1]`. Establish `: Finite (U' ⧸ U.subgroupOf U')` using `Subgroup.index_ne_zero_iff_finite.mp hne`. Rewrite using `[← Nat.cast_card]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.adelic_cohomology_fiber_card :
    UpperTheory.V.Af.CohB.FibCard := by
  intro G _ U U' h hne y
  set e := Subgroup.quotientEquivProdOfLE h with he
  have key : ∀ x : G ⧸ U, (e x).1 = Subgroup.quotientMapOfLE h x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H g => rfl
  have e1 : {x // Subgroup.quotientMapOfLE h x = y} ≃ (U' ⧸ U.subgroupOf U') :=
    { toFun := fun x => (e x.1).2
      invFun := fun b => ⟨e.symm (y, b), by rw [← key, Equiv.apply_symm_apply]⟩
      left_inv := by
        rintro ⟨x, hx⟩
        apply Subtype.ext
        change e.symm (y, (e x).2) = x
        rw [← hx, ← key]
        exact e.symm_apply_apply x
      right_inv := by
        intro b
        change (e (e.symm (y, b))).2 = b
        rw [Equiv.apply_symm_apply] }
  rw [Cardinal.mk_congr e1]
  have : Finite (U' ⧸ U.subgroupOf U') := Subgroup.index_ne_zero_iff_finite.mp hne
  rw [← Nat.cast_card]
  rfl
