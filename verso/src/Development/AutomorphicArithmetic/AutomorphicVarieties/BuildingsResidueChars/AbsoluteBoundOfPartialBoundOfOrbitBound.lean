import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

open UpperTheory.V.Af.CohB in
/- English proof (translation)
Introduce `hP hO Γ Y _ _ hT hB`. Take `⟨T, hT⟩` from `hT`. Use `choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)`. Use `⟨∑ t, cf t, ?_⟩` and prove the remaining obligations. Introduce `X _ p hp D hD d ξ`.

Set `r : MulAction.orbitRel.Quotient Γ Y → ↥T` to `fun q => ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩`. Set `cl : X → ↥T` to `fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))`. Establish `hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x`. Introduce `γ x`. Simplify using `only [cl, hp]`.

Use `congr 1`. Conclude with `Quotient.sound ⟨γ, rfl⟩`. Use `(hP Γ X ↥T cl hcl d ξ).trans ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]`. Use `Finset.sum_le_sum fun t _ => ?_` and prove the remaining obligations.

Establish `hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1`. Introduce and unpack `⟨x, hx⟩`. Express the relevant statement in the definitionally equal form `cl x = t at hx`. Take `⟨h, hh⟩` from `Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))`. Use `⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩` and prove the remaining obligations.

Rewrite using `[mul_smul]`. Simplify using `only at hh ⊢`. Rewrite using `[hh]`. Conclude with `congrArg Subtype.val hx`. Use `hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D (le_trans (Cardinal.mk_le_of_injective (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1})) (fun a b hab => Subtype.ext (Subtype. …` and prove the remaining obligations.
-/
theorem UpperTheory.absolute_bound_of_partial_bound_of_orbit_bound :
    UpperTheory.V.Af.CohB.PartBound → UpperTheory.V.Af.CohB.OrbBound → UpperTheory.V.Af.CohB.AbsBound := by
  intro hP hO Γ Y _ _ hT hB
  obtain ⟨T, hT⟩ := hT
  choose cf hcf using fun t : ↥T => hO Γ Y t.1 (hB t.1)
  refine ⟨∑ t, cf t, ?_⟩
  intro X _ p hp D hD d ξ
  let r : MulAction.orbitRel.Quotient Γ Y → ↥T := fun q =>
    ⟨Classical.choose (hT q.out) • q.out, Classical.choose_spec (hT q.out)⟩
  let cl : X → ↥T := fun x => r (Quotient.mk (MulAction.orbitRel Γ Y) (p x))
  have hcl : ∀ (γ : Γ) (x : X), cl (γ • x) = cl x := by
    intro γ x
    simp only [cl, hp]
    congr 1
    exact Quotient.sound ⟨γ, rfl⟩
  refine (hP Γ X ↥T cl hcl d ξ).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul, Nat.cast_sum]
  refine Finset.sum_le_sum fun t _ => ?_
  have hsurj : ∀ x : ↥(UpperTheory.V.Af.CohB.part cl hcl t), ∃ g : Γ, g • p x.1 = t.1 := by
    rintro ⟨x, hx⟩
    change cl x = t at hx
    obtain ⟨h, hh⟩ := Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel Γ Y) (p x)))
    refine ⟨Classical.choose (hT (Quotient.mk (MulAction.orbitRel Γ Y) (p x)).out) * h, ?_⟩
    rw [mul_smul]
    simp only at hh ⊢
    rw [hh]
    exact congrArg Subtype.val hx
  refine hcf t ↥(UpperTheory.V.Af.CohB.part cl hcl t) (fun x => p x.1) (fun γ x => hp γ x.1) hsurj D
    (le_trans (Cardinal.mk_le_of_injective
      (f := fun z : {x : ↥(UpperTheory.V.Af.CohB.part cl hcl t) // p x.1 = t.1} => (⟨z.1.1, z.2⟩ : {x // p x = t.1}))
      (fun a b hab => Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hab)))) (hD t.1)) d ξ
