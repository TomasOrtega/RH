import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Introduce `h Γ Y _ _ y hB`. Take `⟨c, hc⟩` from `hB`. Use `⟨c, ?_⟩` and prove the remaining obligations. Introduce `X _ p hp hsurj D hD d ξ`. Rewrite using `[h Γ X Y p hp y hsurj d ξ]`.

Use `(hc _).trans ?_` and prove the remaining obligations. Establish `h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D` using `hD`. Establish `hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y)` using `Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt (Cardinal.nat_lt_aleph0 D))`. Establish `hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) = Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d`. Express the relevant statement in the definitionally equal form `Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _`.

Rewrite using `[rank_pi]`. Simplify using `only [rank_fun', Fintype.card_fin]`. Rewrite using `[Cardinal.sum_const']`. Rewrite using `[hr]`. Use `push_cast`.

Rewrite using `[mul_assoc]`. Use `gcongr`.
-/
theorem UpperTheory.orbit_bound_of_shapiro_functorial :
    UpperTheory.V.Af.CohB.ShapiroFun → UpperTheory.V.Af.CohB.OrbBound := by
  intro h Γ Y _ _ y hB
  obtain ⟨c, hc⟩ := hB
  refine ⟨c, ?_⟩
  intro X _ p hp hsurj D hD d ξ
  rw [h Γ X Y p hp y hsurj d ξ]
  refine (hc _).trans ?_
  have h1 : Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) ≤ D := hD
  have hfin : Finite ↥(UpperTheory.V.Af.CohB.fib p hp y) :=
    Cardinal.lt_aleph0_iff_finite.mp (h1.trans_lt (Cardinal.nat_lt_aleph0 D))
  have hr : Module.rank ℂ ↑(Rep.of (UpperTheory.V.Af.CohB.fibRep p hp y ξ)) =
      Cardinal.mk ↥(UpperTheory.V.Af.CohB.fib p hp y) * d := by
    change Module.rank ℂ (↥(UpperTheory.V.Af.CohB.fib p hp y) → Fin d → ℂ) = _
    rw [rank_pi]
    simp only [rank_fun', Fintype.card_fin]
    rw [Cardinal.sum_const']
  rw [hr]
  push_cast
  rw [mul_assoc]
  gcongr
