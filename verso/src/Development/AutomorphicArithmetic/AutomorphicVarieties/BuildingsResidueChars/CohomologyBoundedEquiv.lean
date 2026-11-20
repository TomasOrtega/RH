import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HomologyRank.RankHomology

/- English proof (translation)
Introduce `Γ Γ' _ _ ⟨φ⟩ ⟨c, hc⟩`. Use `⟨c, fun A => ?_⟩` and prove the remaining obligations. Establish `key` using `hc (Rep.res φ.toMonoidHom A)`. Establish `heq : ∀ q, Module.rank ℂ (groupCohomology (Rep.res φ.toMonoidHom A) q) = Module.rank ℂ (groupCohomology A q)` using `fun q => ((groupCohomology.mapIso φ (LinearEquiv.refl ℂ A.V) (fun g => rfl) q).toLinearEquiv).rank_eq`. Unfold `UpperTheory.V.Af.CohB.totCoh at key ⊢`.

Simplify using `only [heq] at key`. Conclude with `key`.
-/
theorem UpperTheory.cohomology_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv := by
  intro Γ Γ' _ _ ⟨φ⟩ ⟨c, hc⟩
  refine ⟨c, fun A => ?_⟩
  have key := hc (Rep.res φ.toMonoidHom A)
  have heq : ∀ q, Module.rank ℂ (groupCohomology (Rep.res φ.toMonoidHom A) q) =
      Module.rank ℂ (groupCohomology A q) := fun q =>
    ((groupCohomology.mapIso φ (LinearEquiv.refl ℂ A.V) (fun g => rfl) q).toLinearEquiv).rank_eq
  unfold UpperTheory.V.Af.CohB.totCoh at key ⊢
  simp only [heq] at key
  exact key
