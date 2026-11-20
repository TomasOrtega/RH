import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory in
/- English proof (translation)
Introduce `hR Γ _ P q X hX A`. Take `⟨i⟩` from `hX`. Rewrite using `[(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]`. Use `(hR _ q).trans ?_` and prove the remaining obligations. Rewrite using `[ChainComplex.linearYonedaObj_X]`.

Conclude with `(Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le`.
-/
theorem UpperTheory.rankCohHom_of_rankHomology :
    UpperTheory.V.Af.CohB.RankHomology → UpperTheory.V.Af.BA.RankCohHom := by
  intro hR Γ _ P q X hX A
  obtain ⟨i⟩ := hX
  rw [(groupCohomologyIsoExt A q ≪≫ P.isoExt q A).toLinearEquiv.rank_eq]
  refine (hR _ q).trans ?_
  rw [ChainComplex.linearYonedaObj_X]
  exact (Linear.homCongr ℂ i (Iso.refl A)).rank_eq.le
