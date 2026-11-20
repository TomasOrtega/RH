import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `h Γ X _ _ hfin`. Use `CategoryTheory.Projective.mk ?_` and prove the remaining obligations. Introduce `E Y f e he`. Establish `hs` using `(Rep.epi_iff_surjective e).1 he`. Establish `heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) = (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1))`.

Introduce `g x`. Establish `hc` using `LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)`. Simplify `hc` using `[UpperTheory.V.Af.BA.permC_single]`. Take `⟨ψ, hψ, hψe⟩` from `h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq`. Use `⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ) ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩` and prove the remaining obligations.

Introduce `g`. Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `x c`. Simplify using `[UpperTheory.V.Af.BA.permC_single, hψ]`. Apply `UpperTheory.V.Af.BA.PC_ext` to reduce the goal to its premises.

Introduce `x`. Simplify using `[Rep.hom_comp, Rep.hom_ofHom, hψe]`.
-/
theorem UpperTheory.projPerm_of_liftEquiv :
    UpperTheory.V.Af.BA.LiftEquiv → UpperTheory.V.Af.BA.ProjPerm := by
  intro h Γ X _ _ hfin
  refine CategoryTheory.Projective.mk ?_
  intro E Y f e he
  have hs := (Rep.epi_iff_surjective e).1 he
  have heq : ∀ (g : Γ) (x : X), (Rep.Hom.hom f) (Finsupp.single (g • x) 1) =
      (Y.ρ g) ((Rep.Hom.hom f) (Finsupp.single x 1)) := by
    intro g x
    have hc := LinearMap.congr_fun ((Rep.Hom.hom f).isIntertwining' g) (Finsupp.single x 1)
    simpa [UpperTheory.V.Af.BA.permC_single] using hc
  obtain ⟨ψ, hψ, hψe⟩ := h Γ X hfin E Y e hs (fun x => (Rep.Hom.hom f) (Finsupp.single x 1)) heq
  refine ⟨Rep.ofHom (ρ := UpperTheory.V.Af.BA.permC Γ X) (σ := E.ρ)
    ⟨Finsupp.linearCombination ℂ ψ, ?_⟩, ?_⟩
  · intro g
    apply Finsupp.lhom_ext
    intro x c
    simp [UpperTheory.V.Af.BA.permC_single, hψ]
  · apply UpperTheory.V.Af.BA.PC_ext
    intro x
    simp [Rep.hom_comp, Rep.hom_ofHom, hψe]
