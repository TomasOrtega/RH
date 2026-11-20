import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PullDegWhole

/- English proof (translation)
Introduce `R R' _ _ _ _ i D D' p ⟨ψ⟩`. Take `⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme, g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i` from `⟨IsOpenImmersion.lift _ _ (by`. Introduce and unpack `_ ⟨y, rfl⟩`. Rewrite using `[Scheme.Opens.range_ι]`. Use the proof step `trivial), IsOpenImmersion.lift_fac _ _ _⟩`.

Use `⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩` and prove the remaining obligations. Take `⟨b, hb, hc⟩` from `p.psi_pr x`. Use `⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans ?_⟩` and prove the remaining obligations. Use `(val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)` and prove the remaining obligations. Conclude with `GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _ (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ`.
-/
theorem exists_isPullDeg_top : ∀ {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {i : R →+* R'} {D : DegPre R} {D' : DegPre R'} (p : IsPullDeg i D D'), Nonempty (PsiOn D ⊤) → ∃ p' : IsPullDeg i D D', p'.W = ⊤ ∧ p'.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) = p.e.hom.left ≫ pullback.fst D.P.A.hom (specOf i) ∧ ∀ x, p'.xe x = p.xe x := by
  intro R R' _ _ _ _ i D D' p ⟨ψ⟩
  obtain ⟨g, hg⟩ : ∃ g : (TK R').left ⟶ (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme,
      g ≫ (⊤ : (Spec (CommRingCat.of R)).Opens).ι = jK R' ≫ specOf i :=
    ⟨IsOpenImmersion.lift _ _ (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      trivial), IsOpenImmersion.lift_fac _ _ _⟩
  refine ⟨{ p with W := ⊤, psiW := ψ, g := g, g_comm := hg, psi_pr := fun x => ?_ }, rfl, rfl, fun _ => rfl⟩
  obtain ⟨b, hb, hc⟩ := p.psi_pr x
  refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => (val_corr hJ hc _).trans ?_⟩
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
  exact GlobalTheory.ArcSpecialise.psiOn_agree p.psiW ψ _ _ _
    (by rw [Category.assoc, Category.assoc]; exact congrArg _ (p.g_comm.trans hg.symm)) hJ

end GlobalTheory.PullDegWhole
