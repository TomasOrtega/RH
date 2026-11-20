import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.GeoDefs
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison.Pb
attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.CompanionTheory.GeoCoord

/- English proof (translation)
Use `letI := (strV q W).toAlgebra`. Introduce `h`. Use `haveI := hW.isLocalization_basicOpen g`. Set `φ` to `IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)`. Establish `hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x` using `fun x => φ.commutes x`.

Use `⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Establish `h2` using `RingHom.Etale.stableUnderComposition _ _ h (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)`. Establish `e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) : MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) = (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g)) (fun k => algebraMap …`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)` and prove the remaining obligations. Simplify using `only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]`.

Rewrite using `[strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]`. Conclude with `(hφ _).symm`. Simplify using `only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]`. Conclude with `(hφ _).symm`. Rewrite using `[e]`.

Conclude with `h2`.
-/
theorem exists_coord_basicOpen {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    {W : X.Opens} (hW : IsAffineOpen W) (g : Γ(X, W)) {d : ℕ} (s : Fin d → Γ(X, W)) :
    letI := (strV q W).toAlgebra
    (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
      (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k)) :
        MvPolynomial (Fin d) K →+* Localization.Away g).Etale →
    ∃ c : Coord q (X.basicOpen g) d, ∀ k, c.t k = resO (X.basicOpen_le g) (s k) := by
  letI := (strV q W).toAlgebra
  intro h
  haveI := hW.isLocalization_basicOpen g
  let φ := IsLocalization.algEquiv (Submonoid.powers g) (Localization.Away g) Γ(X, X.basicOpen g)
  have hφ : ∀ x, φ (algebraMap Γ(X, W) (Localization.Away g) x) = resO (X.basicOpen_le g) x :=
    fun x => φ.commutes x
  refine ⟨⟨hW.basicOpen g, fun k => resO (X.basicOpen_le g) (s k), ?_⟩, fun _ => rfl⟩
  have h2 := RingHom.Etale.stableUnderComposition _ _ h
    (RingHom.Etale.of_bijective (f := (φ : Localization.Away g →+* Γ(X, X.basicOpen g))) φ.bijective)
  have e : (MvPolynomial.eval₂Hom (strV q (X.basicOpen g)) (fun k => resO (X.basicOpen_le g) (s k)) :
        MvPolynomial (Fin d) K →+* Γ(X, X.basicOpen g)) =
      (φ : Localization.Away g →+* Γ(X, X.basicOpen g)).comp
        (MvPolynomial.eval₂Hom (algebraMap K (Localization.Away g))
          (fun k => algebraMap Γ(X, W) (Localization.Away g) (s k))) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun k => ?_)
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C, RingHom.comp_apply]
      rw [strV_res q (X.basicOpen_le g), RingHom.comp_apply, IsScalarTower.algebraMap_apply K Γ(X, W) (Localization.Away g)]
      exact (hφ _).symm
    · simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X, RingHom.comp_apply]
      exact (hφ _).symm
  rw [e]
  exact h2

end GlobalTheory.CompanionTheory.GeoCoord
