import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CoordRes

/- English proof (translation)
Establish `key` using `HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h`. Establish `e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op`. Apply the tactic sequence `simp [Scheme.Hom.appLE] <;> rfl`. Rewrite `key` using `[e]`. Conclude with `key`.
-/
theorem etale_rs {X : Scheme.{0}} {V W : X.Opens} (h : W ≤ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) :
    (rs h).Etale := by
  have key := HasRingHomProperty.appLE @Etale (𝟙 X) inferInstance ⟨V, hV⟩ ⟨W, hW⟩ h
  have e : Scheme.Hom.appLE (𝟙 X) V W h = X.presheaf.map (homOfLE h).op := by
    simp [Scheme.Hom.appLE] <;> rfl
  rw [e] at key
  exact key

/- English proof (translation)
Simplify using `only [rs, strV]`. Rewrite using `[← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]`.
-/
theorem rs_comp_strV {O : Type} [CommRing O] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {V W : X.Opens}
    (h : W ≤ V) : (rs h).comp (strV q V) = strV q W := by
  simp only [rs, strV]
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.appLE_map]

/- English proof (translation)
Introduce `O _ X q V W d c h hW`. Use `⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩` and prove the remaining obligations. Establish `e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) = (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t)`. Rewrite using `[MvPolynomial.comp_eval₂Hom, rs_comp_strV]`. Rewrite using `[e1]`.

Conclude with `RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)`.
-/
theorem main : ∀ {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {V W : X.Opens} {d : ℕ}
    (c : Coord q V d) (h : W ≤ V) (hW : IsAffineOpen W), ∃ c' : Coord q W d, ∀ i, c'.t i = rs h (c.t i) := by
  intro O _ X q V W d c h hW
  refine ⟨⟨hW, fun i => rs h (c.t i), ?_⟩, fun i => rfl⟩
  have e1 : MvPolynomial.eval₂Hom (strV q W) (fun i => rs h (c.t i)) =
      (rs h).comp (MvPolynomial.eval₂Hom (strV q V) c.t) := by
    rw [MvPolynomial.comp_eval₂Hom, rs_comp_strV]
  rw [e1]
  exact RingHom.Etale.stableUnderComposition _ _ c.etale (etale_rs h c.affine hW)

end GlobalTheory.CompanionTheory.CoordRes
