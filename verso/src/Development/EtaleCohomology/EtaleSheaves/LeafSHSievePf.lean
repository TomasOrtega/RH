import Development.EtaleCohomology.EtaleSheaves.LeafClosedSH0Of
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafSHSievePf

/- English proof (translation)
Introduce `X _ hSH S hS`. Take `⟨hHens, hSep⟩` from `hSH`. Set `A : Type` to `Γ(X, ⊤)`. Set `K : Type` to `IsLocalRing.ResidueField A`. Set `π : A →+* K` to `IsLocalRing.residue A`.

Take `⟨𝒰, hle⟩` from `Scheme.mem_grothendieckTopology_iff.1 hS`. Set `x : Spec (.of K) ⟶ X` to `Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv`. Take `⟨Y, g, hg, y, hy⟩` from `(Scheme.geometricFiber K).jointly_surjective _ (Scheme.Cover.mem_grothendieckTopology 𝒰) x`. Take `⟨Z, h, _, ⟨i⟩, rfl⟩` from `hg`. Establish `hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv`.

Conclude with `(Category.assoc _ _ _).trans hy`. Take `⟨l, ⟨-, hl⟩, -⟩` from `GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'`. Establish `hmem : S (𝒰.f i)` using `hle _ _ (Presieve.ofArrows.mk i)`. Use `S.downward_closed hmem (X.isoSpec.hom ≫ l)` as an intermediate fact. Establish `e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X` using `by rw [Category.assoc, hl, Iso.hom_inv_id]`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis.
-/
theorem LeafSHSieve_of : LateralTheory.E.LeafClosedSH0Pf.LeafSHSieve := by
  intro X _ hSH S hS
  obtain ⟨hHens, hSep⟩ := hSH
  let A : Type := Γ(X, ⊤)
  let K : Type := IsLocalRing.ResidueField A
  let π : A →+* K := IsLocalRing.residue A
  obtain ⟨𝒰, hle⟩ := Scheme.mem_grothendieckTopology_iff.1 hS
  let x : Spec (.of K) ⟶ X := Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv
  obtain ⟨Y, g, hg, y, hy⟩ := (Scheme.geometricFiber K).jointly_surjective _
    (Scheme.Cover.mem_grothendieckTopology 𝒰) x
  obtain ⟨Z, h, _, ⟨i⟩, rfl⟩ := hg
  have hy' : (y ≫ h) ≫ 𝒰.f i = Spec.map (CommRingCat.ofHom π) ≫ X.isoSpec.inv := by
    exact (Category.assoc _ _ _).trans hy
  obtain ⟨l, ⟨-, hl⟩, -⟩ := GlobalTheory.existsUnique_lift_of_etale_of_henselian (𝒰.f i) π
    IsLocalRing.residue_surjective (y ≫ h) X.isoSpec.inv hy'
  have hmem : S (𝒰.f i) := hle _ _ (Presieve.ofArrows.mk i)
  have := S.downward_closed hmem (X.isoSpec.hom ≫ l)
  have e : (X.isoSpec.hom ≫ l) ≫ 𝒰.f i = 𝟙 X := by rw [Category.assoc, hl, Iso.hom_inv_id]
  rwa [e] at this

end LateralTheory.E.LeafSHSievePf
