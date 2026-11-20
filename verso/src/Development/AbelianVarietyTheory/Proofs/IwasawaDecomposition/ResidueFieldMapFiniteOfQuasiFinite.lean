import Mathlib
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory

/- English proof (translation)
Use `algebraize [f]`. Establish `: IsLocalHom (algebraMap R S)` using `‹IsLocalHom f›`. Establish `: Algebra.QuasiFinite R (IsLocalRing.ResidueField S)` using `Algebra.QuasiFinite.of_surjective_algHom (IsScalarTower.toAlgHom R S _) IsLocalRing.residue_surjective`. Establish `: Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)` using `.of_restrictScalars R _ _`. Establish `hfin : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)` using `Algebra.QuasiFinite.iff_of_isArtinianRing.mp this`.

Establish `heq : IsLocalRing.ResidueField.map f = algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)`. Use extensionality with `x`. Take `⟨a, rfl⟩` from `IsLocalRing.residue_surjective x`. Both sides reduce to the same expression. Rewrite using `[heq]`.

Conclude with `RingHom.finite_algebraMap.mpr hfin`.
-/
theorem residueField_map_finite_of_quasiFinite {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] (h : f.QuasiFinite) :
    (IsLocalRing.ResidueField.map f).Finite := by
  algebraize [f]
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Algebra.QuasiFinite R (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.of_surjective_algHom (IsScalarTower.toAlgHom R S _)
      IsLocalRing.residue_surjective
  have : Algebra.QuasiFinite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    .of_restrictScalars R _ _
  have hfin : Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.QuasiFinite.iff_of_isArtinianRing.mp this
  have heq : IsLocalRing.ResidueField.map f =
      algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
    ext x
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    rfl
  rw [heq]
  exact RingHom.finite_algebraMap.mpr hfin

/- English proof (translation)
Establish `hq : (g.stalkMap y).hom.QuasiFinite` using `g.quasiFiniteAt y`. Conclude with `residueField_map_finite_of_quasiFinite _ hq`.
-/
theorem residueFieldMap_finite_of_locallyQuasiFinite {Y Z : Scheme.{0}} (g : Y ⟶ Z)
    [LocallyQuasiFinite g] (y : Y) : (g.residueFieldMap y).hom.Finite := by
  have hq : (g.stalkMap y).hom.QuasiFinite := g.quasiFiniteAt y
  exact residueField_map_finite_of_quasiFinite _ hq

end GlobalTheory
