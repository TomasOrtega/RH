import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LogPair
open scoped TensorProduct

/- English proof (translation)
Introduce `k _ _ X f _ U x hxU _`. Use `letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra`. Establish `key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU = (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x`. Rewrite using `[Scheme.Hom.germ_stalkMap f ⊤ x trivial]`. Simplify using `only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]`.

Establish `hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType`. Introduce `p`. Use `StructureSheaf.IsLocalization.to_stalk k p` as an intermediate fact. Use `Algebra.EssFiniteType.of_isLocalization (R := k) ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl` as an intermediate fact. Conclude with `RingHom.essFiniteType_algebraMap.mpr this`.

Establish `hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType` using `hS0 (f x)`. Establish `hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial = StructureSheaf.toStalk k (f x)`. Rewrite using `[Scheme.ΓSpecIso_inv]`. Conclude with `StructureSheaf.toOpen_germ _ _ _`. Establish `hφ : algebraMap k (X.presheaf.stalk x) = (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫ f.stalkMap x).hom` using `by show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _`.

Rewrite using `[cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]`. Establish `hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType` using `hT ▸ hS`. Establish `hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType` using `RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective`. Establish `hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType`. Establish `h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x))` using `rfl`.

Rewrite using `[h, hφ, CommRingCat.hom_comp]`. Conclude with `(hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType`. Use `haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := RingHom.essFiniteType_algebraMap.mp hE`. Conclude with `Algebra.FormallySmooth.of_perfectField`.
-/
theorem GlobalTheory.residueField_formallySmooth_of_isClosed : ∀ (k : Type) [Field k] [PerfectField k] (X : Scheme.{0}) (f : X ⟶ Sp k) [LocallyOfFiniteType f] (U : X.Opens) (x : X) (hxU : x ∈ U), IsClosed ({x} : Set X) → letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra; Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  intro k _ _ X f _ U x hxU _
  letI : Algebra k (X.presheaf.stalk x) := ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)).toAlgebra
  have key : f.appLE ⊤ U le_top ≫ X.presheaf.germ U x hxU =
      (Sp k).presheaf.germ ⊤ (f x) trivial ≫ f.stalkMap x := by
    rw [Scheme.Hom.germ_stalkMap f ⊤ x trivial]
    simp only [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  have hS0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := by
    intro p
    have := StructureSheaf.IsLocalization.to_stalk k p
    have := Algebra.EssFiniteType.of_isLocalization (R := k)
      ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.essFiniteType_algebraMap.mpr this
  have hS : (StructureSheaf.toStalk k (f x)).hom.EssFiniteType := hS0 (f x)
  have hT : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial =
      StructureSheaf.toStalk k (f x) := by
    rw [Scheme.ΓSpecIso_inv]
    exact StructureSheaf.toOpen_germ _ _ _
  have hφ : algebraMap k (X.presheaf.stalk x) =
      (((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ (Sp k).presheaf.germ ⊤ (f x) trivial) ≫
        f.stalkMap x).hom := by
    show ((X.presheaf.germ U x hxU).hom.comp (cstOn f U)) = _
    rw [cstOn, ← CommRingCat.hom_comp, Category.assoc, Category.assoc, key]
  have hS' : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Sp k).presheaf.germ ⊤ (f x) trivial).hom.EssFiniteType := hT ▸ hS
  have hR : (IsLocalRing.residue (X.presheaf.stalk x)).FiniteType :=
    RingHom.FiniteType.of_surjective _ IsLocalRing.residue_surjective
  have hE : (algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x))).EssFiniteType := by
    have h : algebraMap k (IsLocalRing.ResidueField (X.presheaf.stalk x)) =
        (IsLocalRing.residue (X.presheaf.stalk x)).comp (algebraMap k (X.presheaf.stalk x)) := rfl
    rw [h, hφ, CommRingCat.hom_comp]
    exact (hS'.comp (LocallyOfFiniteType.stalkMap f x)).comp hR.essFiniteType
  haveI : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    RingHom.essFiniteType_algebraMap.mp hE
  exact Algebra.FormallySmooth.of_perfectField
