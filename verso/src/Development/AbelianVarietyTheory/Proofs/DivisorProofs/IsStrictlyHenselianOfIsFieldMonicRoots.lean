import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

/- English proof (translation)
Introduce `T _ hF hA`. Use `letI : Field T := hF.toField`. Use `⟨Field.henselian T, ?_⟩` and prove the remaining obligations. Use `haveI hT : IsAlgClosed T := by`. Use `IsAlgClosed.of_exists_root T ?_` and prove the remaining obligations.

Introduce `p hm hirr`. Take `⟨a, ha⟩` from `hA p hm (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr))`. Conclude with `⟨a, by simpa [Polynomial.IsRoot] using ha⟩`. Establish `hinj : Function.Injective (IsLocalRing.residue T)` using `(IsLocalRing.residue T).injective`. Establish `hbij : Function.Bijective (IsLocalRing.residue T)` using `⟨hinj, IsLocalRing.residue_surjective⟩`.

Use `haveI : IsAlgClosed (IsLocalRing.ResidueField T) := IsAlgClosed.of_ringEquiv T _ (RingEquiv.ofBijective _ hbij)`. Use `infer_instance`.
-/
theorem isField_aic_sh : ∀ (T : Type) [CommRing T], IsField T → AIC T → SH T := by
  intro T _ hF hA
  letI : Field T := hF.toField
  refine ⟨Field.henselian T, ?_⟩
  haveI hT : IsAlgClosed T := by
    refine IsAlgClosed.of_exists_root T ?_
    intro p hm hirr
    obtain ⟨a, ha⟩ := hA p hm (Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr))
    exact ⟨a, by simpa [Polynomial.IsRoot] using ha⟩
  have hinj : Function.Injective (IsLocalRing.residue T) := (IsLocalRing.residue T).injective
  have hbij : Function.Bijective (IsLocalRing.residue T) := ⟨hinj, IsLocalRing.residue_surjective⟩
  haveI : IsAlgClosed (IsLocalRing.ResidueField T) :=
    IsAlgClosed.of_ringEquiv T _ (RingEquiv.ofBijective _ hbij)
  infer_instance

end GlobalTheory.EtC
