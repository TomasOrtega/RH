import Development.EtaleCohomology.EtaleSheaves.SHTensorPf

noncomputable section
open CategoryTheory Limits

namespace LateralTheory.E.SepTensorPf

/- English proof (translation)
Introduce `A X B Z x b u v hp _ hX _ hb _ hZ`. Take `⟨_, hXs⟩` from `hX`. Establish `hu : u.hom.IsIntegral` using `LateralTheory.E.SHTensorPf.intPush hp hb`. Set `f : X →+* IsLocalRing.ResidueField Z` to `(IsLocalRing.residue Z).comp u.hom`. Establish `hf : f.IsIntegral` using `RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)`.

Set `_ : Algebra X (IsLocalRing.ResidueField Z)` to `f.toAlgebra`. Establish `: Algebra.IsIntegral X (IsLocalRing.ResidueField Z)` using `⟨hf⟩`. Establish `: Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z)` using `Algebra.IsIntegral.tower_top X`. Conclude with `Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)`.
-/
theorem SepTensor_of : LateralTheory.E.SHTensorPf.SepTensor := by
  intro A X B Z x b u v hp _ hX _ hb _ hZ
  obtain ⟨_, hXs⟩ := hX
  have hu : u.hom.IsIntegral := LateralTheory.E.SHTensorPf.intPush hp hb
  let f : X →+* IsLocalRing.ResidueField Z := (IsLocalRing.residue Z).comp u.hom
  have hf : f.IsIntegral := RingHom.IsIntegral.trans u.hom (IsLocalRing.residue Z) hu
    (RingHom.isIntegral_of_surjective _ IsLocalRing.residue_surjective)
  let _ : Algebra X (IsLocalRing.ResidueField Z) := f.toAlgebra
  have : Algebra.IsIntegral X (IsLocalRing.ResidueField Z) := ⟨hf⟩
  have : Algebra.IsIntegral (IsLocalRing.ResidueField X) (IsLocalRing.ResidueField Z) :=
    Algebra.IsIntegral.tower_top X
  exact Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField X)

end LateralTheory.E.SepTensorPf
