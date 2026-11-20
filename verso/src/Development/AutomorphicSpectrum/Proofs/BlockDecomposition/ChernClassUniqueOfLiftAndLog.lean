import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.EtaleComparisonMapOfFacts
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EtChern

/- English proof (translation)
Substitute using the available equality. Extract witnesses or component facts from the available result. Both sides reduce to the same expression.
-/
theorem restrict_id_pull {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) (x : H (𝟭 C ⋙ F) 2) (x' : H F 2)
    (h : x = (Mor.restrict F (𝟭 C)).pull 2 x') : x = x' := by
  subst h
  obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Apply function extensionality and compare values at an arbitrary argument. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Substitute using the available equality. Establish an intermediate fact. Establish an intermediate fact.

A detailed English derivation is pending.
-/
theorem chern_class_unique_of_lift_and_log : CrystallineSemistableComparison.E.LiftEx → CrystallineSemistableComparison.E.LogEx → CrystallineSemistableComparison.E.FirstChernUniqueEtale := by
  intro hL hG l _ H O _ X q κ D hE y y' hy hy'
  obtain ⟨Λ⟩ := (hL l H O X q κ (El (PX q κ)) (𝟭 _) D).2 hE
  funext n
  obtain ⟨z, hz, hc, e⟩ := hy (El (PX q κ)) (𝟭 _) Λ n
  obtain ⟨z', hz', hc', e'⟩ := hy' (El (PX q κ)) (𝟭 _) Λ n
  have hzz : z = z' := by
    funext s
    exact (hG l _ n).2.1 _ _ _ (hc s) (hc' s)
  subst hzz
  have e1 := restrict_id_pull _ _ _ e
  have e2 := restrict_id_pull _ _ _ e'
  exact e1.symm.trans e2

end GlobalTheory.CompanionTheory.EtChern
