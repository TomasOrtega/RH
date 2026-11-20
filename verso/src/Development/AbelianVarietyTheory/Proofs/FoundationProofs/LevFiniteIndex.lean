import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Introduce `N l hN hl`. Use `haveI : NeZero N := ⟨hN.ne'⟩`. Use `haveI : NeZero l := ⟨hl.ne'⟩`. Unfold `lev`. Use `infer_instance`.
-/
theorem lev_finiteIndex : ∀ (N l : ℕ), 0 < N → 0 < l → (GlobalTheory.Hk.lev N l).FiniteIndex := by
  intro N l hN hl
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  unfold lev
  infer_instance

end GlobalTheory.Hk
