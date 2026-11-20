import Development.EtaleCohomology.KummerTheory.BockCut

noncomputable section
open CategoryTheory Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.ZHomPf

def linOf {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module (ULift.{1} ℤ) M] [Module (ULift.{1} ℤ) N]
    (f : M →+ N) : M →ₗ[ULift.{1} ℤ] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r x := by
    have h : ((r.down : ℤ) : ULift.{1} ℤ) = r := by ext; simp
    simp only [RingHom.id_apply]
    rw [← h, Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, map_zsmul]

/- English proof (translation)
Introduce `F G f hf`. Use `⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩` and prove the remaining obligations. Introduce `X Y g`. Use extensionality with `a`. Conclude with `(hf Y.unop X.unop g.unop a).symm`.

Introduce `U a`. Both sides reduce to the same expression.
-/
theorem ZHom_of : LateralTheory.KummerTheory.BockCut.ZHom := by
  intro F G f hf
  refine ⟨⟨{ app := fun U => ModuleCat.ofHom (linOf (f U.unop)), naturality := ?_ }⟩, ?_⟩
  · intro X Y g
    ext a
    exact (hf Y.unop X.unop g.unop a).symm
  · intro U a
    rfl

end LateralTheory.KummerTheory.ZHomPf
