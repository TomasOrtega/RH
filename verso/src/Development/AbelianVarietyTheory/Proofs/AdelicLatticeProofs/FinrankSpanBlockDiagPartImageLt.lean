import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Introduce `ι _ _ Γ e a ha ha0 hblk`. Set `L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ` to `{ toFun := fun x => blk e x map_add' := fun x y => by`. Simplify using `only [blk, Matrix.mul_add, Matrix.add_mul]`. Normalize the expressions using the abelian group laws. Use the proof step `map_smul' := fun c x => by`.

Simplify using `only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }`. Establish `himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L`. Rewrite using `[Submodule.map_span]`. Both sides reduce to the same expression. Rewrite using `[himg]`.

Use `set S := Submodule.span ℂ Γ with hS`. Set `f` to `L.domRestrict S`. Establish `hrange : LinearMap.range f = S.map L` using `LinearMap.range_domRestrict S L`. Establish `hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f`. Simplify using `only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]`.

Conclude with `hblk`. Establish `hne : LinearMap.ker f ≠ ⊥`. Introduce `h`. Rewrite `hker` using `[h, Submodule.mem_bot]`. Conclude with `ha0 (congrArg Subtype.val hker)`.

Establish `hpos : 0 < Module.finrank ℂ (LinearMap.ker f)` using `Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)`. Establish `hrn` using `LinearMap.finrank_range_add_finrank_ker f`. Rewrite `hrn` using `[hrange]`. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_span_blk_image_lt :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ) (a : Matrix ι ι ℂ), a ∈ Submodule.span ℂ Γ → a ≠ 0 → blk e a = 0 → Module.finrank ℂ (Submodule.span ℂ (blk e '' Γ)) < Module.finrank ℂ (Submodule.span ℂ Γ) := by
  intro ι _ _ Γ e a ha ha0 hblk

  let L : Matrix ι ι ℂ →ₗ[ℂ] Matrix ι ι ℂ :=
    { toFun := fun x => blk e x
      map_add' := fun x y => by
        simp only [blk, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c x => by
        simp only [blk, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_add] }
  have himg : Submodule.span ℂ (blk e '' Γ) = (Submodule.span ℂ Γ).map L := by
    rw [Submodule.map_span]
    rfl
  rw [himg]

  set S := Submodule.span ℂ Γ with hS
  let f := L.domRestrict S
  have hrange : LinearMap.range f = S.map L := LinearMap.range_domRestrict S L
  have hker : (⟨a, ha⟩ : S) ∈ LinearMap.ker f := by
    simp only [LinearMap.mem_ker, f, LinearMap.domRestrict_apply]
    exact hblk
  have hne : LinearMap.ker f ≠ ⊥ := by
    intro h
    rw [h, Submodule.mem_bot] at hker
    exact ha0 (congrArg Subtype.val hker)
  have hpos : 0 < Module.finrank ℂ (LinearMap.ker f) :=
    Nat.pos_of_ne_zero fun h => hne (Submodule.finrank_eq_zero.mp h)
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  rw [hrange] at hrn
  omega

end GlobalTheory.ClassFin
