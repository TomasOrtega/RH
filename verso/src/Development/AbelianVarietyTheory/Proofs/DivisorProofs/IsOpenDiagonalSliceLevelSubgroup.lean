import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CentralNilGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkGLOneCorner
open NumberField MeasureTheory GlobalTheory.CuspRep

namespace GlobalTheory.SliceTwo

open GlobalTheory.LeviGA

/- English proof (translation)
Introduce `E _ _ a r hr t L hL`. Establish `hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l)`. Rewrite using `[Units.continuous_iff]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show Continuous fun l : GL (Fin (a - r)) (Af E) => Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))`.

Conclude with `(continuous_const.matrix_fromBlocks continuous_const continuous_const Units.continuous_val).matrix_reindex _ _`. Establish `e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹)`. Introduce `l`. Rewrite using `[← map_inv]`. Both sides reduce to the same expression.

Repeatedly rewrite using `[e]`. Use `show Continuous fun l : GL (Fin (a - r)) (Af E) => Matrix.reindex (blkEquiv hr) (blkEquiv hr) (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))`. Conclude with `(continuous_const.matrix_fromBlocks continuous_const continuous_const Units.continuous_coe_inv).matrix_reindex _ _`. Establish `hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t` using `(continuous_const.mul hblk).mul continuous_const`. Establish `hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) = (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E)))`.

Use extensionality with `l`. Simplify using `only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, e⟩`. Rewrite using `[← e]`.

Simplify `hk` using `[mul_assoc]`. Introduce `h`. Conclude with `⟨_, h, by group⟩`. Rewrite using `[hs]`. Conclude with `hL.preimage hc`.
-/
theorem isOpen_levelSub : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (hr : r ≤ a) (t : GL (Fin a) (Af E))
    (L : Subgroup (GL (Fin a) (Af E))), IsOpen (L : Set (GL (Fin a) (Af E))) →
      IsOpen (GlobalTheory.SliceTwo.levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) := by
  intro E _ _ a r hr t L hL
  have hblk : Continuous fun l : GL (Fin (a - r)) (Af E) => blkGL hr (1, l) := by
    rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 (l : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_val).matrix_reindex _ _
    · have e : ∀ l : GL (Fin (a - r)) (Af E), ((blkGL hr (1, l))⁻¹ : GL (Fin a) (Af E)) = blkGL hr (1, l⁻¹) := by
        intro l; rw [← map_inv]; rfl
      simp_rw [e]
      show Continuous fun l : GL (Fin (a - r)) (Af E) =>
        Matrix.reindex (blkEquiv hr) (blkEquiv hr)
          (Matrix.fromBlocks ((1 : GL (Fin r) (Af E)) : Matrix _ _ (Af E)) 0 0 ((l⁻¹ : GL _ _) : Matrix _ _ (Af E)))
      exact (continuous_const.matrix_fromBlocks continuous_const continuous_const
        Units.continuous_coe_inv).matrix_reindex _ _
  have hc : Continuous fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t :=
    (continuous_const.mul hblk).mul continuous_const
  have hs : (levelSub hr t L : Set (GL (Fin (a - r)) (Af E))) =
      (fun l : GL (Fin (a - r)) (Af E) => t⁻¹ * blkGL hr (1, l) * t) ⁻¹' (L : Set (GL (Fin a) (Af E))) := by
    ext l
    simp only [levelSub, Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_map,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inr_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, e⟩
      rw [← e]; simpa [mul_assoc] using hk
    · intro h
      exact ⟨_, h, by group⟩
  rw [hs]
  exact hL.preimage hc

end GlobalTheory.SliceTwo
