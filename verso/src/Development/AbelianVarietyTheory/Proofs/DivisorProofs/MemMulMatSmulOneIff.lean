import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

/- English proof (translation)
Establish `h : ∀ y : Fin 2 → F, Matrix.vecMul y ((c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F)) = (c : 𝓞 F) • y`. Introduce `y`. Establish `hm : (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F) = c • (1 : Matrix (Fin 2) (Fin 2) F)`. Use extensionality with `i j`. Rewrite using `[Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[Int.cast_smul_eq_zsmul, hm, Matrix.vecMul_smul, Matrix.vecMul_one]`. Unfold `mulMat`. Simplify using `only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, h]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y, hy, rfl⟩`.
-/
theorem mem_mulMat_smul_one_iff {F : Type} [Field F] [NumberField F] (L : Lat F) (c : ℤ) (v : Fin 2 → F) :
    v ∈ mulMat L (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)) ↔ ∃ y ∈ L, v = (c : 𝓞 F) • y := by
  have h : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F)) = (c : 𝓞 F) • y := by
    intro y
    have hm : (c • (1 : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.cast : ℤ → F) = c • (1 : Matrix (Fin 2) (Fin 2) F) := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [Int.cast_smul_eq_zsmul, hm, Matrix.vecMul_smul, Matrix.vecMul_one]
  unfold mulMat
  simp only [Submodule.mem_map, LinearMap.restrictScalars_apply, Matrix.vecMulLinear_apply, h]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩; exact ⟨y, hy, rfl⟩

/- English proof (translation)
Introduce `F _ _ _ N L hL`. Establish `h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ) = (ZMod.cast (1 : ZMod N) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ)`. Use extensionality with `i j`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Unfold `twist`.

Rewrite using `[h1]`. Apply `le_antisymm` to reduce the goal to its premises. Use `sup_le (fun v hv ↦ ?_) (fun v hv ↦ ?_)` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `(mem_mulMat_smul_one_iff _ _ _).1 hv`. Conclude with `L.smul_mem _ hy`.

Take `⟨y, hy, rfl⟩` from `(mem_mulMat_smul_one_iff _ _ _).1 hv`. Simplify using `using hL.1 y hy`. Introduce `v hv`. Distinguish the cases in `hN : N = 1`. Substitute `hN` using the available equality.

Use `Submodule.mem_sup_right ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hL.2 hv, by simp⟩)` and prove the remaining obligations. Establish `hc : (ZMod.cast (1 : ZMod N) : ℤ) = 1`. Break down `N with _ | _ | N` into its components or cases. Both sides reduce to the same expression. Conclude with `absurd rfl hN`.

Rewrite using `[ZMod.cast_eq_val, ZMod.val_one'' hN]`. Simplify using the standard rewrite rules. Rewrite using `[hc]`. Conclude with `Submodule.mem_sup_left ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hv, by simp⟩)`.
-/
theorem twist_one_of_hasLevel : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F),
    HasLevel N L → twist N L 1 = L := by
  intro F _ _ _ N L hL
  have h1 : (1 : Matrix (Fin 2) (Fin 2) (ZMod N)).map (ZMod.cast : ZMod N → ℤ)
      = (ZMod.cast (1 : ZMod N) : ℤ) • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold twist
  rw [h1]
  apply le_antisymm
  · refine sup_le (fun v hv ↦ ?_) (fun v hv ↦ ?_)
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      exact L.smul_mem _ hy
    · obtain ⟨y, hy, rfl⟩ := (mem_mulMat_smul_one_iff _ _ _).1 hv
      simpa using hL.1 y hy
  · intro v hv
    by_cases hN : N = 1
    · subst hN
      refine Submodule.mem_sup_right ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hL.2 hv, by simp⟩)
    · have hc : (ZMod.cast (1 : ZMod N) : ℤ) = 1 := by
        rcases N with _ | _ | N
        · rfl
        · exact absurd rfl hN
        · rw [ZMod.cast_eq_val, ZMod.val_one'' hN]; simp
      rw [hc]
      exact Submodule.mem_sup_left ((mem_mulMat_smul_one_iff _ _ _).2 ⟨v, hv, by simp⟩)

end GlobalTheory.HilbFam
