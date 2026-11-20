import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv

namespace GlobalTheory.SplitHecke

open Matrix

section

variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ}

/- English proof (translation)
Use `show ∃ o : O, algebraMap O K o = w i`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨j, rfl⟩` from `hx`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Conclude with `⟨1, by simp⟩`. Conclude with `⟨0, by simp [Pi.basisFun_apply, Pi.single_apply, hij]⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨a, ha⟩` from `hx`. Take `⟨b, hb⟩` from `hy`. Conclude with `⟨a + b, by simp [ha, hb]⟩`. Consider the case `smul c x _ hx`. Take `⟨a, ha⟩` from `hx`.

Conclude with `⟨c * a, by simp [ha, Algebra.smul_def]⟩`.
-/
theorem isInt_of_mem_span_basisFun {w : Fin r → K}
    (hw : w ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r)))) (i : Fin r) :
    IsInt O (w i) := by
  show ∃ o : O, algebraMap O K o = w i
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    by_cases hij : i = j
    · subst hij
      exact ⟨1, by simp⟩
    · exact ⟨0, by simp [Pi.basisFun_apply, Pi.single_apply, hij]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by simp [ha, hb]⟩
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨c * a, by simp [ha, Algebra.smul_def]⟩

/- English proof (translation)
Introduce `i j`. Establish `hmem` using `Submodule.mem_map_of_mem (f := ((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) (Submodule.subset_span ⟨j, rfl⟩ : Pi.basisFun K (Fin r) j ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))))`. Take `⟨w, hw, hwe⟩` from `hle hmem`. Simplify using `only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hwe`. Establish `hcol : ((b⁻¹ * a : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ Pi.basisFun K (Fin r) j = w`.

Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]`. Apply the tactic sequence `have hentry : (b⁻¹ * a).1 i j = w i := by`. Rewrite using `[← hcol]`. Simplify using `[Pi.basisFun_apply]`. Rewrite using `[hentry]`.

Conclude with `isInt_of_mem_span_basisFun hw i`.
-/
theorem intM_inv_mul_of_map_le {a b : GL (Fin r) K}
    (hle : (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) ≤
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((b : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)) :
    IntM O (b⁻¹ * a).1 := by
  intro i j
  have hmem := Submodule.mem_map_of_mem
    (f := ((a : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O)
    (Submodule.subset_span ⟨j, rfl⟩ :
      Pi.basisFun K (Fin r) j ∈ Submodule.span O (Set.range (Pi.basisFun K (Fin r))))
  obtain ⟨w, hw, hwe⟩ := hle hmem
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply] at hwe
  have hcol : ((b⁻¹ * a : GL (Fin r) K) : Matrix (Fin r) (Fin r) K) *ᵥ Pi.basisFun K (Fin r) j = w := by
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← hwe, Matrix.mulVec_mulVec, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  have hentry : (b⁻¹ * a).1 i j = w i := by
    rw [← hcol]
    simp [Pi.basisFun_apply]
  rw [hentry]
  exact isInt_of_mem_span_basisFun hw i

end

/- English proof (translation)
Introduce `O K _ _ _ r h h' heq`. Use `show IntM O (h⁻¹ * h').1 ∧ IntM O ((h⁻¹ * h')⁻¹).1`. Use `⟨intM_inv_mul_of_map_le heq.ge, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.mul_inv_rev, inv_inv]`. Conclude with `intM_inv_mul_of_map_le heq.le`.
-/
theorem gInt_inv_mul_of_map_eq : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ)
    (h h' : GL (Fin r) K),
    (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) =
      (Submodule.span O (Set.range (Pi.basisFun K (Fin r)))).map
        (((h' : Matrix (Fin r) (Fin r) K).mulVecLin).restrictScalars O) →
    GInt O (h⁻¹ * h') := by
  intro O K _ _ _ r h h' heq
  show IntM O (h⁻¹ * h').1 ∧ IntM O ((h⁻¹ * h')⁻¹).1
  refine ⟨intM_inv_mul_of_map_le heq.ge, ?_⟩
  rw [_root_.mul_inv_rev, inv_inv]
  exact intM_inv_mul_of_map_le heq.le

end GlobalTheory.SplitHecke
