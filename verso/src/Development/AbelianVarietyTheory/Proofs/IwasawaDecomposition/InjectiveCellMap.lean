import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsClosedFlagsIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniMatBlockTriangular

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace

namespace GlobalTheory.FlagPts

/- English proof (translation)
Use extensionality with `a c`. Rewrite using `[Basis.toMatrix_apply, cellFrame_apply, map_sum]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem toMatrix_cellFrame {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (b : Frames k V) (u : AffPts k (CellIdx k V)) (i : ι) :
    (b i).toMatrix (cellFrame b u i) = uniMat u i := by
  ext a c
  rw [Basis.toMatrix_apply, cellFrame_apply, map_sum]
  simp [Finsupp.single_apply]

/- English proof (translation)
Introduce `u u' h`. Establish `key : ∀ i, uniMat u i = uniMat u' i`. Introduce `i`. Establish `hflag : (cellFrame b u i).flag = (cellFrame b u' i).flag` using `congrArg FullFlag.sub (congrFun h i)`. Use `set B := cellFrame b u i`.

Use `set B' := cellFrame b u' i`. Use `set Y := B.toMatrix B'`. Establish `hmul : uniMat u i * Y = uniMat u' i`. Rewrite using `[← toMatrix_cellFrame b u i, ← toMatrix_cellFrame b u' i, Basis.toMatrix_mul_toMatrix]`. Establish `hup : ∀ j c, c < j → Y j c = 0`.

Introduce `j c hcj`. Establish `hm : B' c ∈ B'.flag c.succ` using `B'.self_mem_flag Fin.castSucc_lt_succ`. Rewrite `hm` using `[← hflag]`. Conclude with `(mem_basis_flag_iff B _ _).1 hm j (Fin.succ_le_castSucc_iff.mpr hcj)`. Establish `hdet : IsUnit (uniMat u i).det` using `by rw [det_uniMat]; exact isUnit_one`.

Establish `hY : Y = (uniMat u i)⁻¹ * uniMat u' i`. Rewrite using `[← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]`. Establish `hlow : ∀ j c, j < c → Y j c = 0`. Use `letI := (uniMat u i).invertibleOfIsUnitDet hdet`. Establish `h1` using `Matrix.blockTriangular_inv_of_blockTriangular (uniMat_blockTriangular u i)`.

Establish `h2` using `h1.mul (uniMat_blockTriangular u' i)`. Introduce `j c hjc`. Rewrite using `[hY]`. Conclude with `h2 (by simpa using hjc)`. Establish `hdiag : ∀ c, Y c c = 1`.

Introduce `c`. Use `congrFun (congrFun hmul c) c` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Finset.sum_eq_single c, uniMat_apply_self, uniMat_apply_self, one_mul]`. Conclude with `this`. Introduce `j _ hj`.

Break down `lt_or_gt_of_ne hj with hj | hj` into its components or cases. Rewrite using `[hlow j c hj, mul_zero]`. Rewrite using `[hup j c hj, mul_zero]`. Introduce `hc`. Conclude with `absurd (Finset.mem_univ c) hc`.

Establish `hY1 : Y = 1`. Use extensionality with `j c`. Break down `lt_trichotomy j c with hjc | rfl | hjc` into its components or cases. Rewrite using `[hlow j c hjc, Matrix.one_apply_ne hjc.ne]`. Rewrite using `[hdiag, Matrix.one_apply_eq]`.

Rewrite using `[hup j c hjc, Matrix.one_apply_ne hjc.ne']`. Rewrite using `[← hmul, hY1, Matrix.mul_one]`. Use function extensionality and compare the values at `x`. Take `⟨i, ⟨a, c⟩, hac⟩` from `x`. Use `congrFun (congrFun (key i) a) c` as an intermediate fact.

Rewrite `this` using `[uniMat_apply_of_lt u i hac, uniMat_apply_of_lt u' i hac]`. Then use the resulting hypothesis.
-/
theorem cellMap_injective (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Function.Injective (cellMap b) := by
  intro u u' h
  have key : ∀ i, uniMat u i = uniMat u' i := by
    intro i
    have hflag : (cellFrame b u i).flag = (cellFrame b u' i).flag :=
      congrArg FullFlag.sub (congrFun h i)
    set B := cellFrame b u i
    set B' := cellFrame b u' i
    set Y := B.toMatrix B'
    have hmul : uniMat u i * Y = uniMat u' i := by
      rw [← toMatrix_cellFrame b u i, ← toMatrix_cellFrame b u' i, Basis.toMatrix_mul_toMatrix]
    have hup : ∀ j c, c < j → Y j c = 0 := by
      intro j c hcj
      have hm : B' c ∈ B'.flag c.succ := B'.self_mem_flag Fin.castSucc_lt_succ
      rw [← hflag] at hm
      exact (mem_basis_flag_iff B _ _).1 hm j (Fin.succ_le_castSucc_iff.mpr hcj)
    have hdet : IsUnit (uniMat u i).det := by rw [det_uniMat]; exact isUnit_one
    have hY : Y = (uniMat u i)⁻¹ * uniMat u' i := by
      rw [← hmul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
    have hlow : ∀ j c, j < c → Y j c = 0 := by
      letI := (uniMat u i).invertibleOfIsUnitDet hdet
      have h1 := Matrix.blockTriangular_inv_of_blockTriangular (uniMat_blockTriangular u i)
      have h2 := h1.mul (uniMat_blockTriangular u' i)
      intro j c hjc
      rw [hY]
      exact h2 (by simpa using hjc)
    have hdiag : ∀ c, Y c c = 1 := by
      intro c
      have := congrFun (congrFun hmul c) c
      rw [Matrix.mul_apply, Finset.sum_eq_single c, uniMat_apply_self, uniMat_apply_self, one_mul] at this
      · exact this
      · intro j _ hj
        rcases lt_or_gt_of_ne hj with hj | hj
        · rw [hlow j c hj, mul_zero]
        · rw [hup j c hj, mul_zero]
      · intro hc; exact absurd (Finset.mem_univ c) hc
    have hY1 : Y = 1 := by
      ext j c
      rcases lt_trichotomy j c with hjc | rfl | hjc
      · rw [hlow j c hjc, Matrix.one_apply_ne hjc.ne]
      · rw [hdiag, Matrix.one_apply_eq]
      · rw [hup j c hjc, Matrix.one_apply_ne hjc.ne']
    rw [← hmul, hY1, Matrix.mul_one]
  funext x
  obtain ⟨i, ⟨a, c⟩, hac⟩ := x
  have := congrFun (congrFun (key i) a) c
  rwa [uniMat_apply_of_lt u i hac, uniMat_apply_of_lt u' i hac] at this

end GlobalTheory.FlagPts
