import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Matrix Formalism.UG GlobalTheory.Doubling

namespace GlobalTheory.Core.Rk.IwArch

section Alg

open scoped ComplexOrder

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Simplify using `[cT, Matrix.map_add, Matrix.transpose_add]`.
-/
theorem cT_add (σ : A →+* A) (M N : Matrix n n A) : cT σ (M + N) = cT σ M + cT σ N := by
  simp [cT, Matrix.map_add, Matrix.transpose_add]

/- English proof (translation)
Simplify using `[cT, Matrix.map_sub, Matrix.transpose_sub]`.
-/
theorem cT_sub (σ : A →+* A) (M N : Matrix n n A) : cT σ (M - N) = cT σ M - cT σ N := by
  simp [cT, Matrix.map_sub, Matrix.transpose_sub]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[cT, conjTranspose_apply, hσ]`.
-/
theorem map_cT (σ : A →+* A) (f : A →+* ℂ) (hσ : ∀ x, f (σ x) = star (f x)) (M : Matrix n n A) :
    (cT σ M).map f = (M.map f)ᴴ := by
  ext i j
  simp [cT, conjTranspose_apply, hσ]

/- English proof (translation)
Rewrite using `[← Matrix.mulVec_injective_iff_isUnit]`. Introduce `v w hvw`. Establish `hd : x *ᵥ (v - w) = 0` using `by rw [mulVec_sub, hvw, sub_self]`. Establish `hy : y *ᵥ (v - w) = 0`. Establish `: (v - w) ∈ LinearMap.ker (yᴴ * y).mulVecLin`.

Rewrite using `[LinearMap.mem_ker, Matrix.mulVecLin_apply, ← h1, ← mulVec_mulVec, hd, mulVec_zero]`. Rewrite `this` using `[ker_mulVecLin_conjTranspose_mul_self, LinearMap.mem_ker, Matrix.mulVecLin_apply]`. Conclude with `this`. Establish `h3 : (1 + 1 : Matrix n n ℂ) *ᵥ (v - w) = 0`. Rewrite using `[← h2, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hd, hy, mulVec_zero, mulVec_zero, sub_zero]`.

Rewrite `h3` using `[add_mulVec, one_mulVec]`. Establish `h4 : v - w = 0` using `funext fun i => add_self_eq_zero.1 (congrFun h3 i)`. Conclude with `sub_eq_zero.1 h4`.
-/
theorem isUnit_of_isotropic (x y x' y' : Matrix n n ℂ) (h1 : xᴴ * x = yᴴ * y) (h2 : x'ᴴ * x - y'ᴴ * y = 1 + 1) :
    IsUnit x := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  have hd : x *ᵥ (v - w) = 0 := by rw [mulVec_sub, hvw, sub_self]
  have hy : y *ᵥ (v - w) = 0 := by
    have : (v - w) ∈ LinearMap.ker (yᴴ * y).mulVecLin := by
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← h1, ← mulVec_mulVec, hd, mulVec_zero]
    rw [ker_mulVecLin_conjTranspose_mul_self, LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
    exact this
  have h3 : (1 + 1 : Matrix n n ℂ) *ᵥ (v - w) = 0 := by
    rw [← h2, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hd, hy, mulVec_zero, mulVec_zero, sub_zero]
  rw [add_mulVec, one_mulVec] at h3
  have h4 : v - w = 0 := funext fun i => add_self_eq_zero.1 (congrFun h3 i)
  exact sub_eq_zero.1 h4

/- English proof (translation)
Establish `hH : cT σ (G⁻¹ : GL ι A).1 * dblGram e (1 : Matrix n n A) * (G⁻¹ : GL ι A).1 = dblGram e 1` using `inv_mem hG`. Establish `h1 : cT σ ((G⁻¹ : GL ι A).1.submatrix e e) * fromBlocks 1 0 0 (-1) * (G⁻¹ : GL ι A).1.submatrix e e = fromBlocks (1 : Matrix n n A) 0 0 (-1)`. Rewrite using `[← submatrix_blkMat e, show cT σ ((G⁻¹ : GL ι A).1.submatrix e e) = (cT σ (G⁻¹ : GL ι A).1).submatrix e e from rfl, submatrix_mul_equiv, submatrix_mul_equiv]`. Conclude with `congrArg (fun X => X.submatrix e e) hH`. Use `set Hs := (G⁻¹ : GL ι A).1.submatrix e e with hHs`.

Rewrite `h1` using `[← fromBlocks_toBlocks Hs]`. Simplify using `only [cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj, Matrix.mul_one] at h1`. Take `⟨e1, e2, e3, e4⟩` from `h1`. Use `set a := Hs.toBlocks₁₁`. Use `set b := Hs.toBlocks₁₂`.

Use `set c := Hs.toBlocks₂₁`. Use `set d := Hs.toBlocks₂₂`. Establish `f1 : (a.map σ)ᵀ * a = 1 + (c.map σ)ᵀ * c` using `by rw [← e1]; abel`. Establish `f2 : (a.map σ)ᵀ * b = (c.map σ)ᵀ * d` using `by rw [← sub_eq_zero, sub_eq_add_neg]; exact e2`. Establish `f3 : (b.map σ)ᵀ * a = (d.map σ)ᵀ * c` using `by rw [← sub_eq_zero, sub_eq_add_neg]; exact e3`.

Establish `f4 : (b.map σ)ᵀ * b = -1 + (d.map σ)ᵀ * d` using `by rw [← e4]; abel`. Establish `i1 : cT σ (a + b) * (a + b) = cT σ (c + d) * (c + d)`. Simplify using `only [cT_add]`. Simplify using `only [cT, Matrix.add_mul, Matrix.mul_add, f1, f2, f3, f4]`. Normalize the expressions using the abelian group laws.

Establish `i2 : cT σ (a - b) * (a + b) - cT σ (c - d) * (c + d) = 1 + 1`. Simplify using `only [cT_sub]`. Simplify using `only [cT, Matrix.sub_mul, Matrix.mul_add, f1, f2, f3, f4]`. Normalize the expressions using the abelian group laws. Establish `hX : IsUnit (a + b).det`.

Establish `hu : IsUnit ((a + b).map f)`. Use `isUnit_of_isotropic _ ((c + d).map f) ((a - b).map f) ((c - d).map f) ?_ ?_` and prove the remaining obligations. Rewrite using `[← map_cT σ f hσ, ← map_cT σ f hσ, ← Matrix.map_mul, ← Matrix.map_mul, i1]`. Rewrite using `[← map_cT σ f hσ, ← map_cT σ f hσ, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub f), i2, Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]`. Rewrite `hu` using `[Matrix.isUnit_iff_isUnit_det]`.

Establish `h' : IsUnit (f (a + b).det)` using `by rw [RingHom.map_det]; exact hu`. Conclude with `(isUnit_map_iff (RingEquiv.ofBijective f hf) _).1 h'`. Use `set X := a + b`. Use `set Y := c + d`. Use `set U := Y * X⁻¹ with hUdef`.

Establish `hU : cT σ U * U = 1`. Rewrite using `[hUdef, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hU' : U * cT σ U = 1` using `mul_eq_one_comm.1 hU`. Set `Ug : GL n A` to `⟨U, cT σ U, hU', hU⟩`.

Establish `hUg : Ug ∈ UJ σ (1 : Matrix n n A)` using `by show cT σ U * 1 * U = 1`. Rewrite using `[Matrix.mul_one, hU]`. Set `K₁ : GL ι A` to `blkGL e (1, Ug)`. Use `⟨K₁⁻¹, inv_mem ?_, inv_mem ?_, ?_⟩` and prove the remaining obligations. Use `show blkGL e (1, Ug) ∈ UJ σ (blkMat e 1 (-1))`.

Conclude with `(blkGL_mem_UJ e).2 ⟨one_mem _, by rw [UJ_neg]; exact hUg⟩`. Rewrite using `[← blkMat_one e]`. Conclude with `(blkGL_mem_UJ e).2 ⟨one_mem _, hUg⟩`. Rewrite using `[inv_inv]`. Use `mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_)` and prove the remaining obligations.

Take `⟨v, rfl⟩` from `(mem_diagSub e).1 hw`. Establish `hK : K₁.1 *ᵥ pairVec e v v = pairVec e v (U *ᵥ v)`. Rewrite using `[val_blkGL, blkMat_mulVec, Units.val_one, one_mulVec]`. Establish `hHu : (G⁻¹ : GL ι A).1 *ᵥ pairVec e (X⁻¹ *ᵥ v) (X⁻¹ *ᵥ v) = pairVec e v (U *ᵥ v)`. Rewrite using `[mulVec_pairVec, ← hHs, ← add_mulVec, ← add_mulVec, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv X hX, one_mulVec]`.

Rewrite using `[Units.val_mul, ← mulVec_mulVec, hK, ← hHu, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mulVec]`. Conclude with `(pairVec_mem_diagSub e).2 rfl`.
-/
theorem exists_mul_inv_mem (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f) (hσ : ∀ x, f (σ x) = star (f x))
    (e : n ⊕ n ≃ ι) (G : GL ι A) (hG : G ∈ UJ σ (dblGram e (1 : Matrix n n A))) :
    ∃ K ∈ UJ σ (dblGram e (1 : Matrix n n A)), K ∈ UJ σ (1 : Matrix ι ι A) ∧ G * K⁻¹ ∈ stabGL (diagSub A e) := by
  have hH : cT σ (G⁻¹ : GL ι A).1 * dblGram e (1 : Matrix n n A) * (G⁻¹ : GL ι A).1 = dblGram e 1 := inv_mem hG
  have h1 : cT σ ((G⁻¹ : GL ι A).1.submatrix e e) * fromBlocks 1 0 0 (-1) * (G⁻¹ : GL ι A).1.submatrix e e =
      fromBlocks (1 : Matrix n n A) 0 0 (-1) := by
    rw [← submatrix_blkMat e, show cT σ ((G⁻¹ : GL ι A).1.submatrix e e) = (cT σ (G⁻¹ : GL ι A).1).submatrix e e from rfl,
      submatrix_mul_equiv, submatrix_mul_equiv]
    exact congrArg (fun X => X.submatrix e e) hH
  set Hs := (G⁻¹ : GL ι A).1.submatrix e e with hHs
  rw [← fromBlocks_toBlocks Hs] at h1
  simp only [cT, fromBlocks_map, fromBlocks_transpose, fromBlocks_multiply, Matrix.mul_zero, add_zero, zero_add,
    Matrix.mul_neg, Matrix.neg_mul, fromBlocks_inj, Matrix.mul_one] at h1
  obtain ⟨e1, e2, e3, e4⟩ := h1
  set a := Hs.toBlocks₁₁
  set b := Hs.toBlocks₁₂
  set c := Hs.toBlocks₂₁
  set d := Hs.toBlocks₂₂
  have f1 : (a.map σ)ᵀ * a = 1 + (c.map σ)ᵀ * c := by rw [← e1]; abel
  have f2 : (a.map σ)ᵀ * b = (c.map σ)ᵀ * d := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e2
  have f3 : (b.map σ)ᵀ * a = (d.map σ)ᵀ * c := by rw [← sub_eq_zero, sub_eq_add_neg]; exact e3
  have f4 : (b.map σ)ᵀ * b = -1 + (d.map σ)ᵀ * d := by rw [← e4]; abel
  have i1 : cT σ (a + b) * (a + b) = cT σ (c + d) * (c + d) := by
    simp only [cT_add]
    simp only [cT, Matrix.add_mul, Matrix.mul_add, f1, f2, f3, f4]
    abel
  have i2 : cT σ (a - b) * (a + b) - cT σ (c - d) * (c + d) = 1 + 1 := by
    simp only [cT_sub]
    simp only [cT, Matrix.sub_mul, Matrix.mul_add, f1, f2, f3, f4]
    abel
  have hX : IsUnit (a + b).det := by
    have hu : IsUnit ((a + b).map f) := by
      refine isUnit_of_isotropic _ ((c + d).map f) ((a - b).map f) ((c - d).map f) ?_ ?_
      · rw [← map_cT σ f hσ, ← map_cT σ f hσ, ← Matrix.map_mul, ← Matrix.map_mul, i1]
      · rw [← map_cT σ f hσ, ← map_cT σ f hσ, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub f), i2,
          Matrix.map_add _ (map_add f), Matrix.map_one _ (map_zero f) (map_one f)]
    rw [Matrix.isUnit_iff_isUnit_det] at hu
    have h' : IsUnit (f (a + b).det) := by rw [RingHom.map_det]; exact hu
    exact (isUnit_map_iff (RingEquiv.ofBijective f hf) _).1 h'
  set X := a + b
  set Y := c + d
  set U := Y * X⁻¹ with hUdef
  have hU : cT σ U * U = 1 := by
    rw [hUdef, cT_mul]
    calc cT σ X⁻¹ * cT σ Y * (Y * X⁻¹) = cT σ X⁻¹ * (cT σ Y * Y) * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = cT σ X⁻¹ * (cT σ X * X) * X⁻¹ := by rw [i1]
      _ = cT σ (X * X⁻¹) * (X * X⁻¹) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [mul_nonsing_inv X hX, cT_one, Matrix.one_mul]
  have hU' : U * cT σ U = 1 := mul_eq_one_comm.1 hU
  let Ug : GL n A := ⟨U, cT σ U, hU', hU⟩
  have hUg : Ug ∈ UJ σ (1 : Matrix n n A) := by
    show cT σ U * 1 * U = 1
    rw [Matrix.mul_one, hU]
  let K₁ : GL ι A := blkGL e (1, Ug)
  refine ⟨K₁⁻¹, inv_mem ?_, inv_mem ?_, ?_⟩
  · show blkGL e (1, Ug) ∈ UJ σ (blkMat e 1 (-1))
    exact (blkGL_mem_UJ e).2 ⟨one_mem _, by rw [UJ_neg]; exact hUg⟩
  · rw [← blkMat_one e]
    exact (blkGL_mem_UJ e).2 ⟨one_mem _, hUg⟩
  · rw [inv_inv]
    refine mem_stabGL_diagSub.2 (keepsDiag_of_mulVec fun w hw => ?_)
    obtain ⟨v, rfl⟩ := (mem_diagSub e).1 hw
    have hK : K₁.1 *ᵥ pairVec e v v = pairVec e v (U *ᵥ v) := by
      rw [val_blkGL, blkMat_mulVec, Units.val_one, one_mulVec]
    have hHu : (G⁻¹ : GL ι A).1 *ᵥ pairVec e (X⁻¹ *ᵥ v) (X⁻¹ *ᵥ v) = pairVec e v (U *ᵥ v) := by
      rw [mulVec_pairVec, ← hHs, ← add_mulVec, ← add_mulVec, mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv X hX,
        one_mulVec]
    rw [Units.val_mul, ← mulVec_mulVec, hK, ← hHu, mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mulVec]
    exact (pairVec_mem_diagSub e).2 rfl

end Alg

end GlobalTheory.Core.Rk.IwArch

namespace GlobalTheory.Core.Rk.IwArch

section Reduce

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hM' : cT σ M.1 * Q * M.1 = Q` using `hM`. Use `show cT σ (C⁻¹ * M * C).1 * (cT σ C.1 * Q * C.1) * (C⁻¹ * M * C).1 = cT σ C.1 * Q * C.1`. Simplify using `only [Units.val_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = cT σ C.1 * Q * C.1 := by`. Rewrite using `[← cT_mul, Units.mul_inv, cT_one, Matrix.mul_one, Matrix.mul_one, hM', Matrix.mul_assoc]`.
-/
theorem conj_mem_UJ (σ : A →+* A) {Q : Matrix ι ι A} (C : GL ι A) {M : GL ι A} (hM : M ∈ UJ σ Q) :
    C⁻¹ * M * C ∈ UJ σ (cT σ C.1 * Q * C.1) := by
  have hM' : cT σ M.1 * Q * M.1 = Q := hM
  show cT σ (C⁻¹ * M * C).1 * (cT σ C.1 * Q * C.1) * (C⁻¹ * M * C).1 = cT σ C.1 * Q * C.1
  simp only [Units.val_mul, cT_mul]
  calc _ = cT σ C.1 * (cT σ M.1 * (cT σ (C⁻¹).1 * cT σ C.1) * Q * (C.1 * (C⁻¹).1) * M.1) * C.1 := by
        simp only [Matrix.mul_assoc]
    _ = cT σ C.1 * Q * C.1 := by
        rw [← cT_mul, Units.mul_inv, cT_one, Matrix.mul_one, Matrix.mul_one, hM', Matrix.mul_assoc]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Q := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem cT_inv_cancel (σ : A →+* A) (Q : Matrix ι ι A) (C : GL ι A) :
    cT σ (C⁻¹).1 * (cT σ C.1 * Q * C.1) * (C⁻¹).1 = Q := by
  calc cT σ (C⁻¹).1 * (cT σ C.1 * Q * C.1) * (C⁻¹).1 = cT σ (C.1 * (C⁻¹).1) * Q * (C.1 * (C⁻¹).1) := by
        rw [cT_mul]; simp only [Matrix.mul_assoc]
    _ = Q := by rw [Units.mul_inv, cT_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Take `⟨K, hK, hK1, hp⟩` from `hcore (C⁻¹ * g * C) (hC ▸ conj_mem_UJ σ C hg)`. Use `⟨C * K * C⁻¹, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `conj_mem_UJ σ C⁻¹ hK` as an intermediate fact. Rewrite `this` using `[← hC, cT_inv_cancel, inv_inv]`. Conclude with `this`.

Use `hK1 using 1 group` and compare the differences between its conclusion and the goal. Use `mul_mem (mul_mem hCd hp) (inv_mem hCd)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem exists_of_conj (σ : A →+* A) (e : n ⊕ n ≃ ι) {Q : Matrix ι ι A} (C : GL ι A)
    (hC : cT σ C.1 * Q * C.1 = dblGram e (1 : Matrix n n A)) (hCd : C ∈ stabGL (diagSub A e))
    (hcore : ∀ G ∈ UJ σ (dblGram e (1 : Matrix n n A)),
      ∃ K ∈ UJ σ (dblGram e (1 : Matrix n n A)), K ∈ UJ σ (1 : Matrix ι ι A) ∧ G * K⁻¹ ∈ stabGL (diagSub A e))
    (g : GL ι A) (hg : g ∈ UJ σ Q) :
    ∃ k ∈ UJ σ Q, C⁻¹ * k * C ∈ UJ σ (1 : Matrix ι ι A) ∧ g * k⁻¹ ∈ stabGL (diagSub A e) := by
  obtain ⟨K, hK, hK1, hp⟩ := hcore (C⁻¹ * g * C) (hC ▸ conj_mem_UJ σ C hg)
  refine ⟨C * K * C⁻¹, ?_, ?_, ?_⟩
  · have := conj_mem_UJ σ C⁻¹ hK
    rw [← hC, cT_inv_cancel, inv_inv] at this
    exact this
  · convert hK1 using 1
    group
  · have := mul_mem (mul_mem hCd hp) (inv_mem hCd)
    convert this using 1
    group

end Reduce

section Swap

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def projT (ε : n → Bool) : Matrix n n A := diagonal fun i => if ε i then 1 else 0

def projF (ε : n → Bool) : Matrix n n A := diagonal fun i => if ε i then 0 else 1

def sgnMat (ε : n → Bool) : Matrix n n A := diagonal fun i => if ε i then 1 else -1

variable (e : n ⊕ n ≃ ι)

def swapMat (ε : n → Bool) : Matrix ι ι A :=
  (fromBlocks (projT ε) (projF ε) (projF ε) (projT ε)).submatrix e.symm e.symm

/- English proof (translation)
Rewrite using `[swapMat, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]`. Use `congr 1`. Simplify using `only [projT, projF, diagonal_mul_diagonal, diagonal_add, fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases h : i = j <;> simp [diagonal_apply, one_apply, h] <;> cases ε j <;> simp`.
-/
theorem swapMat_mul_self (ε : n → Bool) : swapMat (A := A) e ε * swapMat e ε = 1 := by
  rw [swapMat, submatrix_mul_equiv, fromBlocks_multiply, ← blkMat_one e, blkMat]
  congr 1
  simp only [projT, projF, diagonal_mul_diagonal, diagonal_add, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases h : i = j <;> simp [diagonal_apply, one_apply, h] <;> cases ε j <;> simp

end Swap

end GlobalTheory.Core.Rk.IwArch

namespace GlobalTheory.Core.Rk.IwArch

section Swap2

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]
  (e : n ⊕ n ≃ ι)

/- English proof (translation)
Simplify using `only [cT, swapMat, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose]`. Apply the tactic sequence `congr 2 <;> simp only [projT, projF, diagonal_map (map_zero σ), diagonal_transpose, apply_ite σ, map_one, map_zero]`.
-/
theorem cT_swapMat (σ : A →+* A) (ε : n → Bool) : cT σ (swapMat (A := A) e ε) = swapMat e ε := by
  simp only [cT, swapMat, ← submatrix_map, transpose_submatrix, fromBlocks_map, fromBlocks_transpose]
  congr 2 <;> simp only [projT, projF, diagonal_map (map_zero σ), diagonal_transpose, apply_ite σ, map_one, map_zero]

/- English proof (translation)
Rewrite using `[swapMat, dblGram, dblGram, blkMat, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply, fromBlocks_multiply]`. Use `congr 1`. Simplify using `only [projT, projF, sgnMat, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, diagonal_neg, diagonal_mul_diagonal, diagonal_add, fromBlocks_inj]`. Apply the tactic sequence `refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases h : i = j <;> simp [diagonal_apply, one_apply, h] <;> cases ε j <;> simp`.
-/
theorem swapMat_dblGram (ε : n → Bool) :
    swapMat (A := A) e ε * dblGram e (sgnMat ε) * swapMat e ε = dblGram e (1 : Matrix n n A) := by
  rw [swapMat, dblGram, dblGram, blkMat, blkMat, submatrix_mul_equiv, submatrix_mul_equiv, fromBlocks_multiply,
    fromBlocks_multiply]
  congr 1
  simp only [projT, projF, sgnMat, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul,
    diagonal_neg, diagonal_mul_diagonal, diagonal_add, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j <;> by_cases h : i = j <;> simp [diagonal_apply, one_apply, h] <;> cases ε j <;> simp

/- English proof (translation)
Simplify using `[KeepsDiag, leviMat, swapMat, add_comm]`.
-/
theorem keepsDiag_swapMat (ε : n → Bool) : KeepsDiag e (swapMat (A := A) e ε) := by
  simp [KeepsDiag, leviMat, swapMat, add_comm]

def swapGL (ε : n → Bool) : GL ι A := ⟨swapMat e ε, swapMat e ε, swapMat_mul_self e ε, swapMat_mul_self e ε⟩

/- English proof (translation)
Use `show cT σ (swapMat e ε) * 1 * swapMat e ε = 1`. Rewrite using `[cT_swapMat, Matrix.mul_one, swapMat_mul_self]`.
-/
theorem swapGL_mem_UJ_one (σ : A →+* A) (ε : n → Bool) : swapGL (A := A) e ε ∈ UJ σ (1 : Matrix ι ι A) := by
  show cT σ (swapMat e ε) * 1 * swapMat e ε = 1
  rw [cT_swapMat, Matrix.mul_one, swapMat_mul_self]

/- English proof (translation)
The claim follows from `mem_stabGL_diagSub.2 (keepsDiag_swapMat e ε)`.
-/
theorem swapGL_mem_stabGL (ε : n → Bool) : swapGL (A := A) e ε ∈ stabGL (diagSub A e) :=
  mem_stabGL_diagSub.2 (keepsDiag_swapMat e ε)

end Swap2

end GlobalTheory.Core.Rk.IwArch

namespace GlobalTheory.Core.Rk.IwArch

section Frame

variable {A : Type} [CommRing A] {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Use `set B := blkGL e (b, b)`. Use `set P := swapGL (A := A) e ε`. Establish `hB : cT σ B.1 * dblGram e J * B.1 = dblGram e (sgnMat ε)`. Simplify using `only [B, val_blkGL, dblGram, cT_blkMat, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, hb]`. Establish `hC : cT σ (B * P).1 * dblGram e J * (B * P).1 = dblGram e (1 : Matrix n n A)`.

Rewrite using `[Units.val_mul, cT_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = dblGram e (1 : Matrix n n A) := by`. Rewrite using `[hB]`.

Conclude with `(congrArg (· * dblGram e (sgnMat ε) * swapMat e ε) (cT_swapMat e σ ε)).trans (swapMat_dblGram e ε)`. Establish `hCd : B * P ∈ stabGL (diagSub A e)` using `mul_mem (mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)) (swapGL_mem_stabGL e ε)`. Take `⟨k, hk, hk1, hp⟩` from `exists_of_conj σ e (B * P) hC hCd (exists_mul_inv_mem σ f hf hσ e) g hg`. Use `⟨k, hk, ?_, hp⟩` and prove the remaining obligations. Establish `hP1 : P ∈ UJ σ (1 : Matrix ι ι A)` using `swapGL_mem_UJ_one e σ ε`.

Use `mul_mem (mul_mem hP1 hk1) (inv_mem hP1)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem exists_decomp_frame (σ : A →+* A) (f : A →+* ℂ) (hf : Function.Bijective f) (hσ : ∀ x, f (σ x) = star (f x))
    (e : n ⊕ n ≃ ι) {J : Matrix n n A} (b : GL n A) (ε : n → Bool) (hb : cT σ b.1 * J * b.1 = sgnMat ε)
    (g : GL ι A) (hg : g ∈ UJ σ (dblGram e J)) :
    ∃ k ∈ UJ σ (dblGram e J), (blkGL e (b, b))⁻¹ * k * blkGL e (b, b) ∈ UJ σ (1 : Matrix ι ι A) ∧
      g * k⁻¹ ∈ stabGL (diagSub A e) := by
  set B := blkGL e (b, b)
  set P := swapGL (A := A) e ε
  have hB : cT σ B.1 * dblGram e J * B.1 = dblGram e (sgnMat ε) := by
    simp only [B, val_blkGL, dblGram, cT_blkMat, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, hb]
  have hC : cT σ (B * P).1 * dblGram e J * (B * P).1 = dblGram e (1 : Matrix n n A) := by
    rw [Units.val_mul, cT_mul]
    calc cT σ P.1 * cT σ B.1 * dblGram e J * (B.1 * P.1) = cT σ P.1 * (cT σ B.1 * dblGram e J * B.1) * P.1 := by
          simp only [Matrix.mul_assoc]
      _ = dblGram e (1 : Matrix n n A) := by
          rw [hB]; exact (congrArg (· * dblGram e (sgnMat ε) * swapMat e ε) (cT_swapMat e σ ε)).trans
            (swapMat_dblGram e ε)
  have hCd : B * P ∈ stabGL (diagSub A e) :=
    mul_mem (mem_stabGL_diagSub.2 ((keepsDiag_blkMat e).2 rfl)) (swapGL_mem_stabGL e ε)
  obtain ⟨k, hk, hk1, hp⟩ := exists_of_conj σ e (B * P) hC hCd (exists_mul_inv_mem σ f hf hσ e) g hg
  refine ⟨k, hk, ?_, hp⟩
  have hP1 : P ∈ UJ σ (1 : Matrix ι ι A) := swapGL_mem_UJ_one e σ ε
  have := mul_mem (mul_mem hP1 hk1) (inv_mem hP1)
  convert this using 1
  group

end Frame

end GlobalTheory.Core.Rk.IwArch

namespace GlobalTheory.Core.Rk.IwArch

open NumberField GlobalTheory.AdelicU
open scoped TensorProduct

/- English proof (translation)
Take `⟨τ⟩ : Nonempty (EmbOver E w)` from `inferInstance`. Establish `hσ : ∀ x, infEmb τ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ x) = star (infEmb τ x)` using `fun x => (infEmb_sigR hc τ x).symm`. Introduce `g`. Establish `hg : matHom w.Completion σ Q g ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (dblGram finSumFinEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J))`. Rewrite using `[← JR_dblGram, ← hQ]`.

Conclude with `g.2`. Take `⟨k, hk, hk1, hp⟩` from `exists_decomp_frame (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (infEmb τ) (infEmb_bijective hc τ) hσ finSumFinEquiv b ε hb _ hg`. Establish `hk' : k ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR w.Completion σ Q` using `by show k ∈ UJ _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion Q)`. Rewrite using `[hQ, JR_dblGram]`. Conclude with `hk`.

Set `kk : GArch σ Q w` to `⟨k, hk'⟩`. Use `⟨⟨g * kk⁻¹, ?_⟩, kk, ?_, by simp⟩` and prove the remaining obligations. Use `show matHom w.Completion σ Q (g * kk⁻¹) ∈ stabGL (diagSub (w.Completion ⊗[F] E) finSumFinEquiv)`. Rewrite using `[map_mul, map_inv]`. Conclude with `hp`.

Conclude with `mem_stabArch.2 hk1`.
-/
theorem hasIwasawa_KArch {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hc : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {m : ℕ} {J : Matrix (Fin m) (Fin m) E}
    {Q : Matrix (Fin (m + m)) (Fin (m + m)) E} (hQ : Q = dblGram finSumFinEquiv J) (w : InfinitePlace F)
    (b : GL (Fin m) (w.Completion ⊗[F] E)) (ε : Fin m → Bool)
    (hb : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) b.1 * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J * b.1 =
      diagonal fun i => if ε i then 1 else -1) :
    HasIwasawa σ Q (KArch σ Q w b) := by
  obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
  have hσ : ∀ x, infEmb τ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ x) = star (infEmb τ x) := fun x =>
    (infEmb_sigR hc τ x).symm
  intro g
  have hg : matHom w.Completion σ Q g ∈ UJ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ)
      (dblGram finSumFinEquiv (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion J)) := by
    rw [← JR_dblGram, ← hQ]; exact g.2
  obtain ⟨k, hk, hk1, hp⟩ := exists_decomp_frame (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (infEmb τ)
    (infEmb_bijective hc τ) hσ finSumFinEquiv b ε hb _ hg
  have hk' : k ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR w.Completion σ Q := by
    show k ∈ UJ _ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion Q)
    rw [hQ, JR_dblGram]; exact hk
  let kk : GArch σ Q w := ⟨k, hk'⟩
  refine ⟨⟨g * kk⁻¹, ?_⟩, kk, ?_, by simp⟩
  · show matHom w.Completion σ Q (g * kk⁻¹) ∈ stabGL (diagSub (w.Completion ⊗[F] E) finSumFinEquiv)
    rw [map_mul, map_inv]; exact hp
  · exact mem_stabArch.2 hk1

/- English proof (translation)
Introduce `D A a ha w`. Take `⟨ε, hε⟩` from `ha w`. Conclude with `hasIwasawa_KArch (isCMExt_host D) (gram_hdbl A) w _ ε hε`.
-/
theorem hasIwasawa_dblSp_arch : ∀ (D : D7) (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ w : InfinitePlace D.host.F, HasIwasawa D.sp.cm.sig (dblSp A).gram (KArch D.sp.cm.sig (dblSp A).gram w (Formalism.UG.bc (compInf D.host.F D.host.E w) a)) := by
  intro D A a ha w
  obtain ⟨ε, hε⟩ := ha w
  exact hasIwasawa_KArch (isCMExt_host D) (gram_hdbl A) w _ ε hε

end GlobalTheory.Core.Rk.IwArch
