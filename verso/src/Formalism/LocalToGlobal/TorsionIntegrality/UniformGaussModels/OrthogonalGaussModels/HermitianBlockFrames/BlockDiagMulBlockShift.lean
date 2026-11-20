import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.ConjMatrixApply
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

section Blocks
variable {n : Type} [Fintype n] [DecidableEq n]

def mv {R : Type*} [Zero R] [One R] (a : Fin 4) : Matrix (Fin 4 × n) (Fin 4 × n) R :=
  fun x y => if x.1 = a ∧ y.1 = 0 ∧ x.2 = y.2 then 1 else 0

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, mv]`. Distinguish the cases in `h : z.1 = a`. Rewrite using `[Fintype.sum_eq_single (0, z.2)]`. Simplify using `[h]`. Introduce `y hy`.

Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨-, h0, h2⟩`. Conclude with `hy (Prod.ext h0 h2.symm)`. Simplify using `[h]`.
-/
theorem mv_mul_apply {R : Type*} [CommRing R] (a : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((mv a : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = a then G (0, z.2) w else 0 := by
  simp only [Matrix.mul_apply, mv]
  by_cases h : z.1 = a
  · rw [Fintype.sum_eq_single (0, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, bmv0]`. Distinguish the cases in `h : z.1 = 0`. Rewrite using `[Fintype.sum_eq_single (k, z.2)]`. Simplify using `[h]`. Introduce `y hy`.

Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨-, h0, h2⟩`. Conclude with `hy (Prod.ext h0 h2.symm)`. Simplify using `[h]`.
-/
theorem blockShift_mul_apply {R : Type*} [CommRing R] (k : Fin 4) (G : Matrix (Fin 4 × n) (Fin 4 × n) R)
    (z w : Fin 4 × n) : ((bmv0 k : Matrix (Fin 4 × n) (Fin 4 × n) R) * G) z w = if z.1 = 0 then G (k, z.2) w else 0 := by
  simp only [Matrix.mul_apply, bmv0]
  by_cases h : z.1 = 0
  · rw [Fintype.sum_eq_single (k, z.2)]
    · simp [h]
    · intro y hy
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hy (Prod.ext h0 h2.symm)
  · simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Matrix.mulVec, dotProduct, mv]`. Distinguish the cases in `h : x.1 = a`. Rewrite using `[Fintype.sum_eq_single (0, x.2)]`. Simplify using `[h]`.

Introduce `z hz`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨-, h0, h2⟩`. Conclude with `hz (Prod.ext h0 h2.symm)`. Simplify using `[h]`.
-/
theorem mv_mulVec (a : Fin 4) (y : Fin 4 × n → ℂ) :
    (mv a : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = a then y (0, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, mv]
  by_cases h : x.1 = a
  · rw [Fintype.sum_eq_single (0, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [Matrix.mulVec, dotProduct, bmv0]`. Distinguish the cases in `h : x.1 = 0`. Rewrite using `[Fintype.sum_eq_single (k, x.2)]`. Simplify using `[h]`.

Introduce `z hz`. Rewrite using `[if_neg, zero_mul]`. Introduce and unpack `⟨-, h0, h2⟩`. Conclude with `hz (Prod.ext h0 h2.symm)`. Simplify using `[h]`.
-/
theorem blockShift_mulVec (k : Fin 4) (y : Fin 4 × n → ℂ) :
    (bmv0 k : Matrix _ _ ℂ).mulVec y = fun x => if x.1 = 0 then y (k, x.2) else 0 := by
  funext x
  simp only [Matrix.mulVec, dotProduct, bmv0]
  by_cases h : x.1 = 0
  · rw [Fintype.sum_eq_single (k, x.2)]
    · simp [h]
    · intro z hz
      rw [if_neg, zero_mul]
      rintro ⟨-, h0, h2⟩
      exact hz (Prod.ext h0 h2.symm)
  · simp [h]

/- English proof (translation)
Introduce `y hy`. Establish `hy' : ∀ b, slice b y ∈ Λ` using `hy`. Use `show ∀ b, slice b _ ∈ Λ`. Introduce `b`. Rewrite using `[Matrix.toLin'_apply, mv_mulVec]`.

Distinguish the cases in `h : b = a`. Substitute `h` using the available equality. Use `hy' 0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[slice]`.

Use `Λ.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[slice, h]`.
-/
theorem mv_pres (Λ : AddSubgroup (n → ℂ)) (a : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (mv a : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, mv_mulVec]
  by_cases h : b = a
  · subst h
    convert hy' 0 using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

/- English proof (translation)
Introduce `y hy`. Establish `hy' : ∀ b, slice b y ∈ Λ` using `hy`. Use `show ∀ b, slice b _ ∈ Λ`. Introduce `b`. Rewrite using `[Matrix.toLin'_apply, blockShift_mulVec]`.

Distinguish the cases in `h : b = 0`. Substitute `h` using the available equality. Use `hy' k using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[slice]`.

Use `Λ.zero_mem using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Simplify using `[slice, h]`.
-/
theorem blockShift_mapsTo (Λ : AddSubgroup (n → ℂ)) (k : Fin 4) :
    ∀ y ∈ pow4 Λ, Matrix.toLin' (bmv0 k : Matrix _ _ ℂ) y ∈ pow4 Λ := by
  intro y hy
  have hy' : ∀ b, slice b y ∈ Λ := hy
  show ∀ b, slice b _ ∈ Λ
  intro b
  rw [Matrix.toLin'_apply, blockShift_mulVec]
  by_cases h : b = 0
  · subst h
    convert hy' k using 1
    funext i
    simp [slice]
  · convert Λ.zero_mem using 1
    funext i
    simp [slice, h]

/- English proof (translation)
Use extensionality with `x y`. Distinguish the cases in `h : x.1 = y.1`. Simplify using `[bd4, Matrix.transpose_apply, h]`. Simplify using `[bd4, Matrix.transpose_apply, h, Ne.symm h]`.
-/
theorem bd4_transpose {R : Type*} [Zero R] (P : Matrix n n R) : (bd4 P).transpose = bd4 P.transpose := by
  ext x y
  by_cases h : x.1 = y.1
  · simp [bd4, Matrix.transpose_apply, h]
  · simp [bd4, Matrix.transpose_apply, h, Ne.symm h]

/- English proof (translation)
Use extensionality with `x y`. Apply the tactic sequence `by_cases h : x.1 = y.1 <;> simp [bd4, h]`.
-/
theorem bd4_smul {R : Type*} [CommRing R] (c : R) (P : Matrix n n R) : bd4 (c • P) = c • bd4 P := by
  ext x y
  by_cases h : x.1 = y.1 <;> simp [bd4, h]

/- English proof (translation)
Use extensionality with `x y`. Apply the tactic sequence `by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>`. Simplify using `[bd4, Matrix.one_apply, Prod.ext_iff, h1, h2]`.
-/
theorem bd4_one {R : Type*} [CommRing R] : bd4 (1 : Matrix n n R) = 1 := by
  ext x y
  by_cases h1 : x.1 = y.1 <;> by_cases h2 : x.2 = y.2 <;>
    simp [bd4, Matrix.one_apply, Prod.ext_iff, h1, h2]

/- English proof (translation)
Use extensionality with `x y`. Rewrite using `[blockShift_mul_apply]`. Simplify using `only [Matrix.mul_apply, bd4, bmv0]`. Rewrite using `[Fintype.sum_eq_single (0, y.2)]`. Apply the tactic sequence `by_cases h1 : x.1 = 0 <;> by_cases h2 : y.1 = k`.

Simplify using `[h1, h2]`. Establish `h2' : k ≠ y.1` using `fun h => h2 h.symm`. Simplify using `[h1, h2, h2']`. Simplify using `[h1, h2]`. Simplify using `[h1, h2]`.

Introduce `z hz`. Distinguish the cases in `hc : z.1 = 0 ∧ y.1 = k ∧ z.2 = y.2`. Conclude with `absurd (Prod.ext hc.1 hc.2.2 : z = (0, y.2)) hz`. Rewrite using `[if_neg hc, mul_zero]`.
-/
theorem blockDiag_mul_blockShift {R : Type*} [CommRing R] (P : Matrix n n R) (k : Fin 4) :
    bd4 P * bmv0 k = bmv0 k * bd4 P := by
  ext x y
  rw [blockShift_mul_apply]
  simp only [Matrix.mul_apply, bd4, bmv0]
  rw [Fintype.sum_eq_single (0, y.2)]
  · by_cases h1 : x.1 = 0 <;> by_cases h2 : y.1 = k
    · simp [h1, h2]
    · have h2' : k ≠ y.1 := fun h => h2 h.symm
      simp [h1, h2, h2']
    · simp [h1, h2]
    · simp [h1, h2]
  · intro z hz
    by_cases hc : z.1 = 0 ∧ y.1 = k ∧ z.2 = y.2
    · exact absurd (Prod.ext hc.1 hc.2.2 : z = (0, y.2)) hz
    · rw [if_neg hc, mul_zero]

/- English proof (translation)
Use `set v : Fin 4 × n → (n → ℂ) := fun j i => G (0, i) j with hv`. Establish `hspan : Submodule.span ℂ (Set.range v) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Establish `hx : x = ∑ j, (∑ k, Gi j (0, k) * x k) • v j`.

Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]`. Establish `h : ∀ k, ∑ j, G (0, i) j * Gi j (0, k) = if i = k then 1 else 0` using `fun k => by`. Use `congrFun (congrFun hG (0, i)) (0, k)` as an intermediate fact. Simplify `this` using `[Matrix.mul_apply, Matrix.one_apply]`.

Use `symm`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring`.

Use `_ = x i := by simp [h]`. Rewrite using `[hx]`. Conclude with `Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Take `⟨b, hbs, hbspan, hbli⟩` from `exists_linearIndependent ℂ (Set.range v)`. Rewrite `hbspan` using `[hspan]`.

Set `B` to `Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))`. Set `e` to `B.indexEquiv (Pi.basisFun ℂ n)`. Establish `hmem : ∀ i : n, ∃ j, v j = ((e.symm i : b) : n → ℂ)` using `fun i => hbs (e.symm i).2`. Use `choose w hw using hmem`. Use `⟨w, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.linearIndependent_cols_iff_isUnit]`. Establish `hfun : (Matrix.of fun i j => G (0, i) (w j)).col = (fun x : b => (x : n → ℂ)) ∘ e.symm`. Use function extensionality and compare the values at `j i`. Simplify using `[Matrix.col, Matrix.transpose_apply, ← hw j, hv]`. Rewrite using `[hfun]`.

Conclude with `hbli.comp _ e.symm.injective`.
-/
theorem exists_cols (G Gi : Matrix (Fin 4 × n) (Fin 4 × n) ℂ) (hG : G * Gi = 1) :
    ∃ w : n → Fin 4 × n, IsUnit (Matrix.of fun i j => G (0, i) (w j)) := by
  classical
  set v : Fin 4 × n → (n → ℂ) := fun j i => G (0, i) j with hv
  have hspan : Submodule.span ℂ (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x = ∑ j, (∑ k, Gi j (0, k) * x k) • v j := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hv]
      have h : ∀ k, ∑ j, G (0, i) j * Gi j (0, k) = if i = k then 1 else 0 := fun k => by
        have := congrFun (congrFun hG (0, i)) (0, k)
        simpa [Matrix.mul_apply, Matrix.one_apply] using this
      symm
      calc ∑ j, (∑ k, Gi j (0, k) * x k) * G (0, i) j
          = ∑ k, (∑ j, G (0, i) j * Gi j (0, k)) * x k := by
            simp_rw [Finset.sum_mul]
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
        _ = x i := by simp [h]
    rw [hx]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent ℂ (Set.range v)
  rw [hspan] at hbspan
  let B := Module.Basis.mk hbli (le_of_eq (by rw [Subtype.range_coe, hbspan]))
  let e := B.indexEquiv (Pi.basisFun ℂ n)
  have hmem : ∀ i : n, ∃ j, v j = ((e.symm i : b) : n → ℂ) := fun i => hbs (e.symm i).2
  choose w hw using hmem
  refine ⟨w, ?_⟩
  rw [← Matrix.linearIndependent_cols_iff_isUnit]
  have hfun : (Matrix.of fun i j => G (0, i) (w j)).col =
      (fun x : b => (x : n → ℂ)) ∘ e.symm := by
    funext j i
    simp [Matrix.col, Matrix.transpose_apply, ← hw j, hv]
  rw [hfun]
  exact hbli.comp _ e.symm.injective

end Blocks

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
