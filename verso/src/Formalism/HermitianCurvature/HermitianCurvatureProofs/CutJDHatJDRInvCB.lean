import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.DetTransposeApply

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open Matrix

noncomputable section

namespace RInvCB

variable {k r : ℕ}

def Mr (k r : ℕ) (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  Matrix.of fun q => if h : q.val ≤ r then R0 q else v ⟨q.val - r - 1, by omega⟩

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[Mr, h]`.
-/
theorem Mr_le (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    {q : Fin (2 * r + k + 1)} (h : q.val ≤ r) : Mr k r R0 v q = R0 q := by
  funext j; simp [Mr, h]

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `[Mr, h]`.
-/
theorem Mr_gt (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    {q : Fin (2 * r + k + 1)} (h : ¬ q.val ≤ r) : Mr k r R0 v q = v ⟨q.val - r - 1, by omega⟩ := by
  funext j; simp [Mr, h]

def iota (k r : ℕ) (l : Fin (r + k)) : Fin (2 * r + k + 1) := ⟨r + 1 + l.val, by omega⟩

/- English proof (translation)
Establish `h : ¬ (iota k r l).val ≤ r` using `by simp only [iota]; omega`. Use function extensionality and compare the values at `j`. Simplify using `only [Mr, Matrix.of_apply]`. Rewrite using `[dif_neg h]`. Use `congr 2`.

Simplify using `only [iota]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Mr_iota (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    (l : Fin (r + k)) : Mr k r R0 v (iota k r l) = v l := by
  have h : ¬ (iota k r l).val ≤ r := by simp only [iota]; omega
  funext j
  simp only [Mr, Matrix.of_apply]
  rw [dif_neg h]
  congr 2
  simp only [iota]; omega

def fEq (k r : ℕ) : Fin (r + k) ≃ {q : Fin (2 * r + k + 1) // r < q.val} where
  toFun l := ⟨iota k r l, by simp only [iota]; omega⟩
  invFun q := ⟨q.1.val - r - 1, by have := q.1.isLt; have := q.2; omega⟩
  left_inv l := by ext; simp only [iota]; omega
  right_inv q := by ext; simp only [iota]; have := q.2; omega

/- English proof (translation)
Use extensionality with `q j`. Simplify using `only [Matrix.submatrix_apply, id]`. Distinguish the cases in `hq : r < q.val`. Establish `e : q = ((fEq k r) ((fEq k r).symm ⟨q, hq⟩) : Fin (2 * r + k + 1))` using `by simp`. Rewrite using `[e, Equiv.Perm.extendDomain_apply_image]`.

Simplify using `only [fEq, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]`. Rewrite using `[Mr_iota, Mr_iota]`. Both sides reduce to the same expression. Establish `e` using `Equiv.Perm.extendDomain_apply_not_subtype τ (fEq k r) hq`. Simplify using `only [e]`.

Establish `h : q.val ≤ r` using `by omega`. Simplify using `[Mr, dif_pos h]`.
-/
theorem Mr_perm (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    (τ : Equiv.Perm (Fin (r + k))) :
    Mr k r R0 (v ∘ τ) = (Mr k r R0 v).submatrix (τ.extendDomain (fEq k r)) id := by
  ext q j
  simp only [Matrix.submatrix_apply, id]
  by_cases hq : r < q.val
  · have e : q = ((fEq k r) ((fEq k r).symm ⟨q, hq⟩) : Fin (2 * r + k + 1)) := by simp
    rw [e, Equiv.Perm.extendDomain_apply_image]
    simp only [fEq, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]
    rw [Mr_iota, Mr_iota]
    rfl
  · have e := Equiv.Perm.extendDomain_apply_not_subtype τ (fEq k r) hq
    simp only [e]
    have h : q.val ≤ r := by omega
    simp [Mr, dif_pos h]

/- English proof (translation)
Rewrite using `[Mr_perm, Matrix.det_permute, Equiv.Perm.sign_extendDomain]`.
-/
theorem det_Mr_perm (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    (τ : Equiv.Perm (Fin (r + k))) :
    (Mr k r R0 (v ∘ τ)).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Mr k r R0 v).det := by
  rw [Mr_perm, Matrix.det_permute, Equiv.Perm.sign_extendDomain]

/- English proof (translation)
Use `Matrix.det_zero_of_row_eq (i := iota k r i) (j := iota k r j) ?_ ?_` and prove the remaining obligations. Introduce `h`. Apply `hij` to reduce the goal to its premises. Use `ext`. Use `congrArg Fin.val h` as an intermediate fact.

Simplify using `[iota] at this`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Mr_iota, Mr_iota, hv]`.
-/
theorem det_Mr_zero (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    {i j : Fin (r + k)} (hij : i ≠ j) (hv : v i = v j) : (Mr k r R0 v).det = 0 := by
  refine Matrix.det_zero_of_row_eq (i := iota k r i) (j := iota k r j) ?_ ?_
  · intro h; apply hij; ext; have := congrArg Fin.val h; simp [iota] at this; omega
  · rw [Mr_iota, Mr_iota, hv]

end RInvCB

namespace RInvCB

variable {k r : ℕ}

def PhiJ (k r : ℕ) (J : Fin (r + k) → Fin (2 * r + k + 1)) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if h : q.val ≤ r then q else J ⟨q.val - r - 1, by omega⟩

/- English proof (translation)
Establish `hinj : Function.Injective (iota k r)`. Introduce `a b h`. Use `ext`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [iota] at this`.

Use linear arithmetic over natural numbers and integers. Establish `hm` using `Finset.prod_map Finset.univ ⟨iota k r, hinj⟩ f`. Simplify using `only [Function.Embedding.coeFn_mk] at hm`. Rewrite using `[← hm]`. Use `symm`.

Use `Finset.prod_subset (Finset.subset_univ _) (fun q _ hq => hf q ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Apply `hq` to reduce the goal to its premises. Rewrite using `[Finset.mem_map]`. Use `⟨⟨q.val - r - 1, by omega⟩, Finset.mem_univ _, ?_⟩` and prove the remaining obligations.

Use `ext`. Simplify using `only [Function.Embedding.coeFn_mk, iota]`. Use linear arithmetic over natural numbers and integers.
-/
theorem prod_iota (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ q : Fin (2 * r + k + 1), q.val ≤ r → f q = 1) :
    ∏ q, f q = ∏ l : Fin (r + k), f (iota k r l) := by
  classical
  have hinj : Function.Injective (iota k r) := by
    intro a b h; ext; have := congrArg Fin.val h; simp only [iota] at this; omega
  have hm := Finset.prod_map Finset.univ ⟨iota k r, hinj⟩ f
  simp only [Function.Embedding.coeFn_mk] at hm
  rw [← hm]
  symm
  refine Finset.prod_subset (Finset.subset_univ _) (fun q _ hq => hf q ?_)
  by_contra h
  apply hq
  rw [Finset.mem_map]
  refine ⟨⟨q.val - r - 1, by omega⟩, Finset.mem_univ _, ?_⟩
  ext; simp only [Function.Embedding.coeFn_mk, iota]; omega

/- English proof (translation)
Use `set A : Fin (2 * r + k + 1) → Finset (Fin (2 * r + k + 1)) := fun q => if q.val ≤ r then {q} else Finset.univ with hA`. Use `set g : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Fin (2 * r + k + 1) → ℂ) := fun q j => if h : q.val ≤ r then R0 q else c ⟨q.val - r - 1, by omega⟩ j • bvec j with hg`. Establish `e1 : (Mr k r R0 (fun l => ∑ j, c l j • bvec j) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) = fun q => ∑ j ∈ A q, g q j`. Use function extensionality and compare the values at `q`. Distinguish the cases in `h : q.val ≤ r`.

Rewrite using `[Mr_le _ _ h]`. Simplify using `[hA, hg, h]`. Rewrite using `[Mr_gt _ _ h]`. Simplify using `[hA, hg, h]`. Establish `hmul` using `(Matrix.detRowAlternating (n := Fin (2 * r + k + 1)) (R := ℂ)).toMultilinearMap.map_sum_finset g A`.

Establish `e2 : (Mr k r R0 (fun l => ∑ j, c l j • bvec j)).det = ∑ ρ ∈ Fintype.piFinset A, Matrix.detRowAlternating (fun q => g q (ρ q))`. Rewrite using `[Matrix.det, e1]`. Conclude with `hmul`. Rewrite using `[e2]`. Use `Finset.sum_nbij' (fun ρ l => ρ (iota k r l)) (PhiJ k r) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations.

Introduce `ρ _`. Conclude with `Finset.mem_univ _`. Introduce `J _`. Rewrite using `[Fintype.mem_piFinset]`. Introduce `q`.

Distinguish the cases in `h : q.val ≤ r`. Simplify using `[hA, PhiJ, h]`. Simplify using `[hA, h]`. Introduce `ρ hρ`. Rewrite `hρ` using `[Fintype.mem_piFinset]`.

Use function extensionality and compare the values at `q`. Distinguish the cases in `h : q.val ≤ r`. Use `hρ q` as an intermediate fact. Simplify using `only [hA, h, if_true, Finset.mem_singleton] at this`. Simplify using `[PhiJ, h, this]`.

Simplify using `only [PhiJ, dif_neg h]`. Use `congr 1`. Use `ext`. Simplify using `only [iota]`. Use linear arithmetic over natural numbers and integers.

Introduce `J _`. Use function extensionality and compare the values at `l`. Establish `h : ¬ (iota k r l).val ≤ r` using `by simp only [iota]; omega`. Simplify using `only [PhiJ, dif_neg h]`. Use `congr 1`.

Use `ext`. Simplify using `only [iota]`. Use linear arithmetic over natural numbers and integers. Introduce `ρ hρ`. Rewrite `hρ` using `[Fintype.mem_piFinset]`.

Use `set J : Fin (r + k) → Fin (2 * r + k + 1) := fun l => ρ (iota k r l) with hJ`. Use `set cf : Fin (2 * r + k + 1) → ℂ := fun q => if h : q.val ≤ r then 1 else c ⟨q.val - r - 1, by omega⟩ (ρ q) with hcf`. Establish `e3 : (fun q => g q (ρ q)) = fun q => cf q • (Mr k r R0 (fun l => bvec (J l))) q`. Use function extensionality and compare the values at `q`. Distinguish the cases in `h : q.val ≤ r`.

Rewrite using `[Mr_le _ _ h]`. Simplify using `[hg, hcf, h]`. Establish `hq : ρ q = J ⟨q.val - r - 1, by omega⟩`. Simplify using `only [hJ]`. Use `congr 1`.

Use `ext`. Simplify using `only [iota]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Mr_gt _ _ h]`. Simplify using `only [hg, hcf, dif_neg h]`.

Rewrite using `[hq]`. Rewrite using `[e3]`. Establish `e4` using `(Matrix.detRowAlternating (n := Fin (2 * r + k + 1)) (R := ℂ)).toMultilinearMap.map_smul_univ cf (Mr k r R0 (fun l => bvec (J l)))`. Simplify using `only [AlternatingMap.coe_multilinearMap] at e4`. Rewrite using `[e4, smul_eq_mul, ← Matrix.det]`.

Use `congr 1`. Rewrite using `[prod_iota cf (fun q h => by simp [hcf, h])]`. Use `Finset.prod_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Establish `h : ¬ (iota k r l).val ≤ r` using `by simp only [iota]; omega`. Simplify using `only [hcf, dif_neg h, hJ]`.

Use `congr 1`. Use `ext`. Simplify using `only [iota]`. Use linear arithmetic over natural numbers and integers.
-/
theorem det_Mr_expand (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)
    (c : Fin (r + k) → Fin (2 * r + k + 1) → ℂ) :
    (Mr k r R0 (fun l => ∑ j, c l j • bvec j)).det =
      ∑ J : Fin (r + k) → Fin (2 * r + k + 1), (∏ l, c l (J l)) * (Mr k r R0 (fun l => bvec (J l))).det := by
  classical
  set A : Fin (2 * r + k + 1) → Finset (Fin (2 * r + k + 1)) := fun q => if q.val ≤ r then {q} else Finset.univ
    with hA
  set g : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → (Fin (2 * r + k + 1) → ℂ) := fun q j =>
    if h : q.val ≤ r then R0 q else c ⟨q.val - r - 1, by omega⟩ j • bvec j with hg
  have e1 : (Mr k r R0 (fun l => ∑ j, c l j • bvec j) : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) =
      fun q => ∑ j ∈ A q, g q j := by
    funext q
    by_cases h : q.val ≤ r
    · rw [Mr_le _ _ h]; simp [hA, hg, h]
    · rw [Mr_gt _ _ h]; simp [hA, hg, h]
  have hmul := (Matrix.detRowAlternating (n := Fin (2 * r + k + 1)) (R := ℂ)).toMultilinearMap.map_sum_finset g A
  have e2 : (Mr k r R0 (fun l => ∑ j, c l j • bvec j)).det = ∑ ρ ∈ Fintype.piFinset A,
      Matrix.detRowAlternating (fun q => g q (ρ q)) := by
    rw [Matrix.det, e1]
    exact hmul
  rw [e2]
  refine Finset.sum_nbij' (fun ρ l => ρ (iota k r l)) (PhiJ k r) ?_ ?_ ?_ ?_ ?_
  · intro ρ _; exact Finset.mem_univ _
  · intro J _
    rw [Fintype.mem_piFinset]
    intro q
    by_cases h : q.val ≤ r
    · simp [hA, PhiJ, h]
    · simp [hA, h]
  · intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ
    funext q
    by_cases h : q.val ≤ r
    · have := hρ q
      simp only [hA, h, if_true, Finset.mem_singleton] at this
      simp [PhiJ, h, this]
    · simp only [PhiJ, dif_neg h]
      congr 1; ext; simp only [iota]; omega
  · intro J _
    funext l
    have h : ¬ (iota k r l).val ≤ r := by simp only [iota]; omega
    simp only [PhiJ, dif_neg h]
    congr 1; ext; simp only [iota]; omega
  · intro ρ hρ
    rw [Fintype.mem_piFinset] at hρ
    set J : Fin (r + k) → Fin (2 * r + k + 1) := fun l => ρ (iota k r l) with hJ
    set cf : Fin (2 * r + k + 1) → ℂ := fun q =>
      if h : q.val ≤ r then 1 else c ⟨q.val - r - 1, by omega⟩ (ρ q) with hcf
    have e3 : (fun q => g q (ρ q)) = fun q => cf q • (Mr k r R0 (fun l => bvec (J l))) q := by
      funext q
      by_cases h : q.val ≤ r
      · rw [Mr_le _ _ h]; simp [hg, hcf, h]
      · have hq : ρ q = J ⟨q.val - r - 1, by omega⟩ := by
          simp only [hJ]; congr 1; ext; simp only [iota]; omega
        rw [Mr_gt _ _ h]
        simp only [hg, hcf, dif_neg h]
        rw [hq]
    rw [e3]
    have e4 := (Matrix.detRowAlternating (n := Fin (2 * r + k + 1)) (R := ℂ)).toMultilinearMap.map_smul_univ cf
      (Mr k r R0 (fun l => bvec (J l)))
    simp only [AlternatingMap.coe_multilinearMap] at e4
    rw [e4, smul_eq_mul, ← Matrix.det]
    congr 1
    rw [prod_iota cf (fun q h => by simp [hcf, h])]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    have h : ¬ (iota k r l).val ≤ r := by simp only [iota]; omega
    simp only [hcf, dif_neg h, hJ]
    congr 1; ext; simp only [iota]; omega

/- English proof (translation)
Rewrite using `[det_Mr_expand]`. Establish `hF : ∀ (d : Fin (r + k) → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin (r + k))), (Mr k r R0 (fun l => bvec ((d ∘ τ) l))).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Mr k r R0 (fun l => bvec (d l))).det`. Introduce `d τ`. Conclude with `det_Mr_perm R0 (fun l => bvec (d l)) τ`. Establish `hF0 : ∀ d : Fin (r + k) → Fin (2 * r + k + 1), ¬ Function.Injective d → (Mr k r R0 (fun l => bvec (d l))).det = 0`.

Introduce `d hd`. Take `⟨i, j, hne, hij⟩` from `AAInvW.not_inj hd`. Conclude with `det_Mr_zero R0 _ hne (by simp [hij])`. Establish `hgr` using `AAInvW.grouping (A := ℂ) (fun i : Fin (2 * r + k + 1) => i.val) Fin.val_injective (fun d => (Mr k r R0 (fun l => bvec (d l))).det) hF hF0 (fun J => ∏ l, c l (J l))`. Simplify using `only [smul_eq_mul] at hgr`.

Rewrite using `[hgr, jSetR, Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun C _ => ?_)` and prove the remaining obligations. Establish `hiff` using `AAInvW.strictMono_val_iff C`. Distinguish the cases in `hC : StrictMono C`. Rewrite using `[if_pos (hiff.mpr hC), if_pos hC]`.

Use `congr 1`. Rewrite using `[AAInvW.det_transpose_apply]`. Both sides reduce to the same expression. Rewrite using `[if_neg (fun h => hC (hiff.mp h)), if_neg hC]`.
-/
theorem det_Mr_sum (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)
    (c : Fin (r + k) → Fin (2 * r + k + 1) → ℂ) :
    (Mr k r R0 (fun l => ∑ j, c l j • bvec j)).det =
      ∑ J ∈ jSetR k r, (Matrix.of fun l l' => c l (J l')).det * (Mr k r R0 (fun l => bvec (J l))).det := by
  classical
  rw [det_Mr_expand]
  have hF : ∀ (d : Fin (r + k) → Fin (2 * r + k + 1)) (τ : Equiv.Perm (Fin (r + k))),
      (Mr k r R0 (fun l => bvec ((d ∘ τ) l))).det =
        ((Equiv.Perm.sign τ : ℤ) : ℂ) * (Mr k r R0 (fun l => bvec (d l))).det := by
    intro d τ
    exact det_Mr_perm R0 (fun l => bvec (d l)) τ
  have hF0 : ∀ d : Fin (r + k) → Fin (2 * r + k + 1), ¬ Function.Injective d →
      (Mr k r R0 (fun l => bvec (d l))).det = 0 := by
    intro d hd
    obtain ⟨i, j, hne, hij⟩ := AAInvW.not_inj hd
    exact det_Mr_zero R0 _ hne (by simp [hij])
  have hgr := AAInvW.grouping (A := ℂ) (fun i : Fin (2 * r + k + 1) => i.val) Fin.val_injective
    (fun d => (Mr k r R0 (fun l => bvec (d l))).det) hF hF0 (fun J => ∏ l, c l (J l))
  simp only [smul_eq_mul] at hgr
  rw [hgr, jSetR, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun C _ => ?_)
  have hiff := AAInvW.strictMono_val_iff C
  by_cases hC : StrictMono C
  · rw [if_pos (hiff.mpr hC), if_pos hC]
    congr 1
    rw [AAInvW.det_transpose_apply]
    rfl
  · rw [if_neg (fun h => hC (hiff.mp h)), if_neg hC]

end RInvCB

namespace RInvCB

variable {k r : ℕ}

/- English proof (translation)
Use extensionality with `q j`. Distinguish the cases in `h : q.val ≤ r`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct, Mr, h]`. Simplify using `[Matrix.mul_apply, Matrix.vecMul, dotProduct, Mr, h]`.
-/
theorem Mr_mul (R0 : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ)
    (S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    Mr k r R0 v * S = Mr k r (fun q => R0 q ᵥ* S) (fun l => v l ᵥ* S) := by
  ext q j
  by_cases h : q.val ≤ r
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Mr, h]
  · simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Mr, h]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `[Matrix.vecMul, dotProduct, bvec, Pi.single_apply, Finset.sum_apply]`.
-/
theorem bvec_vecMul (i : Fin (2 * r + k + 1)) (S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    bvec i ᵥ* S = ∑ j, S i j • bvec j := by
  funext x
  simp [Matrix.vecMul, dotProduct, bvec, Pi.single_apply, Finset.sum_apply]

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.Qx2.hpk_sq'`.
-/
theorem hpk_sq : Hpk k r * Hpk k r = 1 := Formalism.FourierDecayAlt.P.Qx2.hpk_sq'

/- English proof (translation)
Establish `h : Sᴴ * Hpk k r * S = Hpk k r` using `hS`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_left_inv {S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hS : S ∈ UH (Hpk k r)) :
    (Hpk k r * Sᴴ * Hpk k r) * S = 1 := by
  have h : Sᴴ * Hpk k r * S = Hpk k r := hS
  calc (Hpk k r * Sᴴ * Hpk k r) * S = Hpk k r * (Sᴴ * Hpk k r * S) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, hpk_sq]

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (uh_left_inv hS)`.
-/
theorem uh_inv_eq' {S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hS : S ∈ UH (Hpk k r)) :
    S⁻¹ = Hpk k r * Sᴴ * Hpk k r := Matrix.inv_eq_left_inv (uh_left_inv hS)

/- English proof (translation)
Establish `h` using `congrArg Matrix.det (uh_left_inv hS)`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`. Conclude with `IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h)`.
-/
theorem uh_isUnit {S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hS : S ∈ UH (Hpk k r)) :
    IsUnit S.det := by
  have h := congrArg Matrix.det (uh_left_inv hS)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h)

/- English proof (translation)
The claim follows from `Matrix.nonsing_inv_mul S (uh_isUnit hS)`.
-/
theorem inv_mul_self' {S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hS : S ∈ UH (Hpk k r)) :
    S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S (uh_isUnit hS)

/- English proof (translation)
Rewrite using `[← Matrix.det_mul, inv_mul_self' hS, Matrix.det_one]`.
-/
theorem det_inv_mul {S : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hS : S ∈ UH (Hpk k r)) :
    (S⁻¹).det * S.det = 1 := by
  rw [← Matrix.det_mul, inv_mul_self' hS, Matrix.det_one]

def C0 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : q.val < r then ginvH k r g *ᵥ bvec (eI k r ⟨r - 1 - q.val, by omega⟩) else ginvH k r g *ᵥ z

/- English proof (translation)
Unfold `beJ`. Rewrite using `[← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `q p`. Simplify using `only [Matrix.transpose_apply, Matrix.of_apply]`.

Distinguish the cases in `h1 : q.val < r`. Establish `h : q.val ≤ r` using `by omega`. Simplify using `[Mr, C0, colR, h1, h]`. Distinguish the cases in `h2 : q.val = r`. Establish `h : q.val ≤ r` using `by omega`.

Simplify using `[Mr, C0, colR, h1, h2, h]`. Establish `h : ¬ q.val ≤ r` using `by omega`. Simplify using `[Mr, C0, colR, h1, h2, h]`.
-/
theorem beJ_eq (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    beJ k r z g J = (Mr k r (C0 k r z g) (fun l => bvec (J l))).det := by
  unfold beJ
  rw [← Matrix.det_transpose]
  congr 1
  ext q p
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  by_cases h1 : q.val < r
  · have h : q.val ≤ r := by omega
    simp [Mr, C0, colR, h1, h]
  · by_cases h2 : q.val = r
    · have h : q.val ≤ r := by omega
      simp [Mr, C0, colR, h1, h2, h]
    · have h : ¬ q.val ≤ r := by omega
      simp [Mr, C0, colR, h1, h2, h]

def A0 (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  fun q => if h : p.val < r then herm (Hpk k r) (g *ᵥ bvec q) (bvec (eI k r ⟨p.val, h⟩))
    else herm (Hpk k r) (g *ᵥ bvec q) z

/- English proof (translation)
Unfold `alJ`. Use `congr 1`. Use extensionality with `p q`. Simplify using `only [Matrix.of_apply]`. Distinguish the cases in `h1 : p.val < r`.

Establish `h : p.val ≤ r` using `by omega`. Simplify using `[Mr, A0, rowV, h1, h]`. Distinguish the cases in `h2 : p.val = r`. Establish `h : p.val ≤ r` using `by omega`. Simplify using `[Mr, A0, rowV, h1, h2, h]`.

Establish `h : ¬ p.val ≤ r` using `by omega`. Simplify using `[Mr, A0, rowV, h1, h2, h, bvec, Pi.single_apply]`.
-/
theorem alJ_eq (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    alJ k r z g J = (Mr k r (A0 k r z g) (fun l => bvec (J l))).det := by
  unfold alJ
  congr 1
  ext p q
  simp only [Matrix.of_apply]
  by_cases h1 : p.val < r
  · have h : p.val ≤ r := by omega
    simp [Mr, A0, rowV, h1, h]
  · by_cases h2 : p.val = r
    · have h : p.val ≤ r := by omega
      simp [Mr, A0, rowV, h1, h2, h]
    · have h : ¬ p.val ≤ r := by omega
      simp [Mr, A0, rowV, h1, h2, h, bvec, Pi.single_apply]

/- English proof (translation)
Establish `hcol : s *ᵥ bvec c = ∑ d, s d c • bvec d`. Use function extensionality and compare the values at `i`. Simplify using `[Matrix.mulVec, dotProduct, bvec, Pi.single_apply, Finset.sum_apply]`. Rewrite using `[← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_sum]`. Unfold `herm`.

Rewrite using `[Matrix.mulVec_sum, dotProduct_sum]`. Use `Finset.sum_congr rfl (fun d _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]`.
-/
theorem herm_mul_bvec' (H g s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (c : Fin (2 * r + k + 1))
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm H ((g * s) *ᵥ bvec c) w = ∑ d, s d c * herm H (g *ᵥ bvec d) w := by
  have hcol : s *ᵥ bvec c = ∑ d, s d c • bvec d := by
    funext i
    simp [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, Finset.sum_apply]
  rw [← Matrix.mulVec_mulVec, hcol, Matrix.mulVec_sum]
  unfold herm
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

/- English proof (translation)
Use function extensionality and compare the values at `p q`. Simplify using `only [A0, Matrix.vecMul, dotProduct]`. Use `split_ifs`. Rewrite using `[herm_mul_bvec']`. Conclude with `Finset.sum_congr rfl (fun d _ => mul_comm _ _)`.

Rewrite using `[herm_mul_bvec']`. Conclude with `Finset.sum_congr rfl (fun d _ => mul_comm _ _)`.
-/
theorem besselModelTransportMatrix_mul_right (z : Fin (2 * r + k + 1) → ℂ) (g S : Q.Mx k r) :
    A0 k r z (g * S) = fun p => A0 k r z g p ᵥ* S := by
  funext p q
  simp only [A0, Matrix.vecMul, dotProduct]
  split_ifs
  · rw [herm_mul_bvec']; exact Finset.sum_congr rfl (fun d _ => mul_comm _ _)
  · rw [herm_mul_bvec']; exact Finset.sum_congr rfl (fun d _ => mul_comm _ _)

/- English proof (translation)
Unfold `ginvH`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hpk_sq]`. Simplify using `only [Matrix.mul_one, Matrix.mul_assoc]`.

Use `_ = Hpk k r * Sᴴ * Hpk k r * (Hpk k r * gᴴ * Hpk k r) := by simp only [Matrix.mul_assoc]`.
-/
theorem ginvH_mul (g S : Q.Mx k r) : ginvH k r (g * S) = ginvH k r S * ginvH k r g := by
  unfold ginvH
  rw [Matrix.conjTranspose_mul]
  calc Hpk k r * (Sᴴ * gᴴ) * Hpk k r = Hpk k r * Sᴴ * (Hpk k r * Hpk k r) * gᴴ * Hpk k r := by
        rw [hpk_sq]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Hpk k r * Sᴴ * Hpk k r * (Hpk k r * gᴴ * Hpk k r) := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Establish `e : ginvH k r S = S⁻¹` using `by rw [uh_inv_eq' hS]; rfl`. Use function extensionality and compare the values at `q`. Simplify using `only [C0, ginvH_mul, e, Matrix.vecMul_transpose]`. Apply the tactic sequence `split_ifs <;> rw [Matrix.mulVec_mulVec]`.
-/
theorem coordinate_matrix_mul_unitary (z : Fin (2 * r + k + 1) → ℂ) (g S : Q.Mx k r) (hS : S ∈ UH (Hpk k r)) :
    C0 k r z (g * S) = fun q => C0 k r z g q ᵥ* (S⁻¹)ᵀ := by
  have e : ginvH k r S = S⁻¹ := by rw [uh_inv_eq' hS]; rfl
  funext q
  simp only [C0, ginvH_mul, e, Matrix.vecMul_transpose]
  split_ifs <;> rw [Matrix.mulVec_mulVec]

end RInvCB

open RInvCB in
/- English proof (translation)
Introduce `k r z g S _ hS c`. Establish `hS' : S ∈ UH (Hpk k r)` using `hS`. Establish `e1 : Mr k r (A0 k r z (g * S)) (fun l => bvec (c l)) = Mr k r (A0 k r z g) (fun l => ∑ j, (S⁻¹) (c l) j • bvec j) * S`. Rewrite using `[Mr_mul, besselModelTransportMatrix_mul_right]`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Rewrite using `[← bvec_vecMul, Matrix.vecMul_vecMul, inv_mul_self' hS', Matrix.vecMul_one]`. Rewrite using `[alJ_eq, e1, Matrix.det_mul, det_Mr_sum]`. Establish `e2 : ∀ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det = (Matrix.of fun l l' => (S⁻¹) (c l) (J l')).det * (Mr k r (A0 k r z g) (fun l => bvec (J l))).det`. Introduce `J _`.

Rewrite using `[alJ_eq, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl e2]`. Establish `key : ∀ X : ℂ, X = (S⁻¹).det * (X * S.det)` using `fun X => by`. Rewrite using `[mul_comm X, ← mul_assoc, det_inv_mul hS', one_mul]`.

Conclude with `key _`.
-/
theorem inverse_alpha_minus_holds : RInvAlphaM := by
  intro k r z g S _ hS c
  have hS' : S ∈ UH (Hpk k r) := hS
  have e1 : Mr k r (A0 k r z (g * S)) (fun l => bvec (c l)) =
      Mr k r (A0 k r z g) (fun l => ∑ j, (S⁻¹) (c l) j • bvec j) * S := by
    rw [Mr_mul, besselModelTransportMatrix_mul_right]
    congr 1
    funext l
    rw [← bvec_vecMul, Matrix.vecMul_vecMul, inv_mul_self' hS', Matrix.vecMul_one]
  rw [alJ_eq, e1, Matrix.det_mul, det_Mr_sum]
  have e2 : ∀ J ∈ jSetR k r, alJ k r z g J * ((S⁻¹).submatrix c J).det =
      (Matrix.of fun l l' => (S⁻¹) (c l) (J l')).det * (Mr k r (A0 k r z g) (fun l => bvec (J l))).det := by
    intro J _
    rw [alJ_eq, mul_comm]
    rfl
  rw [Finset.sum_congr rfl e2]
  have key : ∀ X : ℂ, X = (S⁻¹).det * (X * S.det) := fun X => by
    rw [mul_comm X, ← mul_assoc, det_inv_mul hS', one_mul]
  exact key _

open RInvCB in
/- English proof (translation)
Introduce `k r z g S _ hS d`. Establish `hS' : S ∈ UH (Hpk k r)` using `hS`. Establish `e1 : Mr k r (C0 k r z (g * S)) (fun l => bvec (d l)) = Mr k r (C0 k r z g) (fun l => ∑ j, S j (d l) • bvec j) * (S⁻¹)ᵀ`. Rewrite using `[Mr_mul, coordinate_matrix_mul_unitary z g S hS']`. Use `congr 1`.

Use function extensionality and compare the values at `l`. Establish `: (∑ j, S j (d l) • bvec j : Fin (2 * r + k + 1) → ℂ) = bvec (d l) ᵥ* Sᵀ`. Rewrite using `[bvec_vecMul]`. Both sides reduce to the same expression. Rewrite using `[this, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, inv_mul_self' hS', Matrix.transpose_one, Matrix.vecMul_one]`.

Rewrite using `[beJ_eq z (g * S), e1, Matrix.det_mul, det_Mr_sum, Matrix.det_transpose]`. Establish `e2 : ∀ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det = (Matrix.of fun l l' => S (J l') (d l)).det * (Mr k r (C0 k r z g) (fun l => bvec (J l))).det`. Introduce `J _`. Rewrite using `[beJ_eq, mul_comm]`. Use `congr 1`.

Rewrite using `[← Matrix.det_transpose]`. Both sides reduce to the same expression. Rewrite using `[Finset.sum_congr rfl e2]`. Establish `key : ∀ X : ℂ, X = S.det * (X * (S⁻¹).det)` using `fun X => by`. Rewrite using `[mul_comm X, ← mul_assoc, mul_comm S.det, det_inv_mul hS', one_mul]`.

Conclude with `key _`.
-/
theorem inverse_beta_positive_holds : RInvBetaP := by
  intro k r z g S _ hS d
  have hS' : S ∈ UH (Hpk k r) := hS
  have e1 : Mr k r (C0 k r z (g * S)) (fun l => bvec (d l)) =
      Mr k r (C0 k r z g) (fun l => ∑ j, S j (d l) • bvec j) * (S⁻¹)ᵀ := by
    rw [Mr_mul, coordinate_matrix_mul_unitary z g S hS']
    congr 1
    funext l
    have : (∑ j, S j (d l) • bvec j : Fin (2 * r + k + 1) → ℂ) = bvec (d l) ᵥ* Sᵀ := by
      rw [bvec_vecMul]; rfl
    rw [this, Matrix.vecMul_vecMul, ← Matrix.transpose_mul, inv_mul_self' hS', Matrix.transpose_one,
      Matrix.vecMul_one]
  rw [beJ_eq z (g * S), e1, Matrix.det_mul, det_Mr_sum, Matrix.det_transpose]
  have e2 : ∀ J ∈ jSetR k r, beJ k r z g J * (S.submatrix J d).det =
      (Matrix.of fun l l' => S (J l') (d l)).det * (Mr k r (C0 k r z g) (fun l => bvec (J l))).det := by
    intro J _
    rw [beJ_eq, mul_comm]
    congr 1
    rw [← Matrix.det_transpose]
    rfl
  rw [Finset.sum_congr rfl e2]
  have key : ∀ X : ℂ, X = S.det * (X * (S⁻¹).det) := fun X => by
    rw [mul_comm X, ← mul_assoc, mul_comm S.det, det_inv_mul hS', one_mul]
  exact key _

namespace RInvCB

variable {k r : ℕ}

/- English proof (translation)
Use `set L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun p i => (if i = p then 1 else 0) + (if p.val ≤ r ∧ i.val < p.val then d p i else 0) with hL`. Establish `hmul : Mr k r R0' v = L * Mr k r R0 v`. Use extensionality with `p q`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Distinguish the cases in `hp : p.val ≤ r`. Rewrite using `[Mr_le _ _ hp, Mr_le _ _ hp, h p hp]`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`. Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations.

Distinguish the cases in `hi : i.val < p.val`. Establish `hi' : i.val ≤ r` using `by omega`. Simplify using `[hp, hi, Mr_le _ _ hi']`. Simplify using `[hi]`. Simplify using `only [hp, false_and, if_false, Finset.sum_const_zero, add_zero]`.

Rewrite using `[Mr_gt _ _ hp, Mr_gt _ _ hp]`. Establish `hdet : L.det = 1`. Rewrite using `[Matrix.det_of_lowerTriangular]`. Use `Finset.prod_eq_one (fun i _ => ?_)` and prove the remaining obligations. Simplify using `[hL]`.

Introduce `i j hij`. Establish `hij' : i < j` using `hij`. Establish `h1 : j ≠ i` using `ne_of_gt hij'`. Establish `h2 : ¬ (j < i)` using `not_lt.mpr hij'.le`. Simplify using `[hL, h1, h2]`.

Rewrite using `[hmul, Matrix.det_mul, hdet, one_mul]`.
-/
theorem det_Mr_lower (R0 R0' : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)
    (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ) (d : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ)
    (h : ∀ p : Fin (2 * r + k + 1), p.val ≤ r →
      R0' p = R0 p + ∑ i, (if i.val < p.val then d p i else 0) • R0 i) :
    (Mr k r R0' v).det = (Mr k r R0 v).det := by
  classical
  set L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun p i =>
    (if i = p then 1 else 0) + (if p.val ≤ r ∧ i.val < p.val then d p i else 0) with hL
  have hmul : Mr k r R0' v = L * Mr k r R0 v := by
    ext p q
    rw [Matrix.mul_apply]
    simp only [hL, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    by_cases hp : p.val ≤ r
    · rw [Mr_le _ _ hp, Mr_le _ _ hp, h p hp]
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      by_cases hi : i.val < p.val
      · have hi' : i.val ≤ r := by omega
        simp [hp, hi, Mr_le _ _ hi']
      · simp [hi]
    · simp only [hp, false_and, if_false, Finset.sum_const_zero, add_zero]
      rw [Mr_gt _ _ hp, Mr_gt _ _ hp]
  have hdet : L.det = 1 := by
    rw [Matrix.det_of_lowerTriangular]
    · refine Finset.prod_eq_one (fun i _ => ?_)
      simp [hL]
    · intro i j hij
      have hij' : i < j := hij
      have h1 : j ≠ i := ne_of_gt hij'
      have h2 : ¬ (j < i) := not_lt.mpr hij'.le
      simp [hL, h1, h2]
  rw [hmul, Matrix.det_mul, hdet, one_mul]

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `hb' : bᴴ * Hpk k r * b = Hpk k r` using `hb`. Use `show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r`. Rewrite using `[Matrix.conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem uh_mul' {a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r))
    (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  rw [Matrix.conjTranspose_mul]
  calc bᴴ * aᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

/- English proof (translation)
Establish `ha' : aᴴ * Hpk k r * a = Hpk k r` using `ha`. Establish `h1 : a * a⁻¹ = 1` using `Matrix.mul_nonsing_inv a (uh_isUnit ha)`. Use `show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Hpk k r := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem uh_inv_mem' {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ UH (Hpk k r)) :
    a⁻¹ ∈ UH (Hpk k r) := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have h1 : a * a⁻¹ = 1 := Matrix.mul_nonsing_inv a (uh_isUnit ha)
  show (a⁻¹)ᴴ * Hpk k r * a⁻¹ = Hpk k r
  calc (a⁻¹)ᴴ * Hpk k r * a⁻¹ = (a⁻¹)ᴴ * (aᴴ * Hpk k r * a) * a⁻¹ := by rw [ha']
    _ = (a * a⁻¹)ᴴ * Hpk k r * (a * a⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hi : (A⁻¹)ᴴ * Hpk k r * A⁻¹ = Hpk k r` using `uh_inv_mem' hA`. Establish `h2 : A⁻¹ * A = 1` using `inv_mul_self' hA`. Establish `key : Hpk k r * A = (A⁻¹)ᴴ * Hpk k r`. Combine the equalities or inequalities in the displayed calculation. Unfold `herm`.

Rewrite using `[Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]`.
-/
theorem herm_uh {A : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hA : A ∈ UH (Hpk k r))
    (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) (A *ᵥ v) w = herm (Hpk k r) v (A⁻¹ *ᵥ w) := by
  have hi : (A⁻¹)ᴴ * Hpk k r * A⁻¹ = Hpk k r := uh_inv_mem' hA
  have h2 : A⁻¹ * A = 1 := inv_mul_self' hA
  have key : Hpk k r * A = (A⁻¹)ᴴ * Hpk k r := by
    calc Hpk k r * A = (A⁻¹)ᴴ * Hpk k r * A⁻¹ * A := by rw [hi]
      _ = (A⁻¹)ᴴ * Hpk k r := by rw [Matrix.mul_assoc _ A⁻¹, h2, Matrix.mul_one]
  unfold herm
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

def wv (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  if h : p.val < r then bvec (eI k r ⟨p.val, h⟩) else z

/- English proof (translation)
Use `ext`. Both sides reduce to the same expression.
-/
theorem eI_val (i : Fin (2 * r + k + 1)) (h : i.val < r) : eI k r ⟨i.val, h⟩ = i := by ext; rfl

/- English proof (translation)
Take `⟨_, hm2, hm3⟩` from `hm`. Use function extensionality and compare the values at `x`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Distinguish the cases in `hx : x.val < p.val`. Rewrite using `[if_pos hx]`.

Establish `: wv k r z p x = 0`. Unfold `wv`. Use `split_ifs with h1`. Simplify using `only [bvec, Pi.single_apply]`. Rewrite using `[if_neg]`.

Introduce `he`. Rewrite `hx` using `[he]`. Simplify using `[eI] at hx`. Conclude with `hz x (Or.inl (by omega))`. Rewrite using `[this, zero_add]`.

Rewrite using `[if_neg hx, add_zero]`. Unfold `wv`. Use `split_ifs with h1`. Use `hm2 ⟨p.val, h1⟩ x (by simp; omega)` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Rewrite using `[this]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[Finset.sum_eq_single x]`. Distinguish the cases in `hzx : z x = 0`. Rewrite using `[hzx, mul_zero]`.

Establish `h3 : r ≤ x.val ∧ x.val ≤ r + k`. Assume the negation of the conclusion as `hc`. Apply `hzx` to reduce the goal to its premises. Conclude with `hz x (by omega)`. Rewrite using `[hm3 x x h3.1 h3.2 (by omega), if_pos rfl, one_mul]`.

Introduce `j _ hj`. Distinguish the cases in `hzj : z j = 0`. Rewrite using `[hzj, mul_zero]`. Establish `h3 : r ≤ j.val ∧ j.val ≤ r + k`. Assume the negation of the conclusion as `hc`.

Apply `hzj` to reduce the goal to its premises. Conclude with `hz j (by omega)`. Rewrite using `[hm3 x j h3.1 h3.2 (by omega), if_neg (Ne.symm hj), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ x) h`.
-/
theorem nset_wv {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hm : m ∈ Nset k r) {p : Fin (2 * r + k + 1)} (hp : p.val ≤ r) :
    m *ᵥ wv k r z p = wv k r z p + ∑ i, (if i.val < p.val then (m *ᵥ wv k r z p) i else 0) • bvec i := by
  obtain ⟨_, hm2, hm3⟩ := hm
  funext x
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, bvec, Pi.single_apply, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hx : x.val < p.val
  · rw [if_pos hx]
    have : wv k r z p x = 0 := by
      unfold wv
      split_ifs with h1
      · simp only [bvec, Pi.single_apply]
        rw [if_neg]; intro he; rw [he] at hx; simp [eI] at hx
      · exact hz x (Or.inl (by omega))
    rw [this, zero_add]
  · rw [if_neg hx, add_zero]
    unfold wv
    split_ifs with h1
    · have := hm2 ⟨p.val, h1⟩ x (by simp; omega)
      simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [this]
    · simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single x]
      · by_cases hzx : z x = 0
        · rw [hzx, mul_zero]
        · have h3 : r ≤ x.val ∧ x.val ≤ r + k := by
            by_contra hc
            apply hzx
            exact hz x (by omega)
          rw [hm3 x x h3.1 h3.2 (by omega), if_pos rfl, one_mul]
      · intro j _ hj
        by_cases hzj : z j = 0
        · rw [hzj, mul_zero]
        · have h3 : r ≤ j.val ∧ j.val ≤ r + k := by
            by_contra hc
            apply hzj
            exact hz j (by omega)
          rw [hm3 x j h3.1 h3.2 (by omega), if_neg (Ne.symm hj), zero_mul]
      · intro h; exact absurd (Finset.mem_univ x) h

/- English proof (translation)
The claim follows from `uh_mul' (uh_inv_mem' hh.1) (uh_inv_mem' hm.1)`.
-/
theorem A_uh {z : Fin (2 * r + k + 1) → ℂ} {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : h⁻¹ * m⁻¹ ∈ UH (Hpk k r) :=
  uh_mul' (uh_inv_mem' hh.1) (uh_inv_mem' hm.1)

/- English proof (translation)
Rewrite using `[Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (uh_isUnit hm.1), Matrix.nonsing_inv_nonsing_inv _ (uh_isUnit hh.1)]`.
-/
theorem A_inv {z : Fin (2 * r + k + 1) → ℂ} {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : (h⁻¹ * m⁻¹)⁻¹ = m * h := by
  rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (uh_isUnit hm.1),
    Matrix.nonsing_inv_nonsing_inv _ (uh_isUnit hh.1)]

/- English proof (translation)
Unfold `wv`. Use `split_ifs with h1`. Conclude with `(hh.2.1 ⟨p.val, h1⟩).1`. Conclude with `hh.2.2`.
-/
theorem h_wv {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (p : Fin (2 * r + k + 1)) : h *ᵥ wv k r z p = wv k r z p := by
  unfold wv
  split_ifs with h1
  · exact (hh.2.1 ⟨p.val, h1⟩).1
  · exact hh.2.2

/- English proof (translation)
Apply the tactic sequence `funext q; unfold A0 wv; split_ifs <;> rfl`.
-/
theorem A0_eq_herm_mulVec_bvec_wv (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (p : Fin (2 * r + k + 1)) :
    A0 k r z g p = fun q => herm (Hpk k r) (g *ᵥ bvec q) (wv k r z p) := by
  funext q; unfold A0 wv; split_ifs <;> rfl

end RInvCB

open RInvCB in
/- English proof (translation)
Introduce `k r z h m g hz hh hm _ J`. Rewrite using `[alJ_eq, alJ_eq]`. Apply `det_Mr_lower (d := fun p i => star ((m *ᵥ wv k r z p) i))` to reduce the goal to its premises. Introduce `p hp`. Use function extensionality and compare the values at `q`.

Establish `e : A0 k r z (h⁻¹ * m⁻¹ * g) p q = herm (Hpk k r) (g *ᵥ bvec q) (m *ᵥ wv k r z p)`. Rewrite using `[A0_eq_herm_mulVec_bvec_wv]`. Use `show herm (Hpk k r) ((h⁻¹ * m⁻¹ * g) *ᵥ bvec q) (wv k r z p) = _`. Rewrite using `[← Matrix.mulVec_mulVec, herm_uh (A_uh hh hm), A_inv hh hm, ← Matrix.mulVec_mulVec, h_wv hh]`. Rewrite using `[e]`.

Use `conv_lhs => rw [nset_wv hz hm hp]`. Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A0_eq_herm_mulVec_bvec_wv]`. Unfold `herm`. Rewrite using `[star_add, add_dotProduct, star_sum, sum_dotProduct]`. Use `congr 1`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[star_smul, smul_dotProduct, smul_eq_mul]`. Distinguish the cases in `hi : i.val < p.val`. Establish `hi' : i.val < r` using `by omega`. Rewrite using `[if_pos hi, if_pos hi, show wv k r z i = bvec i by simp only [wv, dif_pos hi', eI_val i hi']]`.

Rewrite using `[if_neg hi, if_neg hi, star_zero, zero_mul, zero_mul]`.
-/
theorem inverse_alpha_left_minus : RInvAlphaLeftM := by
  intro k r z h m g hz hh hm _ J
  rw [alJ_eq, alJ_eq]
  apply det_Mr_lower (d := fun p i => star ((m *ᵥ wv k r z p) i))
  intro p hp
  funext q
  have e : A0 k r z (h⁻¹ * m⁻¹ * g) p q = herm (Hpk k r) (g *ᵥ bvec q) (m *ᵥ wv k r z p) := by
    rw [A0_eq_herm_mulVec_bvec_wv]
    show herm (Hpk k r) ((h⁻¹ * m⁻¹ * g) *ᵥ bvec q) (wv k r z p) = _
    rw [← Matrix.mulVec_mulVec, herm_uh (A_uh hh hm), A_inv hh hm, ← Matrix.mulVec_mulVec, h_wv hh]
  rw [e]
  conv_lhs => rw [nset_wv hz hm hp]
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, A0_eq_herm_mulVec_bvec_wv]
  unfold herm
  rw [star_add, add_dotProduct, star_sum, sum_dotProduct]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [star_smul, smul_dotProduct, smul_eq_mul]
  by_cases hi : i.val < p.val
  · have hi' : i.val < r := by omega
    rw [if_pos hi, if_pos hi, show wv k r z i = bvec i by simp only [wv, dif_pos hi', eI_val i hi']]
  · rw [if_neg hi, if_neg hi, star_zero, zero_mul, zero_mul]

namespace RInvCB

variable {k r : ℕ}

def sigF (k r : ℕ) (q : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if h : q.val < r then ⟨r - 1 - q.val, by omega⟩ else q

/- English proof (translation)
Introduce `q`. Unfold `sigF`. Distinguish the cases in `h : q.val < r`. Rewrite using `[dif_pos h]`. Establish `h' : r - 1 - q.val < r` using `by omega`.

Simplify using `only [dif_pos h']`. Use `ext`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Rewrite using `[dif_neg h, dif_neg h]`.
-/
theorem sigF_inv (k r : ℕ) : Function.Involutive (sigF k r) := by
  intro q
  unfold sigF
  by_cases h : q.val < r
  · rw [dif_pos h]
    have h' : r - 1 - q.val < r := by omega
    simp only [dif_pos h']
    ext; simp; omega
  · rw [dif_neg h, dif_neg h]

def C0' (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (p : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) → ℂ :=
  ginvH k r g *ᵥ wv k r z p

/- English proof (translation)
Use extensionality with `q j`. Simplify using `only [Matrix.submatrix_apply, id, Function.Involutive.coe_toPerm]`. Distinguish the cases in `h1 : q.val < r`. Establish `hq : q.val ≤ r` using `by omega`. Establish `hs : (sigF k r q).val < r` using `by simp only [sigF, dif_pos h1]; omega`.

Rewrite using `[Mr_le _ _ hq, Mr_le _ _ (by omega : (sigF k r q).val ≤ r)]`. Simplify using `only [C0, C0', wv, dif_pos h1, dif_pos hs]`. Use `congr 3`. Use `ext`. Simplify using `[sigF, h1]`.

Establish `e : sigF k r q = q` using `by simp [sigF, h1]`. Rewrite using `[e]`. Distinguish the cases in `hq : q.val ≤ r`. Rewrite using `[Mr_le _ _ hq, Mr_le _ _ hq]`. Simplify using `only [C0, C0', wv, dif_neg h1]`.

Rewrite using `[Mr_gt _ _ hq, Mr_gt _ _ hq]`.
-/
theorem minor_matrix_permuted_rows (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (v : Fin (r + k) → Fin (2 * r + k + 1) → ℂ) :
    Mr k r (C0 k r z g) v = (Mr k r (C0' k r z g) v).submatrix (sigF_inv k r).toPerm id := by
  ext q j
  simp only [Matrix.submatrix_apply, id, Function.Involutive.coe_toPerm]
  by_cases h1 : q.val < r
  · have hq : q.val ≤ r := by omega
    have hs : (sigF k r q).val < r := by simp only [sigF, dif_pos h1]; omega
    rw [Mr_le _ _ hq, Mr_le _ _ (by omega : (sigF k r q).val ≤ r)]
    simp only [C0, C0', wv, dif_pos h1, dif_pos hs]
    congr 3
    ext; simp [sigF, h1]
  · have e : sigF k r q = q := by simp [sigF, h1]
    rw [e]
    by_cases hq : q.val ≤ r
    · rw [Mr_le _ _ hq, Mr_le _ _ hq]
      simp only [C0, C0', wv, dif_neg h1]
    · rw [Mr_gt _ _ hq, Mr_gt _ _ hq]

/- English proof (translation)
Rewrite using `[beJ_eq, minor_matrix_permuted_rows, Matrix.det_permute]`.
-/
theorem beJ_eq' (z : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r) (J : Fin (r + k) → Fin (2 * r + k + 1)) :
    beJ k r z g J = (((sigF_inv k r).toPerm.sign : ℤ) : ℂ) * (Mr k r (C0' k r z g) (fun l => bvec (J l))).det := by
  rw [beJ_eq, minor_matrix_permuted_rows, Matrix.det_permute]

end RInvCB

open RInvCB in
/- English proof (translation)
Introduce `k r z h m g hz hh hm _ J`. Rewrite using `[beJ_eq', beJ_eq']`. It suffices to establish `key : (Mr k r (C0' k r z (h⁻¹ * m⁻¹ * g)) (fun l => bvec (J l))).det = (Mr k r (C0' k r z g) (fun l => bvec (J l))).det by rw [key]`. Apply `det_Mr_lower (d := fun p i => (m *ᵥ wv k r z p) i)` to reduce the goal to its premises. Introduce `p hp`.

Establish `hA : ginvH k r (h⁻¹ * m⁻¹) = m * h`. Rewrite using `[← A_inv hh hm, uh_inv_eq' (A_uh hh hm)]`. Both sides reduce to the same expression. Establish `e : C0' k r z (h⁻¹ * m⁻¹ * g) p = ginvH k r g *ᵥ (m *ᵥ wv k r z p)`. Simplify using `only [C0', ginvH_mul, hA]`.

Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_wv hh]`. Rewrite using `[e]`. Use `conv_lhs => rw [nset_wv hz hm hp]`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl (fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul]`. Distinguish the cases in `hi : i.val < p.val`. Establish `hi' : i.val < r` using `by omega`. Simplify using `only [if_pos hi, C0', wv, dif_pos hi', eI_val i hi']`.

Simplify using `only [if_neg hi, zero_smul]`.
-/
theorem inverse_beta_left_positive : RInvBetaLeftP := by
  intro k r z h m g hz hh hm _ J
  rw [beJ_eq', beJ_eq']
  suffices key : (Mr k r (C0' k r z (h⁻¹ * m⁻¹ * g)) (fun l => bvec (J l))).det =
      (Mr k r (C0' k r z g) (fun l => bvec (J l))).det by rw [key]
  apply det_Mr_lower (d := fun p i => (m *ᵥ wv k r z p) i)
  intro p hp
  have hA : ginvH k r (h⁻¹ * m⁻¹) = m * h := by
    rw [← A_inv hh hm, uh_inv_eq' (A_uh hh hm)]; rfl
  have e : C0' k r z (h⁻¹ * m⁻¹ * g) p = ginvH k r g *ᵥ (m *ᵥ wv k r z p) := by
    simp only [C0', ginvH_mul, hA]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h_wv hh]
  rw [e]
  conv_lhs => rw [nset_wv hz hm hp]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Matrix.mulVec_smul]
  by_cases hi : i.val < p.val
  · have hi' : i.val < r := by omega
    simp only [if_pos hi, C0', wv, dif_pos hi', eI_val i hi']
  · simp only [if_neg hi, zero_smul]

end

end Formalism.FourierDecayAlt.P.CutMP
