import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LemmaG3OfCoefficients

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

section Uni

variable {K : Type*} [Field K] {N : ℕ}

/- English proof (translation)
Introduce `i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k < i`.

Rewrite using `[(hA i k).1 hk, zero_mul]`. Rewrite using `[(hB k j).1 (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]`. Substitute `hij` using the available equality. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single i]`. Rewrite using `[(hA i i).2 rfl, (hB i i).2 rfl, one_mul]`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with h | h` into its components or cases. Rewrite using `[(hA i k).1 h, zero_mul]`. Rewrite using `[(hB k i).1 h, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upUni_mul {A B : Matrix (Fin N) (Fin N) K} (hA : IsUpUni A) (hB : IsUpUni B) : IsUpUni (A * B) := by
  intro i j
  refine ⟨fun hji => ?_, fun hij => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hA i k).1 hk, zero_mul]
    · rw [(hB k j).1 (lt_of_lt_of_le hji (not_lt.1 hk)), mul_zero]
  · subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hA i i).2 rfl, (hB i i).2 rfl, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hA i k).1 h, zero_mul]
      · rw [(hB k i).1 h, mul_zero]
    · simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `⟨fun hji => ?_, fun hij => ?_⟩` and prove the remaining obligations. Rewrite using `[conjTranspose_apply, (h j i).1 hji, star_zero]`. Substitute `hij` using the available equality.

Rewrite using `[conjTranspose_apply, (h i i).2 rfl, star_one]`. Introduce `h i j`. Use `⟨fun hij => ?_, fun hij => ?_⟩` and prove the remaining obligations. Use `(h j i).1 hij` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply]`.

Conclude with `star_eq_zero.1 this`. Substitute `hij` using the available equality. Use `(h i i).2 rfl` as an intermediate fact. Rewrite `this` using `[conjTranspose_apply]`. Rewrite using `[← star_star (A i i), this, star_one]`.
-/
theorem loUni_iff_ct {A : Matrix (Fin N) (Fin N) K} [StarRing K] : IsLoUni A ↔ IsUpUni Aᴴ := by
  constructor
  · intro h i j
    refine ⟨fun hji => ?_, fun hij => ?_⟩
    · rw [conjTranspose_apply, (h j i).1 hji, star_zero]
    · subst hij; rw [conjTranspose_apply, (h i i).2 rfl, star_one]
  · intro h i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · have := (h j i).1 hij
      rw [conjTranspose_apply] at this
      exact star_eq_zero.1 this
    · subst hij
      have := (h i i).2 rfl
      rw [conjTranspose_apply] at this
      rw [← star_star (A i i), this, star_one]

/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`. Introduce `i j hij`. Conclude with `(h i j).1 hij`.
-/
theorem upUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : A.det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`. Introduce `i j hij`. Conclude with `(h i j).1 hij`.
-/
theorem loUni_det {A : Matrix (Fin N) (Fin N) K} (h : IsLoUni A) : A.det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · exact Finset.prod_eq_one fun i _ => (h i i).2 rfl
  · intro i j hij
    exact (h i j).1 hij

/- English proof (translation)
Establish `hdet : IsUnit A.det` using `by rw [upUni_det h]; exact isUnit_one`. Establish `hbt : A.BlockTriangular id` using `fun i j hij => (h i j).1 hij`. Use `haveI := A.invertibleOfIsUnitDet hdet`. Establish `hbt' : A⁻¹.BlockTriangular id` using `Matrix.blockTriangular_inv_of_blockTriangular hbt`. Introduce `i j`.

Use `⟨fun hji => hbt' hji, fun hij => ?_⟩` and prove the remaining obligations. Substitute `hij` using the available equality. Establish `e` using `congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i`. Rewrite `e` using `[Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul]`. Simplify using `using e`.

Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hlt | hgt` into its components or cases. Rewrite using `[(h i k).1 hlt, zero_mul]`. Rewrite using `[hbt' hgt, mul_zero]`. Simplify using the standard rewrite rules.
-/
theorem upUni_inv {A : Matrix (Fin N) (Fin N) K} (h : IsUpUni A) : IsUpUni A⁻¹ := by
  have hdet : IsUnit A.det := by rw [upUni_det h]; exact isUnit_one
  have hbt : A.BlockTriangular id := fun i j hij => (h i j).1 hij
  haveI := A.invertibleOfIsUnitDet hdet
  have hbt' : A⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hbt
  intro i j
  refine ⟨fun hji => hbt' hji, fun hij => ?_⟩
  subst hij
  have e := congrFun (congrFun (Matrix.mul_nonsing_inv A hdet) i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, (h i i).2 rfl, one_mul] at e
  · simpa using e
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [(h i k).1 hlt, zero_mul]
    · rw [hbt' hgt, mul_zero]
  · simp

/- English proof (translation)
Rewrite using `[loUni_iff_ct, conjTranspose_mul]`. Conclude with `upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)`.
-/
theorem loUni_mul {A B : Matrix (Fin N) (Fin N) K} [StarRing K] (hA : IsLoUni A) (hB : IsLoUni B) :
    IsLoUni (A * B) := by
  rw [loUni_iff_ct, conjTranspose_mul]
  exact upUni_mul (loUni_iff_ct.1 hB) (loUni_iff_ct.1 hA)

/- English proof (translation)
Rewrite using `[loUni_iff_ct, conjTranspose_nonsing_inv]`. Conclude with `upUni_inv (loUni_iff_ct.1 h)`.
-/
theorem loUni_inv {A : Matrix (Fin N) (Fin N) K} [StarRing K] (h : IsLoUni A) : IsLoUni A⁻¹ := by
  rw [loUni_iff_ct, conjTranspose_nonsing_inv]
  exact upUni_inv (loUni_iff_ct.1 h)

/- English proof (translation)
Distinguish the cases in `hc : c = Fin.last r`. Substitute `hc` using the available equality. Rewrite using `[if_pos rfl]`. Conclude with `(h _ _).2 rfl`. Rewrite using `[if_neg hc]`.

Conclude with `(h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)`.
-/
theorem upUni_last {r : ℕ} {A : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni A) (c : Fin (r + 1)) :
    A (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  by_cases hc : c = Fin.last r
  · subst hc; rw [if_pos rfl]; exact (h _ _).2 rfl
  · rw [if_neg hc]
    exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last c) hc)

end Uni

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Establish `hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c`. Introduce `b`. Rewrite using `[hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]`. Establish `h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b`. Rewrite using `[Finset.sum_eq_single b]`.

Rewrite using `[(hN b b).2 rfl, one_smul]`. Introduce `c hc hcb`. Establish `: b < c` using `lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)`. Rewrite using `[(hN c b).1 this, zero_smul]`. Introduce `hb`.

It suffices to derive a contradiction. Apply `hb` to reduce the goal to its premises. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws.

Establish `he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a`. Introduce `a`. Use `hdiff (Fin.castSucc a)` as an intermediate fact. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc] at this`. Rewrite using `[this]`.

Use `Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hc' : c < Fin.castSucc a` using `(Finset.mem_filter.1 hc).2`. Establish `hcl : c ≠ Fin.last r` using `ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))`. Take `⟨c', rfl⟩` from `Fin.exists_castSucc_eq.2 hcl`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`.

Conclude with `Submodule.subset_span ⟨c', by simpa using hc', rfl⟩`. Use `⟨fun j x hx => ?_, ?_⟩` and prove the remaining obligations. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨a, ha, rfl⟩` from `hy`.

Establish `ha' : (a : ℕ) < j + 1` using `ha`. Use `Submodule.span_mono ?_ (he a)` and prove the remaining obligations. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add, add_sub_add_comm]`. Conclude with `Submodule.add_mem _ hx hy`. Consider the case `smul c x _ hx => rw [map_smul, ← smul_sub]`. Conclude with `Submodule.smul_mem _ _ hx`. Use `hdiff (Fin.last r)` as an intermediate fact.

Simplify using `only [FlagG.fvec, Fin.snoc_last] at this`. Rewrite using `[this]`. Use `Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hcl : c ≠ Fin.last r` using `ne_of_lt (Finset.mem_filter.1 hc).2`. Take `⟨c', rfl⟩` from `Fin.exists_castSucc_eq.2 hcl`.

Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Conclude with `Submodule.subset_span ⟨c', rfl⟩`.
-/
theorem flag_of_upUni (F : FlagG S r T) (g : S.V →ₗ[E] S.V) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E)
    (hN : IsUpUni N) (hg : ∀ b, g (F.fvec b) = ∑ c, N c b • F.fvec c) :
    (∀ j, ∀ x ∈ F.Xa (j + 1), g x - x ∈ F.Xa j) ∧ g F.z - F.z ∈ F.X := by
  have hdiff : ∀ b, g (F.fvec b) - F.fvec b = ∑ c ∈ Finset.univ.filter (· < b), N c b • F.fvec c := by
    intro b
    rw [hg b, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· < b)]
    have h2 : ∑ c ∈ Finset.univ.filter (fun c => ¬ c < b), N c b • F.fvec c = F.fvec b := by
      rw [Finset.sum_eq_single b]
      · rw [(hN b b).2 rfl, one_smul]
      · intro c hc hcb
        have : b < c := lt_of_le_of_ne (not_lt.1 (Finset.mem_filter.1 hc).2) (Ne.symm hcb)
        rw [(hN c b).1 this, zero_smul]
      · intro hb; exfalso; apply hb; simp
    rw [h2]; abel
  have he : ∀ a : Fin r, g (F.e a) - F.e a ∈ F.Xa a := by
    intro a
    have := hdiff (Fin.castSucc a)
    simp only [FlagG.fvec, Fin.snoc_castSucc] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hc' : c < Fin.castSucc a := (Finset.mem_filter.1 hc).2
    have hcl : c ≠ Fin.last r := ne_of_lt (lt_trans hc' (Fin.castSucc_lt_last a))
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', by simpa using hc', rfl⟩
  refine ⟨fun j x hx => ?_, ?_⟩
  · induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      have ha' : (a : ℕ) < j + 1 := ha
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨i, hi, rfl⟩
      exact ⟨i, by show (i : ℕ) < j; have : (i : ℕ) < a := hi; omega, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_sub_add_comm]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul, ← smul_sub]; exact Submodule.smul_mem _ _ hx
  · have := hdiff (Fin.last r)
    simp only [FlagG.fvec, Fin.snoc_last] at this
    rw [this]
    refine Submodule.sum_mem _ fun c hc => Submodule.smul_mem _ _ ?_
    have hcl : c ≠ Fin.last r := ne_of_lt (Finset.mem_filter.1 hc).2
    obtain ⟨c', rfl⟩ := Fin.exists_castSucc_eq.2 hcl
    simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.subset_span ⟨c', rfl⟩

end Formalism.L2.SG.NGCut.NormalVectorPairings
