import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.FiniteSupportHeight
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix
open scoped ComplexOrder

noncomputable section

section GramGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Establish `hg : gram ℂ (Sum.elim v w) = fromBlocks (gram ℂ v) 0 0 (gram ℂ w)`. Use extensionality with `(i | i) (j | j)`. Simplify using `[gram_apply]`. Simplify using `[gram_apply, h]`. Simplify using `[gram_apply, inner_eq_zero_symm.mp (h j i)]`.

Simplify using `[gram_apply]`. Rewrite using `[hg, det_fromBlocks_zero₂₁]`.
-/
theorem det_gram_sumElim_of_orthogonal {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (v : ι → V) (w : κ → V) (h : ∀ i j, inner ℂ (v i) (w j) = 0) :
    det (gram ℂ (Sum.elim v w)) = det (gram ℂ v) * det (gram ℂ w) := by
  have hg : gram ℂ (Sum.elim v w) = fromBlocks (gram ℂ v) 0 0 (gram ℂ w) := by
    ext (i | i) (j | j)
    · simp [gram_apply]
    · simp [gram_apply, h]
    · simp [gram_apply, inner_eq_zero_symm.mp (h j i)]
    · simp [gram_apply]
  rw [hg, det_fromBlocks_zero₂₁]

/- English proof (translation)
Use `set B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 (-M) 0 1 with hBdef`. Establish `hc : Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i) = fun b ↦ ∑ a, B a b • Sum.elim v u a`. Use function extensionality and compare the values at `b`. Break down `b with i | j` into its components or cases. Simplify using `[B, Fintype.sum_sum_type, one_apply, ite_smul]`.

Simplify using `[B, Fintype.sum_sum_type, one_apply, ite_smul, sub_eq_add_neg, add_comm]`. Establish `hB : det B = 1` using `by simp [B]`. Rewrite using `[hc, gram_comb, det_mul, det_mul, det_conjTranspose, hB]`. Simplify using the standard rewrite rules.
-/
theorem det_gram_sumElim_sub {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) (M : Matrix ι κ ℂ) :
    det (gram ℂ (Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i))) = det (gram ℂ (Sum.elim v u)) := by
  set B : Matrix (ι ⊕ κ) (ι ⊕ κ) ℂ := fromBlocks 1 (-M) 0 1 with hBdef
  have hc : Sum.elim v (fun j ↦ u j - ∑ i, M i j • v i) =
      fun b ↦ ∑ a, B a b • Sum.elim v u a := by
    funext b
    rcases b with i | j
    · simp [B, Fintype.sum_sum_type, one_apply, ite_smul]
    · simp [B, Fintype.sum_sum_type, one_apply, ite_smul, sub_eq_add_neg, add_comm]
  have hB : det B = 1 := by simp [B]
  rw [hc, gram_comb, det_mul, det_mul, det_conjTranspose, hB]
  simp

end GramGeometry

section GramGeometry2

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

instance hasOrthogonalProjection_span_range {ι : Type*} [Fintype ι] (v : ι → V) :
    (Submodule.span ℂ (Set.range v)).HasOrthogonalProjection := by
  have : FiniteDimensional ℂ (Submodule.span ℂ (Set.range v)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range v)
  infer_instance

/- English proof (translation)
Use `set U := Submodule.span ℂ (Set.range v)`. Establish `hmem : ∀ j, ∃ c : ι → ℂ, ∑ i, c i • v i = U.starProjection (u j)` using `fun j ↦ (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem (u j))`. Use `choose c hc using hmem`. Establish `hu : (fun j ↦ u j - U.starProjection (u j)) = fun j ↦ u j - ∑ i, (of fun i j ↦ c j i) i j • v i`. Use function extensionality and compare the values at `j`.

Simplify using `[hc]`. Rewrite using `[← det_gram_sumElim_sub v u (of fun i j ↦ c j i), ← hu]`. Use `det_gram_sumElim_of_orthogonal v _ fun i j ↦ ?_` and prove the remaining obligations. Conclude with `Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i)) (U.sub_starProjection_mem_orthogonal (u j))`.
-/
theorem det_gram_sumElim_eq {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : ι → V) (u : κ → V) :
    det (gram ℂ (Sum.elim v u)) = det (gram ℂ v) *
      det (gram ℂ (fun j ↦ u j - (Submodule.span ℂ (Set.range v)).starProjection (u j))) := by
  set U := Submodule.span ℂ (Set.range v)
  have hmem : ∀ j, ∃ c : ι → ℂ, ∑ i, c i • v i = U.starProjection (u j) := fun j ↦
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem (u j))
  choose c hc using hmem
  have hu : (fun j ↦ u j - U.starProjection (u j)) = fun j ↦ u j - ∑ i, (of fun i j ↦ c j i) i j • v i := by
    funext j
    simp [hc]
  rw [← det_gram_sumElim_sub v u (of fun i j ↦ c j i), ← hu]
  refine det_gram_sumElim_of_orthogonal v _ fun i j ↦ ?_
  exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i))
    (U.sub_starProjection_mem_orthogonal (u j))

/- English proof (translation)
Rewrite using `[det_unique, gram_apply, inner_self_eq_norm_sq_to_K]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem det_gram_unique {κ : Type*} [Unique κ] (w : κ → V) :
    det (gram ℂ w) = ((‖w default‖ ^ 2 : ℝ) : ℂ) := by
  rw [det_unique, gram_apply, inner_self_eq_norm_sq_to_K]
  push_cast
  rfl

/- English proof (translation)
The claim follows from `(posSemidef_gram ℂ w).det_nonneg`.
-/
theorem det_gram_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ det (gram ℂ w) :=
  (posSemidef_gram ℂ w).det_nonneg

/- English proof (translation)
The claim follows from `((Complex.nonneg_iff.mp (det_gram_nonneg w)).2).symm`.
-/
theorem im_det_gram {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    (det (gram ℂ w)).im = 0 :=
  ((Complex.nonneg_iff.mp (det_gram_nonneg w)).2).symm

/- English proof (translation)
The claim follows from `(Complex.nonneg_iff.mp (det_gram_nonneg w)).1`.
-/
theorem det_gram_re_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ι → V) :
    0 ≤ (det (gram ℂ w)).re :=
  (Complex.nonneg_iff.mp (det_gram_nonneg w)).1

/- English proof (translation)
Establish `: gram ℂ (w ∘ e) = (gram ℂ w).submatrix e e` using `by ext i j; rfl`. Rewrite using `[this, det_submatrix_equiv_self]`.
-/
theorem det_gram_comp_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (e : κ ≃ ι) (w : ι → V) : det (gram ℂ (w ∘ e)) = det (gram ℂ w) := by
  have : gram ℂ (w ∘ e) = (gram ℂ w).submatrix e e := by ext i j; rfl
  rw [this, det_submatrix_equiv_self]

/- English proof (translation)
Use `set U := Submodule.span ℂ (Set.range c)`. Use `set U' := Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))`. Take `⟨a, ha⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem x)`. Establish `hmem : Y.starProjection (U.starProjection x) ∈ U'`. Rewrite using `[← ha, map_sum]`.

Use `Submodule.sum_mem _ fun i _ ↦ ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`. Establish `h1 : ‖Y.starProjection x - U'.starProjection (Y.starProjection x)‖ ≤ ‖Y.starProjection x - Y.starProjection (U.starProjection x)‖`. Rewrite using `[Submodule.starProjection_minimal]`.

Conclude with `ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (⟨_, hmem⟩ : U')`. Use `h1.trans ?_` and prove the remaining obligations. Rewrite using `[← map_sub]`. Conclude with `Y.norm_starProjection_apply_le _`.
-/
theorem norm_sub_proj_map_le {ι : Type*} [Fintype ι] (Y : Submodule ℂ V) [Y.HasOrthogonalProjection]
    (c : ι → V) (x : V) :
    ‖Y.starProjection x - (Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))).starProjection
        (Y.starProjection x)‖ ≤ ‖x - (Submodule.span ℂ (Set.range c)).starProjection x‖ := by
  set U := Submodule.span ℂ (Set.range c)
  set U' := Submodule.span ℂ (Set.range fun i ↦ Y.starProjection (c i))
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp (U.starProjection_apply_mem x)
  have hmem : Y.starProjection (U.starProjection x) ∈ U' := by
    rw [← ha, map_sum]
    refine Submodule.sum_mem _ fun i _ ↦ ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have h1 : ‖Y.starProjection x - U'.starProjection (Y.starProjection x)‖ ≤
      ‖Y.starProjection x - Y.starProjection (U.starProjection x)‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, fun _ ⟨_, h⟩ ↦ h ▸ norm_nonneg _⟩ (⟨_, hmem⟩ : U')
  refine h1.trans ?_
  rw [← map_sub]
  exact Y.norm_starProjection_apply_le _

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro c`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Introduce `c`. Set `e : Fin n ⊕ Unit ≃ Fin (n + 1)` to `(Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv`. Establish `he : ∀ (w : Fin (n + 1) → V), w ∘ e = Sum.elim (fun i ↦ w i.castSucc) (fun _ : Unit ↦ w (Fin.last n))`. Introduce `w`. Use function extensionality and compare the values at `b`.

Break down `b with i | u` into its components or cases. Both sides reduce to the same expression. Simplify using `only [Function.comp_apply, Sum.elim_inr]`. Use `congr 1`. Establish `key : ∀ (w : Fin (n + 1) → V), det (gram ℂ w) = det (gram ℂ fun i : Fin n ↦ w i.castSucc) * ((‖w (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ w i.castSucc)).starProjection (w (Fin.last n))‖ ^ 2 : ℝ) : ℂ)`.

Introduce `w`. Rewrite using `[← det_gram_comp_equiv e w, he, det_gram_sumElim_eq, det_gram_unique]`. Rewrite using `[key c, key (fun i ↦ Y.starProjection (c i))]`. Establish `hc'` using `ih (fun i : Fin n ↦ c i.castSucc)`. Simplify using `only [Complex.re_mul_ofReal]`.

Establish `hn` using `norm_sub_proj_map_le Y (fun i : Fin n ↦ c i.castSucc) (c (Fin.last n))`. Conclude with `mul_le_mul hc' (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _) (det_gram_re_nonneg _)`.
-/
theorem re_det_gram_proj_le_fin (Y : Submodule ℂ V) [Y.HasOrthogonalProjection] :
    ∀ (n : ℕ) (c : Fin n → V),
      (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  intro n
  induction n with
  | zero => intro c; simp
  | succ n ih =>
    intro c
    let e : Fin n ⊕ Unit ≃ Fin (n + 1) :=
      (Equiv.sumCongr (Equiv.refl _) finOneEquiv.symm).trans finSumFinEquiv
    have he : ∀ (w : Fin (n + 1) → V), w ∘ e =
        Sum.elim (fun i ↦ w i.castSucc) (fun _ : Unit ↦ w (Fin.last n)) := by
      intro w
      funext b
      rcases b with i | u
      · rfl
      · simp only [Function.comp_apply, Sum.elim_inr]
        congr 1
    have key : ∀ (w : Fin (n + 1) → V), det (gram ℂ w) = det (gram ℂ fun i : Fin n ↦ w i.castSucc) *
        ((‖w (Fin.last n) - (Submodule.span ℂ (Set.range fun i : Fin n ↦ w i.castSucc)).starProjection
          (w (Fin.last n))‖ ^ 2 : ℝ) : ℂ) := by
      intro w
      rw [← det_gram_comp_equiv e w, he, det_gram_sumElim_eq, det_gram_unique]
    rw [key c, key (fun i ↦ Y.starProjection (c i))]
    have hc' := ih (fun i : Fin n ↦ c i.castSucc)
    simp only [Complex.re_mul_ofReal]
    have hn := norm_sub_proj_map_le Y (fun i : Fin n ↦ c i.castSucc) (c (Fin.last n))
    exact mul_le_mul hc' (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _)
      (det_gram_re_nonneg _)

/- English proof (translation)
Set `e` to `(Fintype.equivFin ι).symm`. Establish `h` using `re_det_gram_proj_le_fin Y (Fintype.card ι) (c ∘ e)`. Rewrite `h` using `[det_gram_comp_equiv e c, show (fun i ↦ Y.starProjection ((c ∘ e) i)) = (fun i ↦ Y.starProjection (c i)) ∘ e from rfl, det_gram_comp_equiv]`. Then use the resulting hypothesis.
-/
theorem re_det_gram_proj_le {ι : Type*} [Fintype ι] [DecidableEq ι] (Y : Submodule ℂ V)
    [Y.HasOrthogonalProjection] (c : ι → V) :
    (det (gram ℂ fun i ↦ Y.starProjection (c i))).re ≤ (det (gram ℂ c)).re := by
  let e := (Fintype.equivFin ι).symm
  have h := re_det_gram_proj_le_fin Y (Fintype.card ι) (c ∘ e)
  rwa [det_gram_comp_equiv e c, show (fun i ↦ Y.starProjection ((c ∘ e) i)) =
    (fun i ↦ Y.starProjection (c i)) ∘ e from rfl, det_gram_comp_equiv] at h

/- English proof (translation)
Use `set U := Submodule.span ℂ (Set.range v)`. Establish `hUW : U ≤ W` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)`. Rewrite using `[det_gram_sumElim_eq, Complex.mul_re, im_det_gram v, zero_mul, sub_zero]`. Use `mul_le_mul_of_nonneg_left ?_ (det_gram_re_nonneg v)` and prove the remaining obligations. Establish `hQ : (fun j ↦ Wᗮ.starProjection (u j)) = fun j ↦ Wᗮ.starProjection (u j - U.starProjection (u j))`.

Use function extensionality and compare the values at `j`. Rewrite using `[map_sub, sub_eq_self.mpr]`. Rewrite using `[Submodule.starProjection_apply_eq_zero_iff]`. Conclude with `Submodule.le_orthogonal_orthogonal W (hUW (U.starProjection_apply_mem (u j)))`. Rewrite using `[hQ]`.

Conclude with `re_det_gram_proj_le Wᗮ _`.
-/
theorem re_det_gram_sumElim_ge {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (W : Submodule ℂ V) [W.HasOrthogonalProjection] (v : ι → V) (hv : ∀ i, v i ∈ W) (u : κ → V) :
    (det (gram ℂ v)).re * (det (gram ℂ fun j ↦ Wᗮ.starProjection (u j))).re ≤
      (det (gram ℂ (Sum.elim v u))).re := by
  set U := Submodule.span ℂ (Set.range v)
  have hUW : U ≤ W := Submodule.span_le.mpr (Set.range_subset_iff.mpr hv)
  rw [det_gram_sumElim_eq, Complex.mul_re, im_det_gram v, zero_mul, sub_zero]
  refine mul_le_mul_of_nonneg_left ?_ (det_gram_re_nonneg v)
  have hQ : (fun j ↦ Wᗮ.starProjection (u j)) =
      fun j ↦ Wᗮ.starProjection (u j - U.starProjection (u j)) := by
    funext j
    rw [map_sub, sub_eq_self.mpr]
    rw [Submodule.starProjection_apply_eq_zero_iff]
    exact Submodule.le_orthogonal_orthogonal W (hUW (U.starProjection_apply_mem (u j)))
  rw [hQ]
  exact re_det_gram_proj_le Wᗮ _

end GramGeometry2

end

end GroundTheory.Heights₂.Heights
