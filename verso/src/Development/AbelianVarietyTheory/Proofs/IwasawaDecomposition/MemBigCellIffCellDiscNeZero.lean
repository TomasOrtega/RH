import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TruncMatMemSubalgebra

set_option autoImplicit false

noncomputable section

open Module TopologicalSpace Matrix

namespace GlobalTheory.FlagPts

/- English proof (translation)
Rewrite using `[Basis.mem_span_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h c hc`. Assume the negation of the conclusion as `hne`. Use `h (Finsupp.mem_support_iff.2 hne)` as an intermediate fact.

Simplify using `only [Set.mem_setOf_eq] at this`. Use linear arithmetic over natural numbers and integers. Introduce `h c hc`. Simplify using `only [Finset.mem_coe, Finsupp.mem_support_iff] at hc`. Simplify using `only [Set.mem_setOf_eq]`.

Assume the negation of the conclusion as `hlt`. Conclude with `hc (h c (by omega))`.
-/
theorem mem_span_tail_iff {W : Type} [AddCommGroup W] {k : Type} [Field k] [Module k W] {d : ℕ}
    (e : Basis (Fin d) k W) (m : ℕ) (v : W) :
    v ∈ Submodule.span k (e '' {a | m ≤ (a : ℕ)}) ↔ ∀ c : Fin d, (c : ℕ) < m → e.repr v c = 0 := by
  rw [Basis.mem_span_image]
  constructor
  · intro h c hc
    by_contra hne
    have := h (Finsupp.mem_support_iff.2 hne)
    simp only [Set.mem_setOf_eq] at this
    omega
  · intro h c hc
    simp only [Finset.mem_coe, Finsupp.mem_support_iff] at hc
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    exact hc (h c (by omega))

/- English proof (translation)
Establish `hlow (c : Fin d) (hc : (c : ℕ) < m) : (truncMat m M *ᵥ y) c = ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e`. Simplify using `only [Matrix.mulVec, dotProduct, truncMat]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Distinguish the cases in `he : (e : ℕ) < m`. Simplify using `[hc, he]`.

Establish `hce : c ≠ e` using `fun h => he (h ▸ hc)`. Simplify using `[he, hce]`. Establish `hhigh (c : Fin d) (hc : ¬ (c : ℕ) < m) : (truncMat m M *ᵥ y) c = y c`. Simplify using `only [Matrix.mulVec, dotProduct, truncMat]`. Rewrite using `[Finset.sum_eq_single c]`.

Simplify using `[hc]`. Introduce `e _ hec`. Simplify using `[hc, Ne.symm hec]`. Simplify using the standard rewrite rules. Establish `hsum (h : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) (c : Fin d) : ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e = (M *ᵥ y) c`.

Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Distinguish the cases in `he : (e : ℕ) < m`. Simplify using `[he]`. Simplify using `[he, h e (by omega)]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0` using `fun e he => by`. Rewrite using `[← hhigh e (by omega)]; exact congrFun h e`. Use `⟨h1, fun c hc => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hsum h1 c, ← hlow c hc]`. Conclude with `congrFun h c`. Introduce and unpack `⟨h1, h2⟩`. Use function extensionality and compare the values at `c`. Distinguish the cases in `hc : (c : ℕ) < m`.

Rewrite using `[hlow c hc, hsum h1 c]`. Conclude with `h2 c hc`. Rewrite using `[hhigh c hc]; exact h1 c (by omega)`.
-/
theorem truncMat_mulVec_eq_zero_iff {R : Type} [CommRing R] {d : ℕ} (m : ℕ)
    (M : Matrix (Fin d) (Fin d) R) (y : Fin d → R) :
    truncMat m M *ᵥ y = 0 ↔
      (∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) ∧ ∀ c : Fin d, (c : ℕ) < m → (M *ᵥ y) c = 0 := by
  have hlow (c : Fin d) (hc : (c : ℕ) < m) :
      (truncMat m M *ᵥ y) c = ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [hc, he]
    · have hce : c ≠ e := fun h => he (h ▸ hc)
      simp [he, hce]
  have hhigh (c : Fin d) (hc : ¬ (c : ℕ) < m) : (truncMat m M *ᵥ y) c = y c := by
    simp only [Matrix.mulVec, dotProduct, truncMat]
    rw [Finset.sum_eq_single c]
    · simp [hc]
    · intro e _ hec
      simp [hc, Ne.symm hec]
    · simp
  have hsum (h : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0) (c : Fin d) :
      ∑ e : Fin d, (if (e : ℕ) < m then M c e else 0) * y e = (M *ᵥ y) c := by
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases he : (e : ℕ) < m
    · simp [he]
    · simp [he, h e (by omega)]
  constructor
  · intro h
    have h1 : ∀ e : Fin d, m ≤ (e : ℕ) → y e = 0 := fun e he => by
      rw [← hhigh e (by omega)]; exact congrFun h e
    refine ⟨h1, fun c hc => ?_⟩
    rw [← hsum h1 c, ← hlow c hc]
    exact congrFun h c
  · rintro ⟨h1, h2⟩
    funext c
    by_cases hc : (c : ℕ) < m
    · rw [hlow c hc, hsum h1 c]; exact h2 c hc
    · rw [hhigh c hc]; exact h1 c (by omega)

variable {k : Type} [Field k] {ι : Type} {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)]

/- English proof (translation)
Establish `h` using `congrArg (fun w => (b i).repr w c) ((g i).sum_equivFun v)`. Simplify using `only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[← h]`. Simplify using `only [Matrix.mulVec, dotProduct, frameMat]`. Conclude with `Finset.sum_congr rfl fun e _ => mul_comm _ _`.
-/
theorem repr_eq_frameMat_mulVec (b g : Frames k V) (i : ι) (v : V i) (c : Fin (finrank k (V i))) :
    (b i).repr v c = (frameMat b g i *ᵥ (g i).equivFun v) c := by
  have h := congrArg (fun w => (b i).repr w c) ((g i).sum_equivFun v)
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
    Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  simp only [Matrix.mulVec, dotProduct, frameMat]
  exact Finset.sum_congr rfl fun e _ => mul_comm _ _

/- English proof (translation)
Rewrite using `[Ne, ← Matrix.exists_mulVec_eq_zero_iff, Submodule.disjoint_def]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `h ⟨y, hy0, hy⟩`. Apply `hy0` to reduce the goal to its premises. Rewrite `hy` using `[truncMat_mulVec_eq_zero_iff]`.

Establish `hv : (g i).equivFun ((g i).equivFun.symm y) = y` using `LinearEquiv.apply_symm_apply _ _`. Establish `h0` using `h ((g i).equivFun.symm y) (mem_step_flags.2 fun a ha => by rw [← Basis.equivFun_apply, hv]; exact hy.1 a ha) ((mem_span_tail_iff (b i) m _).2 fun c hc => by`. Rewrite using `[repr_eq_frameMat_mulVec b g, hv]`. Conclude with `hy.2 c hc)`. Rewrite using `[← hv, h0, map_zero]`.

Introduce `h v hv1 hv2`. Assume the negation of the conclusion as `hv`. Use `h ⟨(g i).equivFun v, fun h0 => hv ((g i).equivFun.map_eq_zero_iff.1 h0), ?_⟩` and prove the remaining obligations. Rewrite using `[truncMat_mulVec_eq_zero_iff]`. Use `⟨fun e he => ?_, fun c hc => ?_⟩` and prove the remaining obligations.

Rewrite using `[Basis.equivFun_apply]`. Conclude with `mem_step_flags.1 hv1 e he`. Rewrite using `[← repr_eq_frameMat_mulVec b g]`. Conclude with `(mem_span_tail_iff (b i) m v).1 hv2 c hc`.
-/
theorem disjoint_step_iff_det_truncMat_ne_zero (b g : Frames k V) (i : ι) (m : ℕ) :
    Disjoint (g.flags.step i m) (Submodule.span k (b i '' {a | m ≤ (a : ℕ)})) ↔
      (truncMat m (frameMat b g i)).det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff, Submodule.disjoint_def]
  constructor
  · rintro h ⟨y, hy0, hy⟩
    apply hy0
    rw [truncMat_mulVec_eq_zero_iff] at hy
    have hv : (g i).equivFun ((g i).equivFun.symm y) = y := LinearEquiv.apply_symm_apply _ _
    have h0 := h ((g i).equivFun.symm y)
      (mem_step_flags.2 fun a ha => by rw [← Basis.equivFun_apply, hv]; exact hy.1 a ha)
      ((mem_span_tail_iff (b i) m _).2 fun c hc => by
        rw [repr_eq_frameMat_mulVec b g, hv]; exact hy.2 c hc)
    rw [← hv, h0, map_zero]
  · intro h v hv1 hv2
    by_contra hv
    refine h ⟨(g i).equivFun v, fun h0 => hv ((g i).equivFun.map_eq_zero_iff.1 h0), ?_⟩
    rw [truncMat_mulVec_eq_zero_iff]
    refine ⟨fun e he => ?_, fun c hc => ?_⟩
    · rw [Basis.equivFun_apply]; exact mem_step_flags.1 hv1 e he
    · rw [← repr_eq_frameMat_mulVec b g]; exact (mem_span_tail_iff (b i) m v).1 hv2 c hc

/- English proof (translation)
Simplify using `only [bigCell, Set.mem_setOf_eq, disjoint_step_iff_det_truncMat_ne_zero, cellDisc, Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]`. Prove the components needed by the constructor for the conclusion. Introduce `h i m`. Conclude with `h i m`. Introduce `h i m`.

Distinguish the cases in `hm : m ≤ finrank k (V i)`. Conclude with `h i ⟨m, by omega⟩`. Establish `heq : truncMat m (frameMat b g i) = truncMat (finrank k (V i)) (frameMat b g i)`. Use extensionality with `c e`. Establish `hc` using `c.2`.

Establish `he` using `e.2`. Simplify using `only [truncMat]`. Rewrite using `[if_pos ⟨by omega, by omega⟩, if_pos ⟨hc, he⟩]`. Rewrite using `[heq]`. Conclude with `h i ⟨finrank k (V i), by omega⟩`.
-/
theorem mem_bigCell_iff_cellDisc_ne_zero (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type)
    [∀ i, AddCommGroup (V i)] [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)]
    (b g : Frames k V) : g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := by
  simp only [bigCell, Set.mem_setOf_eq, disjoint_step_iff_det_truncMat_ne_zero, cellDisc,
    Finset.prod_ne_zero_iff, Finset.mem_univ, true_implies]
  constructor
  · intro h i m
    exact h i m
  · intro h i m
    by_cases hm : m ≤ finrank k (V i)
    · exact h i ⟨m, by omega⟩
    · have heq : truncMat m (frameMat b g i) = truncMat (finrank k (V i)) (frameMat b g i) := by
        ext c e
        have hc := c.2
        have he := e.2
        simp only [truncMat]
        rw [if_pos ⟨by omega, by omega⟩, if_pos ⟨hc, he⟩]
      rw [heq]
      exact h i ⟨finrank k (V i), by omega⟩

/- English proof (translation)
The claim follows from `mem_bigCell_iff_cellDisc_ne_zero`.
-/
example : ∀ (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b g : Frames k V),
    g.flags ∈ bigCell b ↔ cellDisc b g ≠ 0 := mem_bigCell_iff_cellDisc_ne_zero

end GlobalTheory.FlagPts
