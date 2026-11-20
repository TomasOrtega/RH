import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGramDetSandwich
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.LoewnerDetBound
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine

open Matrix Filter Topology Asymptotics
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements
open scoped ComplexOrder

namespace LevelTowerAlt.MuBd

section Mat

/- English proof (translation)
Establish `hd : ∀ i, 0 ≤ (H i i).re ∧ (H i i).im = 0 ∧ (H i i).re ≤ c` using `fun i => by`. Establish `h1` using `Complex.nonneg_iff.1 (hH.diag_nonneg (i := i))`. Establish `h2` using `(Complex.nonneg_iff.1 (hc.diag_nonneg (i := i))).1`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Complex.sub_re, Complex.ofReal_re] at h2`. Conclude with `⟨h1.1, h1.2.symm, by linarith⟩`.

Establish `h2` using `(Complex.nonneg_iff.1 (hH.submatrix ![p, q]).det_nonneg).1`. Rewrite `h2` using `[det_fin_two]`. Simplify using `only [submatrix_apply, cons_val_zero, cons_val_one] at h2`. Establish `e : H q p = starRingEnd ℂ (H p q)` using `(hH.1.apply q p).symm`. Rewrite `h2` using `[e, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, (hd p).2.1, zero_mul, sub_zero]`.

Establish `h3 : (H p p).re * (H q q).re ≤ c * c` using `mul_le_mul (hd p).2.2 (hd q).2.2 (hd q).1 ((hd p).1.trans (hd p).2.2)`. Conclude with `abs_le_of_sq_le_sq' (by nlinarith) ((hd p).1.trans (hd p).2.2) |>.2`.
-/
theorem norm_entry_le {n : Type} [Fintype n] [DecidableEq n] {H : Matrix n n ℂ} (hH : H.PosSemidef) {c : ℝ}
    (hc : ((c : ℂ) • (1 : Matrix n n ℂ) - H).PosSemidef) (p q : n) : ‖H p q‖ ≤ c := by
  have hd : ∀ i, 0 ≤ (H i i).re ∧ (H i i).im = 0 ∧ (H i i).re ≤ c := fun i => by
    have h1 := Complex.nonneg_iff.1 (hH.diag_nonneg (i := i))
    have h2 := (Complex.nonneg_iff.1 (hc.diag_nonneg (i := i))).1
    simp only [Matrix.sub_apply, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Complex.sub_re,
      Complex.ofReal_re] at h2
    exact ⟨h1.1, h1.2.symm, by linarith⟩
  have h2 := (Complex.nonneg_iff.1 (hH.submatrix ![p, q]).det_nonneg).1
  rw [det_fin_two] at h2
  simp only [submatrix_apply, cons_val_zero, cons_val_one] at h2
  have e : H q p = starRingEnd ℂ (H p q) := (hH.1.apply q p).symm
  rw [e, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    (hd p).2.1, zero_mul, sub_zero] at h2
  have h3 : (H p p).re * (H q q).re ≤ c * c := mul_le_mul (hd p).2.2 (hd q).2.2 (hd q).1 ((hd p).1.trans (hd p).2.2)
  exact abs_le_of_sq_le_sq' (by nlinarith) ((hd p).1.trans (hd p).2.2) |>.2

/- English proof (translation)
Set `e : Fin j ⊕ Fin (N - j) ≃ Fin N` to `finSumFinEquiv.trans (finCongr (by omega))`. Establish `el : ∀ a, e (Sum.inl a) = headIdx hj a` using `fun a => by ext; simp [e, headIdx]`. Establish `er : ∀ k, e (Sum.inr k) = tailIdx hj k` using `fun k => by ext; simp [e, tailIdx]`. Use `set A := G.submatrix (headIdx hj) (headIdx hj) with hA`. Use `set B := G.submatrix (headIdx hj) (tailIdx hj) with hB`.

Use `set D := G.submatrix (tailIdx hj) (tailIdx hj) with hD`. Establish `hb : G.submatrix e e = fromBlocks A B Bᴴ D`. Apply the tactic sequence `ext (a | a) (b | b) <;> simp [el, er, hA, hB, hD]`. Conclude with `(hG.1.apply _ _).symm`. Establish `hAp : A.PosDef` using `hG.submatrix (Fin.castLE_injective hj)`.

Establish `hDp : D.PosSemidef` using `hG.posSemidef.submatrix _`. Use `letI : Invertible A := hAp.isUnit.invertible`. Establish `hS : (D - Bᴴ * A⁻¹ * B).PosSemidef` using `(PosDef.fromBlocks₁₁ B D hAp).1 (hb ▸ hG.posSemidef.submatrix e)`. Establish `hT : (Bᴴ * A⁻¹ * B).PosSemidef` using `hAp.inv.posSemidef.conjTranspose_mul_mul_same B`. Establish `hdet : G.det = A.det * (D - Bᴴ * A⁻¹ * B).det`.

Rewrite using `[← det_submatrix_equiv_self e, hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]`. Establish `h1` using `(norm_det_le_of_loewner (H := D - Bᴴ * A⁻¹ * B) (A := D) one_pos (by simpa using hT) (by simpa using hDp.add hS)).2.2`. Establish `h2` using `Complex.pos_iff.1 hAp.det_pos`. Unfold `quotNormSq`. Rewrite using `[← hA, hdet, Complex.mul_re, ← h2.2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h2.1.ne']`.

Conclude with `(Complex.re_le_norm _).trans (by simpa using h1)`.
-/
theorem quotNormSq_le {j N : ℕ} (hj : j ≤ N) {G : Matrix (Fin N) (Fin N) ℂ} (hG : G.PosDef) :
    quotNormSq hj G ≤ (G.submatrix (tailIdx hj) (tailIdx hj)).det.re := by
  let e : Fin j ⊕ Fin (N - j) ≃ Fin N := finSumFinEquiv.trans (finCongr (by omega))
  have el : ∀ a, e (Sum.inl a) = headIdx hj a := fun a => by ext; simp [e, headIdx]
  have er : ∀ k, e (Sum.inr k) = tailIdx hj k := fun k => by ext; simp [e, tailIdx]
  set A := G.submatrix (headIdx hj) (headIdx hj) with hA
  set B := G.submatrix (headIdx hj) (tailIdx hj) with hB
  set D := G.submatrix (tailIdx hj) (tailIdx hj) with hD
  have hb : G.submatrix e e = fromBlocks A B Bᴴ D := by
    ext (a | a) (b | b) <;> simp [el, er, hA, hB, hD]
    exact (hG.1.apply _ _).symm
  have hAp : A.PosDef := hG.submatrix (Fin.castLE_injective hj)
  have hDp : D.PosSemidef := hG.posSemidef.submatrix _
  letI : Invertible A := hAp.isUnit.invertible
  have hS : (D - Bᴴ * A⁻¹ * B).PosSemidef := (PosDef.fromBlocks₁₁ B D hAp).1 (hb ▸ hG.posSemidef.submatrix e)
  have hT : (Bᴴ * A⁻¹ * B).PosSemidef := hAp.inv.posSemidef.conjTranspose_mul_mul_same B
  have hdet : G.det = A.det * (D - Bᴴ * A⁻¹ * B).det := by
    rw [← det_submatrix_equiv_self e, hb, det_fromBlocks₁₁, invOf_eq_nonsing_inv]
  have h1 := (norm_det_le_of_loewner (H := D - Bᴴ * A⁻¹ * B) (A := D) one_pos
    (by simpa using hT) (by simpa using hDp.add hS)).2.2
  have h2 := Complex.pos_iff.1 hAp.det_pos
  unfold quotNormSq
  rw [← hA, hdet, Complex.mul_re, ← h2.2, zero_mul, sub_zero, mul_div_cancel_left₀ _ h2.1.ne']
  exact (Complex.re_le_norm _).trans (by simpa using h1)

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]`.
-/
theorem submatrix_gram' {N k : ℕ} (A H : Matrix (Fin N) (Fin N) ℂ) (e : Fin k → Fin N) :
    (Aᴴ * H * A).submatrix e e = (A.submatrix id e)ᴴ * H * A.submatrix id e := by
  ext a b
  simp [Matrix.mul_apply, Matrix.submatrix_apply, Matrix.conjTranspose_apply]

end Mat

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

structure Gr {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (l : Filter V) (L E : V → ℝ) (f : V → F) : Prop where
  diff : ∀ᶠ t in l, DifferentiableAt ℝ f t
  bdd : f =O[l] L
  der : fderiv ℝ f =O[l] E

variable {l : Filter V} {L E : V → ℝ}

section Gen

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/- English proof (translation)
Assemble the required witnesses or components as `⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_zero _ _, by rw [fderiv_fun_const]; exact isBigO_zero _ _⟩`.
-/
theorem Gr.zero : Gr l L E (fun _ => (0 : F)) :=
  ⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_zero _ _, by
    rw [fderiv_fun_const]; exact isBigO_zero _ _⟩

/- English proof (translation)
Use `⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_add h.2, hf.bdd.add hg.bdd, (hf.der.add hg.der).congr' ?_ EventuallyEq.rfl⟩` and prove the remaining obligations. Use `filter_upwards [hf.diff, hg.diff] with t h1 h2`. Rewrite using `[fderiv_fun_add h1 h2]`.
-/
theorem Gr.add {f g : V → F} (hf : Gr l L E f) (hg : Gr l L E g) : Gr l L E fun t => f t + g t := by
  refine ⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_add h.2, hf.bdd.add hg.bdd,
    (hf.der.add hg.der).congr' ?_ EventuallyEq.rfl⟩
  filter_upwards [hf.diff, hg.diff] with t h1 h2
  rw [fderiv_fun_add h1 h2]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Gr.zero`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `(h i (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem Gr.sum {σ : Type} (s : Finset σ) {f : σ → V → F} (h : ∀ i ∈ s, Gr l L E (f i)) :
    Gr l L E fun t => ∑ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Gr.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Use `⟨hf.diff.mono fun t h => T.differentiableAt.comp t h, (T.isBigO_comp f l).trans hf.bdd, ?_⟩` and prove the remaining obligations. Use `(((ContinuousLinearMap.compL ℝ V F G T).isBigO_comp (fderiv ℝ f) l).trans hf.der).congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [hf.diff] with t h`. Conclude with `((T.hasFDerivAt.comp t h.hasFDerivAt).fderiv).symm`.
-/
theorem Gr.clm {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (T : F →L[ℝ] G) {f : V → F}
    (hf : Gr l L E f) : Gr l L E fun t => T (f t) := by
  refine ⟨hf.diff.mono fun t h => T.differentiableAt.comp t h, (T.isBigO_comp f l).trans hf.bdd, ?_⟩
  refine (((ContinuousLinearMap.compL ℝ V F G T).isBigO_comp (fderiv ℝ f) l).trans hf.der).congr' ?_
    EventuallyEq.rfl
  filter_upwards [hf.diff] with t h
  exact ((T.hasFDerivAt.comp t h.hasFDerivAt).fderiv).symm

/- English proof (translation)
Assemble the required witnesses or components as `⟨((hf.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero).filter_mono hl, ((hf.continuousAt.isBigO_one ℝ).mono hl).trans hL, ((((hf.fderiv_right (m := 0) (by simp)).continuousAt).isBigO_one ℝ).mono hl).trans hE⟩`.
-/
theorem Gr.of_contDiffAt {t₀ : V} (hl : l ≤ 𝓝 t₀) (hL : (fun _ => (1 : ℝ)) =O[l] L) (hE : (fun _ => (1 : ℝ)) =O[l] E)
    {f : V → F} (hf : ContDiffAt ℝ 1 f t₀) : Gr l L E f :=
  ⟨((hf.eventually (by simp)).mono fun _ h => h.differentiableAt one_ne_zero).filter_mono hl,
    ((hf.continuousAt.isBigO_one ℝ).mono hl).trans hL,
    ((((hf.fderiv_right (m := 0) (by simp)).continuousAt).isBigO_one ℝ).mono hl).trans hE⟩

end Gen

local notation "𝟙" => (fun _ => (1 : ℝ))

/- English proof (translation)
Assemble the required witnesses or components as `⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_const_const _ one_ne_zero _, by rw [fderiv_fun_const]; exact isBigO_zero _ _⟩`.
-/
theorem Gr.const (c : ℂ) : Gr l 𝟙 E (fun _ => c) :=
  ⟨Eventually.of_forall fun _ => differentiableAt_const _, isBigO_const_const _ one_ne_zero _, by
    rw [fderiv_fun_const]; exact isBigO_zero _ _⟩

/- English proof (translation)
Use `⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_mul h.2, by simpa using hf.bdd.mul hg.bdd, ?_⟩` and prove the remaining obligations. Establish `h1 : (fun t => f t • fderiv ℝ g t) =O[l] E` using `by simpa using hf.bdd.smul hg.der`. Establish `h2 : (fun t => g t • fderiv ℝ f t) =O[l] E` using `by simpa using hg.bdd.smul hf.der`. Use `(h1.add h2).congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [hf.diff, hg.diff] with t h1 h2`.

Rewrite using `[fderiv_fun_mul h1 h2]`.
-/
theorem Gr.mul {f g : V → ℂ} (hf : Gr l 𝟙 E f) (hg : Gr l 𝟙 E g) : Gr l 𝟙 E fun t => f t * g t := by
  refine ⟨(hf.diff.and hg.diff).mono fun t h => h.1.fun_mul h.2, by simpa using hf.bdd.mul hg.bdd, ?_⟩
  have h1 : (fun t => f t • fderiv ℝ g t) =O[l] E := by simpa using hf.bdd.smul hg.der
  have h2 : (fun t => g t • fderiv ℝ f t) =O[l] E := by simpa using hg.bdd.smul hf.der
  refine (h1.add h2).congr' ?_ EventuallyEq.rfl
  filter_upwards [hf.diff, hg.diff] with t h1 h2
  rw [fderiv_fun_mul h1 h2]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Gr.const 1`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.prod_insert hi]`. Conclude with `(h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))`.
-/
theorem Gr.prod {σ : Type} (s : Finset σ) {f : σ → V → ℂ} (h : ∀ i ∈ s, Gr l 𝟙 E (f i)) :
    Gr l 𝟙 E fun t => ∏ i ∈ s, f i t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Gr.const 1
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).mul (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/- English proof (translation)
Simplify using `only [det_apply']`. Conclude with `Gr.sum _ fun σ _ => (Gr.const _).mul (Gr.prod _ fun i _ => h _ _)`.
-/
theorem Gr.det {n : ℕ} {M : V → Matrix (Fin n) (Fin n) ℂ} (h : ∀ p q, Gr l 𝟙 E fun t => M t p q) :
    Gr l 𝟙 E fun t => (M t).det := by
  simp only [det_apply']
  exact Gr.sum _ fun σ _ => (Gr.const _).mul (Gr.prod _ fun i _ => h _ _)

/- English proof (translation)
Simplify using `only [Matrix.mul_apply, Matrix.conjTranspose_apply]`. Conclude with `Gr.sum _ fun k _ => (Gr.sum _ fun i _ => (Gr.clm (Complex.conjCLE : ℂ →L[ℝ] ℂ) (hA i p)).mul (hB i k)).mul (hA k q)`.
-/
theorem Gr.sandwich {n : ℕ} {A B : V → Matrix (Fin n) (Fin n) ℂ} (hA : ∀ p q, Gr l 𝟙 E fun t => A t p q)
    (hB : ∀ p q, Gr l 𝟙 E fun t => B t p q) (p q : Fin n) : Gr l 𝟙 E fun t => ((A t)ᴴ * B t * A t) p q := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Gr.sum _ fun k _ => (Gr.sum _ fun i _ =>
    (Gr.clm (Complex.conjCLE : ℂ →L[ℝ] ℂ) (hA i p)).mul (hB i k)).mul (hA k q)

/- English proof (translation)
Establish `hpos : ∀ᶠ t in l, 0 < R t ∧ 0 < g t` using `by filter_upwards [hR, hlo] with t h1 h2`. Use `(Real.exp_pos 1).trans_le h1` as an intermediate fact. Conclude with `⟨this, (by positivity : 0 < c / R t ^ m).trans_le h2⟩`. Use `⟨(hg.diff.and hpos).mono fun t h => h.1.log h.2.2.ne', ?_, ?_⟩` and prove the remaining obligations. Take `⟨C, hC0, hC⟩` from `hg.bdd.exists_pos`.

Use `IsBigO.of_bound (|Real.log c| + m + |Real.log C|) ?_` and prove the remaining obligations. Use `filter_upwards [hC.bound, hR, hlo, hpos] with t h1 h2 h3 h4`. Establish `hL : 1 ≤ Real.log (R t)`. Rewrite using `[Real.le_log_iff_exp_le h4.1]`. Conclude with `h2`.

Rewrite `h1` using `[norm_one, mul_one, Real.norm_of_nonneg h4.2.le]`. Establish `u` using `Real.log_le_log h4.2 h1`. Establish `hRp` using `h4.1`. Establish `d` using `Real.log_le_log (by positivity) h3`. Rewrite `d` using `[Real.log_div hc.ne' (pow_pos h4.1 m).ne', Real.log_pow]`.

Rewrite using `[Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (R t)), Real.norm_eq_abs, abs_le]`. Establish `a1` using `le_mul_of_one_le_right (abs_nonneg (Real.log c)) hL`. Establish `a2` using `le_mul_of_one_le_right (abs_nonneg (Real.log C)) hL`. Establish `a3` using `neg_abs_le (Real.log c)`. Establish `a4` using `le_abs_self (Real.log C)`.

Establish `a5` using `abs_nonneg (Real.log C)`. Establish `a6` using `abs_nonneg (Real.log c)`. Establish `a7 : (0 : ℝ) ≤ m * Real.log (R t)` using `mul_nonneg (Nat.cast_nonneg m) (by linarith)`. Apply the tactic sequence `constructor <;> nlinarith`. Establish `h1 : (fun t => (g t)⁻¹) =O[l] fun t => R t ^ m`.

Use `IsBigO.of_bound c⁻¹ ?_` and prove the remaining obligations. Use `filter_upwards [hlo, hpos] with t h3 h4`. Establish `hRp` using `h4.1`. Rewrite using `[Real.norm_of_nonneg (inv_pos.2 h4.2).le, Real.norm_of_nonneg (pow_pos hRp m).le]`. Use `(inv_anti₀ (by positivity) h3).trans_eq ?_` and prove the remaining obligations.

Rewrite using `[inv_div, div_eq_inv_mul]`. Use `(h1.smul hg.der).congr' ?_ EventuallyEq.rfl` and prove the remaining obligations. Use `filter_upwards [hg.diff, hpos] with t h h4`. Rewrite using `[fderiv.log h h4.2.ne']`.
-/
theorem Gr.log {g R : V → ℝ} (hg : Gr l 𝟙 E g) (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t) {c : ℝ} (hc : 0 < c) {m : ℕ}
    (hlo : ∀ᶠ t in l, c / R t ^ m ≤ g t) :
    Gr l (fun t => Real.log (R t)) (fun t => R t ^ m * E t) fun t => Real.log (g t) := by
  have hpos : ∀ᶠ t in l, 0 < R t ∧ 0 < g t := by
    filter_upwards [hR, hlo] with t h1 h2
    have := (Real.exp_pos 1).trans_le h1
    exact ⟨this, (by positivity : 0 < c / R t ^ m).trans_le h2⟩
  refine ⟨(hg.diff.and hpos).mono fun t h => h.1.log h.2.2.ne', ?_, ?_⟩
  · obtain ⟨C, hC0, hC⟩ := hg.bdd.exists_pos
    refine IsBigO.of_bound (|Real.log c| + m + |Real.log C|) ?_
    filter_upwards [hC.bound, hR, hlo, hpos] with t h1 h2 h3 h4
    have hL : 1 ≤ Real.log (R t) := by
      rw [Real.le_log_iff_exp_le h4.1]; exact h2
    rw [norm_one, mul_one, Real.norm_of_nonneg h4.2.le] at h1
    have u := Real.log_le_log h4.2 h1
    have hRp := h4.1
    have d := Real.log_le_log (by positivity) h3
    rw [Real.log_div hc.ne' (pow_pos h4.1 m).ne', Real.log_pow] at d
    rw [Real.norm_of_nonneg (by linarith : 0 ≤ Real.log (R t)), Real.norm_eq_abs, abs_le]
    have a1 := le_mul_of_one_le_right (abs_nonneg (Real.log c)) hL
    have a2 := le_mul_of_one_le_right (abs_nonneg (Real.log C)) hL
    have a3 := neg_abs_le (Real.log c)
    have a4 := le_abs_self (Real.log C)
    have a5 := abs_nonneg (Real.log C)
    have a6 := abs_nonneg (Real.log c)
    have a7 : (0 : ℝ) ≤ m * Real.log (R t) := mul_nonneg (Nat.cast_nonneg m) (by linarith)
    constructor <;> nlinarith
  · have h1 : (fun t => (g t)⁻¹) =O[l] fun t => R t ^ m := by
      refine IsBigO.of_bound c⁻¹ ?_
      filter_upwards [hlo, hpos] with t h3 h4
      have hRp := h4.1
      rw [Real.norm_of_nonneg (inv_pos.2 h4.2).le, Real.norm_of_nonneg (pow_pos hRp m).le]
      refine (inv_anti₀ (by positivity) h3).trans_eq ?_
      rw [inv_div, div_eq_inv_mul]
    refine (h1.smul hg.der).congr' ?_ EventuallyEq.rfl
    filter_upwards [hg.diff, hpos] with t h h4
    rw [fderiv.log h h4.2.ne']

/- English proof (translation)
Rewrite `h0` using `[Matrix.mul_one]`. Establish `hp` using `(Complex.pos_iff.1 h0.det_pos).1`. Establish `hΦ : Continuous fun M : Matrix (Fin N) (Fin k) ℂ => (Mᴴ * M).det.re` using `Complex.continuous_re.comp ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det)`. Establish `hev : ∀ᶠ t in 𝓝 t₀, ((A t₀)ᴴ * A t₀).det.re / 2 < ((A t)ᴴ * A t).det.re` using `(hΦ.continuousAt.comp hA).eventually (lt_mem_nhds (half_lt_self hp))`. Use `⟨C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2), by positivity, ?_⟩` and prove the remaining obligations.

Use `filter_upwards [hH, hR, hev.filter_mono hl] with t h1 h2 h3`. Establish `hR1 : 1 ≤ R t` using `(Real.one_le_exp zero_le_one).trans h2`. Establish `hR0 : 0 < R t` using `one_pos.trans_le hR1`. Use `le_trans ?_ (GramDetSandwich.proof (H t) (A t) c (C * R t) hc h1.1 h1.2.1 h1.2.2).1` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[mul_inv, mul_pow, inv_pow (R t)]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ _ := mul_le_mul_of_nonneg_left h3.le (by positivity)`.
-/
theorem det_lower {N k : ℕ} (hk : k ≤ N) {t₀ : V} (hl : l ≤ 𝓝 t₀) {R : V → ℝ} (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t)
    {A : V → Matrix (Fin N) (Fin k) ℂ} (hA : ContinuousAt A t₀) (h0 : ((A t₀)ᴴ * (1 : Matrix (Fin N) (Fin N) ℂ) * A t₀).PosDef)
    {H : V → Matrix (Fin N) (Fin N) ℂ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hH : ∀ᶠ t in l, (H t).PosDef ∧ ((H t)⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((C * R t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (H t)⁻¹).PosSemidef) :
    ∃ c' > (0 : ℝ), ∀ᶠ t in l, c' / R t ^ N ≤ ((A t)ᴴ * H t * A t).det.re := by
  rw [Matrix.mul_one] at h0
  have hp := (Complex.pos_iff.1 h0.det_pos).1
  have hΦ : Continuous fun M : Matrix (Fin N) (Fin k) ℂ => (Mᴴ * M).det.re :=
    Complex.continuous_re.comp ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).matrix_det)
  have hev : ∀ᶠ t in 𝓝 t₀, ((A t₀)ᴴ * A t₀).det.re / 2 < ((A t)ᴴ * A t).det.re :=
    (hΦ.continuousAt.comp hA).eventually (lt_mem_nhds (half_lt_self hp))
  refine ⟨C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2), by positivity, ?_⟩
  filter_upwards [hH, hR, hev.filter_mono hl] with t h1 h2 h3
  have hR1 : 1 ≤ R t := (Real.one_le_exp zero_le_one).trans h2
  have hR0 : 0 < R t := one_pos.trans_le hR1
  refine le_trans ?_ (GramDetSandwich.proof (H t) (A t) c (C * R t) hc h1.1 h1.2.1 h1.2.2).1
  calc C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) / R t ^ N
      ≤ C⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) / R t ^ k :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_right₀ hR1 hk)
    _ = (C * R t)⁻¹ ^ k * (((A t₀)ᴴ * A t₀).det.re / 2) := by
        rw [mul_inv, mul_pow, inv_pow (R t)]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h3.le (by positivity)

/- English proof (translation)
Establish `hSg : ∀ p q, Gr l 𝟙 E fun t => S t p q` using `fun p q => Gr.of_contDiffAt hl (isBigO_refl _ _) hE (hS p q)`. Establish `hHg : ∀ p q, Gr l 𝟙 E fun t => H t p q` using `fun p q => ⟨hd p q, IsBigO.of_bound c⁻¹ (hH.mono fun t h => by`. Rewrite using `[norm_one, mul_one]`. Conclude with `norm_entry_le h.1.posSemidef (GramDetSandwich.loewner_inv hN _ _ _ hc h.1 h.2.1 h.2.2).2.2 p q), hD p q⟩`. Establish `hGg` using `Gr.sandwich hSg hHg`.

Establish `hSc : ContinuousAt S t₀` using `continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hS p q).continuousAt`. Establish `hPD : ((S t₀)ᴴ * 1 * S t₀).PosDef` using `Matrix.PosDef.one.conjTranspose_mul_mul_same h0`. Take `⟨c1, hc1, h1⟩` from `det_lower le_rfl hl hR hSc hPD hc hC hH`. Take `⟨c2, hc2, h2⟩` from `det_lower hj hl hR (A := fun t => (S t).submatrix id (headIdx hj)) ((continuous_id.matrix_submatrix _ _).continuousAt.comp hSc) (by rw [← submatrix_gram']; exact hPD.submatrix (Fin.castLE_injective hj)) hc hC hH`. Simplify using `only [← submatrix_gram'] at h2`.

Establish `g1` using `(Gr.clm Complex.reCLM (Gr.det hGg)).log hR hc1 h1`. Establish `g2` using `(Gr.clm Complex.reCLM (Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (headIdx hj) (headIdx hj)) fun p q => hGg _ _)).log hR hc2 h2`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `(Gr.clm ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g1).add (Gr.clm ((-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g2)` as an intermediate fact. Use `this using 2 with t` and compare the differences between its conclusion and the goal.

Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨B, hB⟩` from `(Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (tailIdx hj) (tailIdx hj)) fun p q => hGg _ _).bdd.bound`. Use `⟨B, ?_⟩` and prove the remaining obligations. Use `filter_upwards [hB, hG] with t h1 h2`.

Rewrite `h1` using `[norm_one, mul_one]`. Conclude with `(quotNormSq_le hj h2).trans ((Complex.re_le_norm _).trans h1)`.
-/
theorem quot_bounds {j N : ℕ} (hj : j ≤ N) (hN : 0 < N) {t₀ : V} (hl : l ≤ 𝓝 t₀) {R : V → ℝ}
    (hR : ∀ᶠ t in l, Real.exp 1 ≤ R t) (hE : 𝟙 =O[l] E)
    {S : V → Matrix (Fin N) (Fin N) ℂ} (hS : ∀ p q, ContDiffAt ℝ 1 (fun t => S t p q) t₀)
    (h0 : Function.Injective (S t₀).mulVec)
    {H : V → Matrix (Fin N) (Fin N) ℂ} {c C : ℝ} (hc : 0 < c) (hC : 0 < C)
    (hH : ∀ᶠ t in l, (H t).PosDef ∧ ((H t)⁻¹ - (c : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)).PosSemidef ∧
      (((C * R t : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - (H t)⁻¹).PosSemidef)
    (hd : ∀ p q, ∀ᶠ t in l, DifferentiableAt ℝ (fun s => H s p q) t)
    (hD : ∀ p q, fderiv ℝ (fun s => H s p q) =O[l] E)
    (hG : ∀ᶠ t in l, ((S t)ᴴ * H t * S t).PosDef) :
    Gr l (fun t => Real.log (R t)) (fun t => R t ^ N * E t) (fun t =>
      (Real.log ((S t)ᴴ * H t * S t).det.re -
        Real.log (((S t)ᴴ * H t * S t).submatrix (headIdx hj) (headIdx hj)).det.re) / 2) ∧
    ∃ B : ℝ, ∀ᶠ t in l, quotNormSq hj ((S t)ᴴ * H t * S t) ≤ B := by
  have hSg : ∀ p q, Gr l 𝟙 E fun t => S t p q := fun p q => Gr.of_contDiffAt hl (isBigO_refl _ _) hE (hS p q)
  have hHg : ∀ p q, Gr l 𝟙 E fun t => H t p q := fun p q => ⟨hd p q, IsBigO.of_bound c⁻¹ (hH.mono fun t h => by
    rw [norm_one, mul_one]
    exact norm_entry_le h.1.posSemidef (GramDetSandwich.loewner_inv hN _ _ _ hc h.1 h.2.1 h.2.2).2.2 p q), hD p q⟩
  have hGg := Gr.sandwich hSg hHg
  have hSc : ContinuousAt S t₀ := continuousAt_pi.2 fun p => continuousAt_pi.2 fun q => (hS p q).continuousAt
  have hPD : ((S t₀)ᴴ * 1 * S t₀).PosDef := Matrix.PosDef.one.conjTranspose_mul_mul_same h0
  obtain ⟨c1, hc1, h1⟩ := det_lower le_rfl hl hR hSc hPD hc hC hH
  obtain ⟨c2, hc2, h2⟩ := det_lower hj hl hR (A := fun t => (S t).submatrix id (headIdx hj))
    ((continuous_id.matrix_submatrix _ _).continuousAt.comp hSc)
    (by rw [← submatrix_gram']; exact hPD.submatrix (Fin.castLE_injective hj)) hc hC hH
  simp only [← submatrix_gram'] at h2
  have g1 := (Gr.clm Complex.reCLM (Gr.det hGg)).log hR hc1 h1
  have g2 := (Gr.clm Complex.reCLM (Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (headIdx hj) (headIdx hj))
    fun p q => hGg _ _)).log hR hc2 h2
  refine ⟨?_, ?_⟩
  · have := (Gr.clm ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g1).add
      (Gr.clm ((-1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) g2)
    convert this using 2 with t
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, Complex.reCLM_apply]
    ring
  · obtain ⟨B, hB⟩ := (Gr.det (M := fun t => ((S t)ᴴ * H t * S t).submatrix (tailIdx hj) (tailIdx hj))
      fun p q => hGg _ _).bdd.bound
    refine ⟨B, ?_⟩
    filter_upwards [hB, hG] with t h1 h2
    rw [norm_one, mul_one] at h1
    exact (quotNormSq_le hj h2).trans ((Complex.re_le_norm _).trans h1)

end LevelTowerAlt.MuBd
