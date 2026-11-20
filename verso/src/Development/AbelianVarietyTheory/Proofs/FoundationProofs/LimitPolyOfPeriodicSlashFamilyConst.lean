import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PolyDegreeSlashActionRightActionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvalPolyDegreeSlashAction
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.QConst

open Filter Topology

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
/- English proof (translation)
Break down `eq_or_ne p 0 with rfl | h` into its components or cases. Simplify using the standard rewrite rules. Conclude with `(natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)`.
-/
private theorem natDegree_lt_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) :
    p.natDegree < w + 1 := by
  rcases eq_or_ne p 0 with rfl | h
  · simp
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
/- English proof (translation)
Rewrite using `[eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]`. Use `(norm_sum_le _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[norm_mul, norm_pow]`.
-/
private theorem norm_eval_le_sum_of_mem_degreeLT {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (x : ℂ) : ‖p.eval x‖ ≤ ∑ j ∈ Finset.range (w + 1), ‖p.coeff j‖ * ‖x‖ ^ j := by
  rw [eval_eq_sum_range' (natDegree_lt_of_mem_degreeLT hp)]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  simp [norm_mul, norm_pow]

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
/- English proof (translation)
Establish `hn' : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp`.

Consider the case `succ k ih`. Establish `hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n` using `by push_cast; ring`. Simplify using `only [IsRoot.def, eval_sub, eval_C] at ih ⊢`. Rewrite using `[hk, hQ]`. Conclude with `ih`.

Establish `hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x}` using `Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n) (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot`. Rewrite using `[coeff_zero_eq_eval_zero]`. Conclude with `sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)`.
-/
private theorem eq_C_of_eval_add_natCast_eq {Q : ℂ[X]} {n : ℕ} (hn : 0 < n)
    (hQ : ∀ x : ℂ, Q.eval (x + n) = Q.eval x) : Q = C (Q.coeff 0) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hroot : ∀ k : ℕ, IsRoot (Q - C (Q.eval 0)) ((k : ℂ) * n) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hk : ((k + 1 : ℕ) : ℂ) * n = (k : ℂ) * n + n := by push_cast; ring
      simp only [IsRoot.def, eval_sub, eval_C] at ih ⊢
      rw [hk, hQ]
      exact ih
  have hinf : Set.Infinite {x | IsRoot (Q - C (Q.eval 0)) x} :=
    Set.infinite_of_injective_forall_mem (f := fun k : ℕ => (k : ℂ) * n)
      (fun a b hab => by exact_mod_cast mul_right_cancel₀ hn' hab) hroot
  rw [coeff_zero_eq_eval_zero]
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in
/- English proof (translation)
Establish `h1` using `((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero`. Establish `h2` using `h1.const_mul (Real.exp (c * b))`. Rewrite `h2` using `[mul_zero]`. Use `h2.congr fun y => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, id]`.

Rewrite using `[mul_add, Real.exp_add, neg_mul, Real.exp_neg]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem tendsto_exp_neg_mul_mul_add_pow_zero {c : ℝ} (hc : 0 < c) (b : ℝ) (m : ℕ) :
    Tendsto (fun y : ℝ => Real.exp (-c * y) * (b + y) ^ m) atTop (𝓝 0) := by
  have h1 := ((isLittleO_pow_exp_pos_mul_atTop m hc).comp_tendsto
    (tendsto_atTop_add_const_left atTop b tendsto_id)).tendsto_div_nhds_zero
  have h2 := h1.const_mul (Real.exp (c * b))
  rw [mul_zero] at h2
  refine h2.congr fun y => ?_
  simp only [Function.comp_apply, id]
  rw [mul_add, Real.exp_add, neg_mul, Real.exp_neg]
  field_simp

open Polynomial UpperHalfPlane in
open scoped MatrixGroups ModularForm in
open scoped Manifold in
open Filter Topology in

/- English proof (translation)
Introduce `w n V Q C' c hn hc hQ hV hper h`. Establish `hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1]`. Unfold `_root_.GlobalTheory.HeckeFamilyMatrices.mat`. Conclude with `ModularGroup.coe_T_zpow _`. Establish `htrans : ∀ (τ : ℍ) (x : ℂ), (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n)`.

Introduce `τ x`. Rewrite using `[← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]`. Simplify using the standard rewrite rules. Establish `hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ, ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w * ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j`. Introduce `τ hτ b hb x`.

Establish `hC' : 0 ≤ C'`. Establish `h0` using `h τ hτ 0 (Nat.zero_le _)`. Establish `: 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w` using `by positivity`. Use polynomial arithmetic with `[norm_nonneg ((V τ - Q).coeff 0)]`. Rewrite using `[Finset.mul_sum]`.

Use `(norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans (Finset.sum_le_sum fun j hj => ?_)` and prove the remaining obligations. Establish `hj' : j ≤ w` using `Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)`. Conclude with `mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w) (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)`. Use `eq_C_of_eval_add_natCast_eq hn fun x => ?_` and prove the remaining obligations. Use `set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j`.

Establish `hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤ C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w)`. Introduce `y hy`. Set `τ : ℍ` to `⟨(y : ℂ) * Complex.I, by simp; linarith⟩`. Establish `hτim : τ.im = y` using `by simp [τ, UpperHalfPlane.im]`. Establish `hτn : ‖(τ : ℂ)‖ = y`.

Simplify using `[τ, abs_of_pos (show (0 : ℝ) < y by linarith)]`. Establish `hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n`. Rewrite using `[ModularGroup.coe_T_zpow_smul_eq]`. Simplify using the standard rewrite rules. Establish `hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y`.

Rewrite using `[← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]`. Simplify using the standard rewrite rules. Establish `hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y`. Rewrite using `[hτ'c]`. Use `norm_add_le (τ : ℂ) (n : ℂ)` as an intermediate fact.

Rewrite `this` using `[hτn, Complex.norm_natCast]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn0 : (0 : ℝ) ≤ n` using `Nat.cast_nonneg n`. Establish `e1` using `hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x`. Establish `e2` using `hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)`.

Rewrite `e1` using `[hτim]`. Rewrite `e2` using `[hτ'im]`. Establish `hsplit : Q.eval (x + n) - Q.eval x = (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n)`. Simplify using `only [eval_sub, htrans τ x]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hsplit]`. Use `(norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))` and prove the remaining obligations. Simplify using `only [M]`. Expand and normalize the polynomial expressions, which then agree. Establish `hlim` using `(tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)`.

Rewrite `hlim` using `[mul_zero]`. Establish `hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0` using `ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)`. Conclude with `sub_eq_zero.1 (norm_le_zero_iff.1 hle)`.
-/
theorem _root_.GlobalTheory.HeckeFamilyMatrices.QConst.qconst : ∀ (w n : ℕ) (V : ℍ → ℂ[X]) (Q : ℂ[X]) (C' c : ℝ), 0 < n → 0 < c → Q ∈ degreeLT ℂ (w + 1) →
    (∀ τ, V τ ∈ degreeLT ℂ (w + 1)) →
    (∀ τ : ℍ, _root_.GlobalTheory.HeckeFamilyMatrices.slP w (_root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ))) (V (ModularGroup.T ^ (n : ℤ) • τ)) = V τ) →
    (∀ τ : ℍ, 1 ≤ τ.im → ∀ j ≤ w, ‖(V τ - Q).coeff j‖ ≤ C' * Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w) →
    Q = C (Q.coeff 0) := by
  intro w n V Q C' c hn hc hQ hV hper h
  have hT : _root_.GlobalTheory.HeckeFamilyMatrices.mat (ModularGroup.T ^ (n : ℤ)) = !![1, (n : ℤ); 0, 1] := by
    unfold _root_.GlobalTheory.HeckeFamilyMatrices.mat
    exact ModularGroup.coe_T_zpow _
  have htrans : ∀ (τ : ℍ) (x : ℂ),
      (V τ).eval x = (V (ModularGroup.T ^ (n : ℤ) • τ)).eval (x + n) := by
    intro τ x
    rw [← hper τ, _root_.GlobalTheory.HeckeFamilyMatrices.eval_polySlash w _ _ x (hV _) (by rw [hT]; simp), hT]
    simp
  have hbound : ∀ τ : ℍ, 1 ≤ τ.im → ∀ b : ℝ, 1 + ‖(τ : ℂ)‖ ≤ b → ∀ x : ℂ,
      ‖(V τ - Q).eval x‖ ≤ C' * Real.exp (-c * τ.im) * b ^ w *
        ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j := by
    intro τ hτ b hb x
    have hC' : 0 ≤ C' := by
      have h0 := h τ hτ 0 (Nat.zero_le _)
      have : 0 < Real.exp (-c * τ.im) * (1 + ‖(τ : ℂ)‖) ^ w := by positivity
      nlinarith [norm_nonneg ((V τ - Q).coeff 0)]
    rw [Finset.mul_sum]
    refine (norm_eval_le_sum_of_mem_degreeLT (Submodule.sub_mem _ (hV τ) hQ) x).trans
      (Finset.sum_le_sum fun j hj => ?_)
    have hj' : j ≤ w := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    exact mul_le_mul_of_nonneg_right ((h τ hτ j hj').trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hb w)
        (mul_nonneg hC' (Real.exp_pos _).le))) (by positivity)
  refine eq_C_of_eval_add_natCast_eq hn fun x => ?_
  set M : ℝ := ∑ j ∈ Finset.range (w + 1), ‖x + n‖ ^ j + ∑ j ∈ Finset.range (w + 1), ‖x‖ ^ j
  have hest : ∀ y : ℝ, 1 ≤ y → ‖Q.eval (x + n) - Q.eval x‖ ≤
      C' * M * (Real.exp (-c * y) * ((1 + n) + y) ^ w) := by
    intro y hy
    let τ : ℍ := ⟨(y : ℂ) * Complex.I, by simp; linarith⟩
    have hτim : τ.im = y := by simp [τ, UpperHalfPlane.im]
    have hτn : ‖(τ : ℂ)‖ = y := by
      simp [τ, abs_of_pos (show (0 : ℝ) < y by linarith)]
    have hτ'c : ((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ) = τ + n := by
      rw [ModularGroup.coe_T_zpow_smul_eq]
      simp
    have hτ'im : (ModularGroup.T ^ (n : ℤ) • τ).im = y := by
      rw [← hτim, ← UpperHalfPlane.coe_im, hτ'c, ← UpperHalfPlane.coe_im]
      simp
    have hτ'n : 1 + ‖((ModularGroup.T ^ (n : ℤ) • τ : ℍ) : ℂ)‖ ≤ (1 + n) + y := by
      rw [hτ'c]
      have := norm_add_le (τ : ℂ) (n : ℂ)
      rw [hτn, Complex.norm_natCast] at this
      linarith
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have e1 := hbound τ (by rw [hτim]; exact hy) ((1 + n) + y) (by rw [hτn]; linarith) x
    have e2 := hbound _ (by rw [hτ'im]; exact hy) ((1 + n) + y) hτ'n (x + n)
    rw [hτim] at e1
    rw [hτ'im] at e2
    have hsplit : Q.eval (x + n) - Q.eval x =
        (V τ - Q).eval x - (V (ModularGroup.T ^ (n : ℤ) • τ) - Q).eval (x + n) := by
      simp only [eval_sub, htrans τ x]
      ring
    rw [hsplit]
    refine (norm_sub_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    simp only [M]
    ring
  have hlim := (tendsto_exp_neg_mul_mul_add_pow_zero hc (1 + n) w).const_mul (C' * M)
  rw [mul_zero] at hlim
  have hle : ‖Q.eval (x + n) - Q.eval x‖ ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, hest⟩)
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hle)

end GlobalTheory.HeckeFamilyMatrices.QConst
