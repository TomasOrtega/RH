import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousQuad
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionUnipotentInvariant

noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.HolTPf

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

abbrev EE (n : ℕ) := Fin n → Fin n → ℂ

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_re (v : EE n) : (Matrix.of ((1 / 2 : ℂ) • (v + fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.conjTranspose_apply, Matrix.of_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm_im (v : EE n) :
    (Matrix.of ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))).IsHermitian := by
  ext i j
  simp [Matrix.conjTranspose_apply, Matrix.of_apply]
  field_simp
  ring

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem split_re_im (v : EE n) :
    v = (1 / 2 : ℂ) • (v + fun i j => star (v j i)) + Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i))) := by
  funext i j
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  field_simp
  ring

/- English proof (translation)
Use extensionality with `i j`. Establish `h2` using `congrFun (congrFun hk i) j`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2 ⊢`. Simplify using `[h2]`.
-/
private theorem herm_Hpk_smul_left (k : EE n) (hk : (Matrix.of k).IsHermitian) (t : ℝ) :
    (Matrix.of ((t : ℂ) • k)).IsHermitian := by
  ext i j
  have h2 := congrFun (congrFun hk i) j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply] at h2 ⊢
  simp [h2]

/- English proof (translation)
Establish `key : ∀ W ∈ Dom n, fderiv ℂ G W = 0`. Introduce `W hW`. Establish `hGd : HasFDerivAt G (fderiv ℂ G W) W` using `((hG W hW).differentiableAt (isOpen_dom'.mem_nhds hW)).hasFDerivAt`. Establish `hk0 : ∀ k : EE n, (Matrix.of k).IsHermitian → fderiv ℂ G W k = 0`. Introduce `k hk`.

Establish `hc : HasDerivAt (fun t : ℝ => W + (t : ℂ) • k) k 0`. Establish `h1` using `((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const k).const_add W`. Simplify using `using h1`. Establish `hcomp` using `(hGd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)`. Establish `hfun : (G ∘ fun t : ℝ => W + (t : ℂ) • k) = fun _ => G W`.

Use function extensionality and compare the values at `t`. Conclude with `hT W hW _ (herm_Hpk_smul_left k hk t)`. Rewrite `hcomp` using `[hfun]`. Simplify using `using hcomp.unique (hasDerivAt_const _ _)`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← split_re_im v]`. Use `_ = 0 := by`. Rewrite using `[map_add, hk0 _ (herm_re v), map_smul, hk0 _ (herm_im v)]`. Simplify using the standard rewrite rules.

Introduce `W hW W' hW'`. Conclude with `convex_dom'.is_const_of_fderivWithin_eq_zero hG (fun x hx => by rw [fderivWithin_of_isOpen isOpen_dom' hx]; exact key x hx) hW hW'`.
-/
theorem const_of_transl (G : EE n → ℂ) (hG : DifferentiableOn ℂ G (Dom n))
    (hT : ∀ W ∈ Dom n, ∀ k : EE n, (Matrix.of k).IsHermitian → G (W + k) = G W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n, G W = G W' := by
  have key : ∀ W ∈ Dom n, fderiv ℂ G W = 0 := by
    intro W hW
    have hGd : HasFDerivAt G (fderiv ℂ G W) W :=
      ((hG W hW).differentiableAt (isOpen_dom'.mem_nhds hW)).hasFDerivAt
    have hk0 : ∀ k : EE n, (Matrix.of k).IsHermitian → fderiv ℂ G W k = 0 := by
      intro k hk
      have hc : HasDerivAt (fun t : ℝ => W + (t : ℂ) • k) k 0 := by
        have h1 := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.smul_const k).const_add W
        simpa using h1
      have hcomp := (hGd.restrictScalars ℝ).comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
      have hfun : (G ∘ fun t : ℝ => W + (t : ℂ) • k) = fun _ => G W := by
        funext t
        exact hT W hW _ (herm_Hpk_smul_left k hk t)
      rw [hfun] at hcomp
      simpa using hcomp.unique (hasDerivAt_const _ _)
    refine ContinuousLinearMap.ext fun v => ?_
    calc fderiv ℂ G W v = fderiv ℂ G W ((1 / 2 : ℂ) • (v + fun i j => star (v j i)) +
          Complex.I • ((1 / (2 * Complex.I) : ℂ) • (v - fun i j => star (v j i)))) := by
          rw [← split_re_im v]
      _ = 0 := by
          rw [map_add, hk0 _ (herm_re v), map_smul, hk0 _ (herm_im v)]
          simp
  intro W hW W' hW'
  exact convex_dom'.is_const_of_fderivWithin_eq_zero hG
    (fun x hx => by rw [fderivWithin_of_isOpen isOpen_dom' hx]; exact key x hx) hW hW'

/- English proof (translation)
Apply `const_of_transl (fun W => Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W)` to reduce the goal to its premises. Use `DifferentiableOn.mul ?_ hH` and prove the remaining obligations. Apply `Differentiable.differentiableOn` to reduce the goal to its premises. Establish `hl : Differentiable ℂ (fun W : EE n => (β * Matrix.of W).trace)`. Simplify using `only [Matrix.trace, Matrix.mul_apply, Matrix.of_apply, Matrix.diag]`.

Use `fun_prop`. Use `fun_prop`. Introduce `W hW k hk`. Establish `hof : Matrix.of (c • k) = c • Matrix.of k` using `rfl`. Establish `hh : (Matrix.of (c • k)).IsHermitian`.

Rewrite using `[hof, Matrix.IsHermitian, Matrix.conjTranspose_smul, hcs, hk.eq]`. Establish `hWk : W + k = W + c • (c • k)`. Use extensionality with `i j`. Simplify using `[smul_smul, hc]`. Establish `htr : (β * Matrix.of (W + k)).trace = (β * Matrix.of W).trace + (β * Matrix.of k).trace`.

Rewrite using `[← Matrix.of_add_of, Matrix.mul_add, Matrix.trace_add]`. Establish `htr2 : (β * Matrix.of (c • k)).trace = c * (β * Matrix.of k).trace`. Rewrite using `[hof, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]`. Establish `hHk : H (W + k) = Complex.exp (Complex.I * (c * (β * Matrix.of k).trace)) * H W`. Rewrite using `[hWk, hT W hW _ hh, htr2]`.

Apply the tactic sequence `try dsimp only`. Rewrite using `[hHk, htr, ← mul_assoc, ← Complex.exp_add]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exp_trace_mul_H_const_on_dom (H : EE n → ℂ) (hH : DifferentiableOn ℂ H (Dom n))
    (β : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (hc : c * c = 1) (hcs : star c = c)
    (hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W) :
    ∀ W ∈ Dom n, ∀ W' ∈ Dom n,
      Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W =
        Complex.exp (-(c * Complex.I * (β * Matrix.of W').trace)) * H W' := by
  apply const_of_transl (fun W => Complex.exp (-(c * Complex.I * (β * Matrix.of W).trace)) * H W)
  · refine DifferentiableOn.mul ?_ hH
    apply Differentiable.differentiableOn
    have hl : Differentiable ℂ (fun W : EE n => (β * Matrix.of W).trace) := by
      simp only [Matrix.trace, Matrix.mul_apply, Matrix.of_apply, Matrix.diag]
      fun_prop
    fun_prop
  · intro W hW k hk
    have hof : Matrix.of (c • k) = c • Matrix.of k := rfl
    have hh : (Matrix.of (c • k)).IsHermitian := by
      rw [hof, Matrix.IsHermitian, Matrix.conjTranspose_smul, hcs, hk.eq]
    have hWk : W + k = W + c • (c • k) := by
      ext i j
      simp [smul_smul, hc]
    have htr : (β * Matrix.of (W + k)).trace = (β * Matrix.of W).trace + (β * Matrix.of k).trace := by
      rw [← Matrix.of_add_of, Matrix.mul_add, Matrix.trace_add]
    have htr2 : (β * Matrix.of (c • k)).trace = c * (β * Matrix.of k).trace := by
      rw [hof, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
    have hHk : H (W + k) = Complex.exp (Complex.I * (c * (β * Matrix.of k).trace)) * H W := by
      rw [hWk, hT W hW _ hh, htr2]
    try dsimp only
    rw [hHk, htr, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring

/- English proof (translation)
Introduce `n p q e φ hφ β hβ a a' x y hx ha`. Take `⟨H, hH, hφH⟩` from `hφ`. Take `⟨Z, hZ⟩ : ∃ Z : GR n → Matrix (Fin n) (Fin n) ℂ, ∀ y, Z y = if q = 0 then zOf y else -(zOf y)ᴴ` from `⟨_, fun _ => rfl⟩`. Take `⟨c, hc⟩ : ∃ c : ℂ, c = if q = 0 then 1 else -1` from `⟨_, rfl⟩`. Establish `hφ' : ∀ y, φ y = F0 p q e y * H (Z y)` using `fun y => by rw [hZ]; exact hφH y`.

Establish `hdom : ∀ y : GR n, Z y ∈ Dom n`. Introduce `y`. Rewrite using `[hZ]`. Use `split_ifs`. Conclude with `zOf_mem' y`.

Conclude with `neg_conj_mem' (zOf_mem' y)`. Establish `hsurj : ∀ W ∈ Dom n, ∃ y : GR n, Z y = W`. Introduce `W hW`. Simplify using `only [hZ]`. Use `split_ifs`.

Conclude with `zOf_surj' hW`. Take `⟨y, hy⟩` from `zOf_surj' (neg_conj_mem' hW)`. Use `⟨y, ?_⟩` and prove the remaining obligations. Rewrite using `[hy]`. Simplify using `only [Matrix.conjTranspose_neg, neg_neg, Matrix.conjTranspose_conjTranspose]`.

Both sides reduce to the same expression. Establish `hnU : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h → Z (x * y) = Z y + c • h`. Introduce `h x y hh hx`. Rewrite using `[hZ, hZ, hc, zOf_nU' h x y hx]`. Use `split_ifs`.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.conjTranspose_add, hh.eq]`. Simplify using the standard rewrite rules. Normalize the expressions using the abelian group laws. Establish `hlevi : ∀ y : GR n, Z (x * y) = a * Z y * aᴴ`.

Introduce `y`. Rewrite using `[hZ, hZ, zOf_levi' a a' x y hx]`. Use `split_ifs`. Both sides reduce to the same expression. Simplify using `[Matrix.conjTranspose_mul, Matrix.mul_assoc]`.

Establish `hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian → H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W`. Introduce `W hW h hh`. Take `⟨y0, hy0⟩` from `hsurj W hW`. Take `⟨x0, hx0⟩` from `nU_mem' hh`. Establish `h1` using `hβ _ x0 y0 hh hx0`.

Rewrite `h1` using `[hφ', hφ', spherical_section_unipotent_invariant p q e _ x0 y0 hx0, hnU _ x0 y0 hh hx0]`. Establish `e0 : (W + c • h : EE n) = Z y0 + c • Matrix.of h`. Rewrite using `[hy0]`. Both sides reduce to the same expression. Rewrite using `[e0]`.

Apply `mul_left_cancel₀ (spherical_section_ne_zero_group p q e y0)` to reduce the goal to its premises. Rewrite using `[h1, hy0]`. Expand and normalize the polynomial expressions, which then agree. Establish `hc2 : c * c = 1`. Rewrite using `[hc]`.

Apply the tactic sequence `split_ifs <;> norm_num`. Establish `hcs : star c = c`. Rewrite using `[hc]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hconst` using `exp_trace_mul_H_const_on_dom H hH β c hc2 hcs hT`.

Establish `htr : (β * (a * Z y * aᴴ)).trace = (β * Z y).trace`. Rewrite using `[show β * (a * Z y * aᴴ) = (β * a * Z y) * aᴴ by simp [Matrix.mul_assoc], Matrix.trace_mul_comm, show aᴴ * (β * a * Z y) = (aᴴ * β * a) * Z y by simp [Matrix.mul_assoc], ha]`. Establish `hHeq : H (a * Z y * aᴴ) = H (Z y)`. Establish `h1` using `hconst _ (hlevi y ▸ hdom (x * y)) _ (hdom y)`. Establish `htr' : (β * Matrix.of (a * Z y * aᴴ)).trace = (β * Matrix.of (Z y)).trace` using `htr`.

Rewrite `h1` using `[htr']`. Conclude with `mul_left_cancel₀ (Complex.exp_ne_zero _) h1`. Rewrite using `[hφ' (x * y), hφ' y, spherical_section_levi_mul p q e a a' x y hx, hlevi y, hHeq]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem holomorphic_translation_levi : ∀ (n p q : ℕ) (e : ℤ) (φ : GR n → ℂ), IsHolW p q e φ → ∀ β : Matrix (Fin n) (Fin n) ℂ,
    (∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      φ (x * y) = Complex.exp (Complex.I * (β * h).trace) * φ y) →
    ∀ (a a' : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), mR x = Matrix.fromBlocks a 0 0 a' → aᴴ * β * a = β →
      φ (x * y) = F0 p q e x * φ y := by
  intro n p q e φ hφ β hβ a a' x y hx ha
  obtain ⟨H, hH, hφH⟩ := hφ
  obtain ⟨Z, hZ⟩ : ∃ Z : GR n → Matrix (Fin n) (Fin n) ℂ,
      ∀ y, Z y = if q = 0 then zOf y else -(zOf y)ᴴ := ⟨_, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = if q = 0 then 1 else -1 := ⟨_, rfl⟩
  have hφ' : ∀ y, φ y = F0 p q e y * H (Z y) := fun y => by rw [hZ]; exact hφH y
  have hdom : ∀ y : GR n, Z y ∈ Dom n := by
    intro y
    rw [hZ]
    split_ifs
    · exact zOf_mem' y
    · exact neg_conj_mem' (zOf_mem' y)
  have hsurj : ∀ W ∈ Dom n, ∃ y : GR n, Z y = W := by
    intro W hW
    simp only [hZ]
    split_ifs
    · exact zOf_surj' hW
    · obtain ⟨y, hy⟩ := zOf_surj' (neg_conj_mem' hW)
      refine ⟨y, ?_⟩
      rw [hy]
      simp only [Matrix.conjTranspose_neg, neg_neg, Matrix.conjTranspose_conjTranspose]
      rfl
  have hnU : ∀ (h : Matrix (Fin n) (Fin n) ℂ) (x y : GR n), h.IsHermitian → mR x = nU h →
      Z (x * y) = Z y + c • h := by
    intro h x y hh hx
    rw [hZ, hZ, hc, zOf_nU' h x y hx]
    split_ifs
    · simp
    · rw [Matrix.conjTranspose_add, hh.eq]
      simp
      abel
  have hlevi : ∀ y : GR n, Z (x * y) = a * Z y * aᴴ := by
    intro y
    rw [hZ, hZ, zOf_levi' a a' x y hx]
    split_ifs
    · rfl
    · simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hT : ∀ W ∈ Dom n, ∀ h : EE n, (Matrix.of h).IsHermitian →
      H (W + c • h) = Complex.exp (Complex.I * (β * Matrix.of h).trace) * H W := by
    intro W hW h hh
    obtain ⟨y0, hy0⟩ := hsurj W hW
    obtain ⟨x0, hx0⟩ := nU_mem' hh
    have h1 := hβ _ x0 y0 hh hx0
    rw [hφ', hφ', spherical_section_unipotent_invariant p q e _ x0 y0 hx0, hnU _ x0 y0 hh hx0] at h1
    have e0 : (W + c • h : EE n) = Z y0 + c • Matrix.of h := by
      rw [hy0]
      rfl
    rw [e0]
    apply mul_left_cancel₀ (spherical_section_ne_zero_group p q e y0)
    rw [h1, hy0]
    ring
  have hc2 : c * c = 1 := by
    rw [hc]
    split_ifs <;> norm_num
  have hcs : star c = c := by
    rw [hc]
    split_ifs <;> simp
  have hconst := exp_trace_mul_H_const_on_dom H hH β c hc2 hcs hT
  have htr : (β * (a * Z y * aᴴ)).trace = (β * Z y).trace := by
    rw [show β * (a * Z y * aᴴ) = (β * a * Z y) * aᴴ by simp [Matrix.mul_assoc],
      Matrix.trace_mul_comm,
      show aᴴ * (β * a * Z y) = (aᴴ * β * a) * Z y by simp [Matrix.mul_assoc], ha]
  have hHeq : H (a * Z y * aᴴ) = H (Z y) := by
    have h1 := hconst _ (hlevi y ▸ hdom (x * y)) _ (hdom y)
    have htr' : (β * Matrix.of (a * Z y * aᴴ)).trace = (β * Matrix.of (Z y)).trace := htr
    rw [htr'] at h1
    exact mul_left_cancel₀ (Complex.exp_ne_zero _) h1
  rw [hφ' (x * y), hφ' y, spherical_section_levi_mul p q e a a' x y hx, hlevi y, hHeq]
  ring

end PositivityTheory.Rg.Sw.HSt.HolTPf
