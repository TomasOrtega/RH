import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.MdiscSt
import ReciprocityTheory.AnalyticForms.AnalyticCharts.MaDensCompEqZeroOfRankLt

namespace ReciprocityTheory.AnForm.M

open Filter Topology
open scoped ContDiff ComplexOrder

noncomputable section

section SlopeTestRemainingChoices

variable {D : ℕ}

/- English proof (translation)
Establish `h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ` using `by show fderiv ℝ (c • φ) = _`. Conclude with `fderiv_const_smul_field c`. Establish `h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ)`. Rewrite using `[h1]`. Conclude with `fderiv_const_smul_field c`.

Use extensionality with `i j`. Simplify using `only [hessC, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Matrix.smul_apply]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_const_mul' (c : ℝ) (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) :
    hessC (fun w => c * φ w) z = (c : ℂ) • hessC φ z := by
  have h1 : fderiv ℝ (fun w => c * φ w) = c • fderiv ℝ φ := by
    show fderiv ℝ (c • φ) = _
    exact fderiv_const_smul_field c
  have h2 : fderiv ℝ (fderiv ℝ (fun w => c * φ w)) = c • fderiv ℝ (fderiv ℝ φ) := by
    rw [h1]; exact fderiv_const_smul_field c
  ext i j
  simp only [hessC, h2, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Matrix.smul_apply]
  push_cast
  ring

/- English proof (translation)
Establish `e1 : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w` using `by filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w h1 h2`. Conclude with `fderiv_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))`. Establish `d1 : DifferentiableAt ℝ (fderiv ℝ φ) z` using `(hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero`. Establish `d2 : DifferentiableAt ℝ (fderiv ℝ ψ) z` using `(hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero`. Establish `e2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z = fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z`.

Rewrite using `[e1.fderiv_eq]`. Conclude with `fderiv_add d1 d2`. Use extensionality with `i j`. Simplify using `only [hessC, e2, ContinuousLinearMap.add_apply, Matrix.add_apply]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem hessC_add' (φ ψ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (hψ : ContDiffAt ℝ 2 ψ z) :
    hessC (fun w => φ w + ψ w) z = hessC φ z + hessC ψ z := by
  have e1 : fderiv ℝ (fun w => φ w + ψ w) =ᶠ[𝓝 z] fun w => fderiv ℝ φ w + fderiv ℝ ψ w := by
    filter_upwards [hφ.eventually (by simp), hψ.eventually (by simp)] with w h1 h2
    exact fderiv_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num))
  have d1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have d2 : DifferentiableAt ℝ (fderiv ℝ ψ) z :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have e2 : fderiv ℝ (fderiv ℝ (fun w => φ w + ψ w)) z =
      fderiv ℝ (fderiv ℝ φ) z + fderiv ℝ (fderiv ℝ ψ) z := by
    rw [e1.fderiv_eq]; exact fderiv_add d1 d2
  ext i j
  simp only [hessC, e2, ContinuousLinearMap.add_apply, Matrix.add_apply]
  push_cast
  ring

/- English proof (translation)
Unfold `mdisc`. Use `congr 1`. Conclude with `Fintype.sum_equiv σ.finsetCongr _ _ fun S => by`. Simplify using `[Equiv.finsetCongr_apply, Finset.sum_map, Finset.card_map]`.
-/
theorem mdisc_comp_perm' (M : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mdisc (M ∘ σ) = mdisc M := by
  unfold mdisc
  congr 1
  exact Fintype.sum_equiv σ.finsetCongr _ _ fun S => by
    simp [Equiv.finsetCongr_apply, Finset.sum_map, Finset.card_map]

/- English proof (translation)
Use `ReciprocityTheory.AnForm.A.mdisc_update_add (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 B C` as an intermediate fact. Simplify `this` using `only [Fin.update_cons_zero]`.
-/
theorem mdisc_cons_add {e : ℕ} (B C : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (B + C) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) +
        mdisc (Fin.cons C F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_add
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 B C
  simpa only [Fin.update_cons_zero] using this

/- English proof (translation)
Use `ReciprocityTheory.AnForm.A.mdisc_update_smul (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 c B` as an intermediate fact. Simplify `this` using `only [Fin.update_cons_zero]`.
-/
theorem mdisc_cons_smul {e : ℕ} (c : ℂ) (B : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ)
    (F : Fin e → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) :
    mdisc (Fin.cons (c • B) F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) =
      c * mdisc (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) := by
  have := ReciprocityTheory.AnForm.A.mdisc_update_smul
    (Fin.cons B F : Fin (e + 1) → Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) 0 c B
  simpa only [Fin.update_cons_zero] using this

/- English proof (translation)
Establish `hs` using `hφ.isSymmSndFDerivAt (by simp)`. Use extensionality with `i j`. Simplify using `only [Matrix.conjTranspose_apply, hessC]`. Rewrite using `[hs (Pi.single j 1) (Pi.single i 1), hs (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1), hs (Pi.single j 1) (Complex.I • Pi.single i 1), hs (Complex.I • Pi.single j 1) (Pi.single i 1)]`. Apply the tactic sequence `apply Complex.ext <;> simp`.
-/
theorem hessC_isHermitian' (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z) :
    (hessC φ z).IsHermitian := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  ext i j
  simp only [Matrix.conjTranspose_apply, hessC]
  rw [hs (Pi.single j 1) (Pi.single i 1), hs (Complex.I • Pi.single j 1) (Complex.I • Pi.single i 1),
    hs (Pi.single j 1) (Complex.I • Pi.single i 1), hs (Complex.I • Pi.single j 1) (Pi.single i 1)]
  apply Complex.ext <;> simp

/- English proof (translation)
Simplify using `only [leviC, smul_add, map_add]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem leviC_add_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a b b' : Fin D → ℂ) :
    leviC H a (b + b') = leviC H a b + leviC H a b' := by
  simp only [leviC, smul_add, map_add]
  push_cast
  ring

/- English proof (translation)
Establish `h1 : c • b = c.re • b + c.im • (Complex.I • b)`. Use extensionality with `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]`. Use `conv_lhs => rw [← Complex.re_add_im c]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b`. Use extensionality with `k`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]`. Use `conv_lhs => rw [← Complex.re_add_im c]`. Take the linear combination `((c.im : ℂ) * b k) * Complex.I_sq`.

Unfold `leviC`. Rewrite using `[h2, h1]`. Simplify using `only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Apply the tactic sequence `apply Complex.ext <;> simp <;> ring`.
-/
theorem leviC_smul_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (c : ℂ) (a b : Fin D → ℂ) :
    leviC H a (c • b) = starRingEnd ℂ c * leviC H a b := by
  have h1 : c • b = c.re • b + c.im • (Complex.I • b) := by
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    ring
  have h2 : Complex.I • (c • b) = c.re • (Complex.I • b) - c.im • b := by
    ext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im c]
    linear_combination ((c.im : ℂ) * b k) * Complex.I_sq
  unfold leviC
  rw [h2, h1]
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  apply Complex.ext <;> simp <;> ring

/- English proof (translation)
Set `ℓ : (Fin D → ℂ) →+ ℂ` to `{ toFun := leviC H a map_zero' := by simp [leviC] map_add' := leviC_add_right H a }`. Establish `hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin D → ℂ)` using `by conv_lhs => rw [← Finset.univ_sum_single (star x)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use extensionality with `k`. Distinguish the cases in `h : k = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[h]`. Use `map_sum ℓ (fun j => star (x j) • (Pi.single j 1 : Fin D → ℂ)) Finset.univ` as an intermediate fact. Rewrite `this` using `[← hx]`.

Express the relevant statement in the definitionally equal form `leviC H a (star x) = ∑ j, leviC H a (star (x j) • Pi.single j 1) at this`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[leviC_smul_right]`. Simplify using `[mul_comm]`.
-/
theorem sum_leviC_right (H : (Fin D → ℂ) →L[ℝ] (Fin D → ℂ) →L[ℝ] ℝ) (a x : Fin D → ℂ) :
    ∑ j, leviC H a (Pi.single j 1) * x j = leviC H a (star x) := by
  let ℓ : (Fin D → ℂ) →+ ℂ :=
    { toFun := leviC H a
      map_zero' := by simp [leviC]
      map_add' := leviC_add_right H a }
  have hx : star x = ∑ j, star (x j) • (Pi.single j 1 : Fin D → ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single (star x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    ext k
    by_cases h : k = j
    · subst h; simp
    · simp [h]
  have := map_sum ℓ (fun j => star (x j) • (Pi.single j 1 : Fin D → ℂ)) Finset.univ
  rw [← hx] at this
  change leviC H a (star x) = ∑ j, leviC H a (star (x j) • Pi.single j 1) at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviC_smul_right]
  simp [mul_comm]

/- English proof (translation)
Establish `hs` using `hφ.isSymmSndFDerivAt (by simp)`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian' φ z hφ) fun x => ?_` and prove the remaining obligations. Establish `hq : star x ⬝ᵥ ((hessC φ z).mulVec x) = leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x)`. Rewrite using `[Matrix.dotProduct_mulVec]`. Simplify using `only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]`.

Conclude with `sum_leviC_right _ _ _`. Rewrite using `[hq, Complex.nonneg_iff]`. Prove the components needed by the constructor for the conclusion. Use `h (star x)` as an intermediate fact. Simplify using `only [levi] at this`.

Simplify `this` using `[leviC]`. Simplify using `[leviC, hs (star x) (Complex.I • star x)]`.
-/
theorem hessC_posSemidef (φ : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hφ : ContDiffAt ℝ 2 φ z)
    (h : ∀ w, 0 ≤ levi φ z w) : (hessC φ z).PosSemidef := by
  have hs := hφ.isSymmSndFDerivAt (by simp)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hessC_isHermitian' φ z hφ) fun x => ?_
  have hq : star x ⬝ᵥ ((hessC φ z).mulVec x) =
      leviC (fderiv ℝ (fderiv ℝ φ) z) (star x) (star x) := by
    rw [Matrix.dotProduct_mulVec]
    simp only [Matrix.vecMul, dotProduct, hessC_eq_leviC, sum_mul_leviC]
    exact sum_leviC_right _ _ _
  rw [hq, Complex.nonneg_iff]
  constructor
  · have := h (star x)
    simp only [levi] at this
    simpa [leviC] using this
  · simp [leviC, hs (star x) (Complex.I • star x)]

end SlopeTestRemainingChoices

end

end ReciprocityTheory.AnForm.M
