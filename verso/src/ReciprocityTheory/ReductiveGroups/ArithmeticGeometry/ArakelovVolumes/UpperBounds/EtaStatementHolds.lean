import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff

/- English proof (translation)
Distinguish the cases in `hd : DifferentiableAt ℝ g y`. Rewrite using `[fderiv_const_mul hd]`. Simplify using the standard rewrite rules. Distinguish the cases in `ht : t = 0`. Substitute `ht` using the available equality.

Simplify using the standard rewrite rules. Establish `ht' : (t : ℂ) ≠ 0` using `by exact_mod_cast ht`. Establish `hd' : ¬ DifferentiableAt ℝ (fun w => (t : ℂ) * g w) y`. Introduce `h'`. Apply `hd` to reduce the goal to its premises.

Establish `h''` using `h'.const_mul ((t : ℂ)⁻¹)`. Simplify `h''` using `[← mul_assoc, inv_mul_cancel₀ ht']`. Rewrite using `[fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]`. Simplify using the standard rewrite rules.
-/
private lemma fderiv_const_mul_apply {n : ℕ} (t : ℝ) (g : V n → ℂ) (y : V n) (v : V n) :
    fderiv ℝ (fun w => (t : ℂ) * g w) y v = (t : ℂ) * fderiv ℝ g y v := by
  by_cases hd : DifferentiableAt ℝ g y
  · rw [fderiv_const_mul hd]
    simp
  · by_cases ht : t = 0
    · subst ht
      simp
    · have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
      have hd' : ¬ DifferentiableAt ℝ (fun w => (t : ℂ) * g w) y := by
        intro h'
        apply hd
        have h'' := h'.const_mul ((t : ℂ)⁻¹)
        simpa [← mul_assoc, inv_mul_cancel₀ ht'] using h''
      rw [fderiv_zero_of_not_differentiableAt hd', fderiv_zero_of_not_differentiableAt hd]
      simp

/- English proof (translation)
Unfold `wd`. Rewrite using `[fderiv_const_mul_apply, fderiv_const_mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma wd_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) (y : V n) :
    wd n j (fun w => (t : ℂ) * g w) y = (t : ℂ) * wd n j g y := by
  unfold wd
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

/- English proof (translation)
Use function extensionality and compare the values at `y`. Unfold `wdb`. Rewrite using `[fderiv_const_mul_apply, fderiv_const_mul_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
private lemma wdb_const_mul (n : ℕ) (j : Fin n) (t : ℝ) (g : V n → ℂ) :
    wdb n j (fun w => (t : ℂ) * g w) = fun y => (t : ℂ) * wdb n j g y := by
  funext y
  unfold wdb
  rw [fderiv_const_mul_apply, fderiv_const_mul_apply]
  ring

/- English proof (translation)
Unfold `leviM leviV`. Establish `h1 : (fun w => (((t * g (cpt X x0 w) : ℝ)) : ℂ)) = fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ)`. Use function extensionality and compare the values at `w`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [h1, wdb_const_mul, wd_const_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]`.
-/
private lemma leviM_const_mul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (g : Frame X.Ψ r → ℝ) (t : ℝ) (x0 : Frame X.Ψ r) (z : V (nd X)) (ξ : Fin (nd X) → ℂ) :
    leviM X (fun x => t * g x) x0 z ξ = t * leviM X g x0 z ξ := by
  unfold leviM leviV
  have h1 : (fun w => (((t * g (cpt X x0 w) : ℝ)) : ℂ)) =
      fun w => (t : ℂ) * ((g (cpt X x0 w) : ℝ) : ℂ) := by
    funext w
    push_cast
    ring
  simp only [h1, wdb_const_mul, wd_const_mul, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

/- English proof (translation)
Introduce `r X Xa`. Take `⟨η, hη, h⟩` from `Xa.posF`. Use `⟨η, hη, fun x0 ho z hz ξ => ?_⟩` and prove the remaining obligations. Establish `hx0 : x0 ∈ X.dom` using `IW.orth_mem_dom (X := X) (x0 := x0) (ho := ho)`. Establish `hzd : cpt X x0 z ∈ X.dom` using `hz`.

Establish `hc1` using `Xa.frame_theta_const_pos`. Establish `ha1` using `Xa.frame_theta_weight_pos`. Establish `ht0 : (0 : ℝ) ≤ 1 + Xa.c1 / Xa.a1` using `by positivity`. Establish `htr : (1 + Xa.c1 / Xa.a1) * Xa.rr ≤ 2 * (Xa.T : ℝ)`. Rewrite using `[mul_comm]`.

Conclude with `Xa.rr_le`. Establish `h1` using `h (1 + Xa.c1 / Xa.a1) ht0 htr x0 hx0 z hzd ξ`. Establish `h2` using `Xa.base_psi_levi_lower_bound x0 hx0 z hzd ξ`. Establish `h3` using `IW.leviM_comb (X := X) (x0 := x0) (ho := ho) (hz := hz) (la1 := Xa.Fp) (la2 := Xa.L) (k := nd X) (ξ := ξ)`. Establish `h4` using `leviM_const_mul X Xa.ps0 (1 + Xa.c1 / Xa.a1) x0 z ξ`.

Establish `h5` using `mul_le_mul_of_nonneg_left h2 ht0`. Rewrite `h1` using `[h3]`. Unfold `leviO at h1 ⊢`. Rewrite using `[h4]`. Use polynomial arithmetic with `[h1, h5]`.
-/
theorem eta_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) := by
  intro r X Xa
  obtain ⟨η, hη, h⟩ := Xa.posF
  refine ⟨η, hη, fun x0 ho z hz ξ => ?_⟩
  have hx0 : x0 ∈ X.dom := IW.orth_mem_dom (X := X) (x0 := x0) (ho := ho)
  have hzd : cpt X x0 z ∈ X.dom := hz
  have hc1 := Xa.frame_theta_const_pos
  have ha1 := Xa.frame_theta_weight_pos
  have ht0 : (0 : ℝ) ≤ 1 + Xa.c1 / Xa.a1 := by positivity
  have htr : (1 + Xa.c1 / Xa.a1) * Xa.rr ≤ 2 * (Xa.T : ℝ) := by
    rw [mul_comm]
    exact Xa.rr_le
  have h1 := h (1 + Xa.c1 / Xa.a1) ht0 htr x0 hx0 z hzd ξ
  have h2 := Xa.base_psi_levi_lower_bound x0 hx0 z hzd ξ
  have h3 := IW.leviM_comb (X := X) (x0 := x0) (ho := ho) (hz := hz) (la1 := Xa.Fp) (la2 := Xa.L)
    (k := nd X) (ξ := ξ)
  have h4 := leviM_const_mul X Xa.ps0 (1 + Xa.c1 / Xa.a1) x0 z ξ
  have h5 := mul_le_mul_of_nonneg_left h2 ht0
  rw [h3] at h1
  unfold leviO at h1 ⊢
  rw [h4]
  nlinarith [h1, h5]

end ReciprocityTheory.ChartRestriction.G.AR.Up.EtaPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

/- English proof (translation)
The claim follows from `EtaPf.eta_holds`.
-/
theorem EtaStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : EtaStatement (E := E) :=
  EtaPf.eta_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
