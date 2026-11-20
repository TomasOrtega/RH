import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
open MvPolynomial
open scoped ContDiff
open GlobalTheory.PsCo.Pc1

noncomputable section

namespace GlobalTheory.PsCo.Pc1.B

/- English proof (translation)
Take `⟨hc, R, hR⟩` from `hH`. Use `⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h : H =ᶠ[nhds x] fun _ => (0 : ℝ)` using `by filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy`. Conclude with `hR y (le_of_lt hy)`. Rewrite using `[h.deriv_eq]`.

Simplify using the standard rewrite rules.
-/
theorem sb_derivcut (H : ℝ → ℝ) (hH : IsCutFn H) : IsCutFn (deriv H) := by
  obtain ⟨hc, R, hR⟩ := hH
  refine ⟨(contDiff_infty_iff_deriv.1 hc).2, R + 1, fun x hx => ?_⟩
  have h : H =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds (show R < x by linarith)] with y hy
    exact hR y (le_of_lt hy)
  rw [h.deriv_eq]
  simp

/- English proof (translation)
Simplify using `only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]`. Use `push_cast`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sb_evrp {n : ℕ} (ε : Fin n → Bool) (g : Mat n) : ev g (rP ε) = ((rM ε g : ℝ) : ℂ) := by
  simp only [rP, rM, map_sum, map_mul, ev, eval_X, Sum.elim_inl, Sum.elim_inr]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/- English proof (translation)
Use `induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a` and prove the remaining obligations. Introduce `a`. Establish `: dZ ε Z (C a) = 0`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `(dZ ε Z).map_algebraMap a`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Introduce `p v ih`. Distinguish the cases in `hp : p = 0`. Simplify using `[hp]`.

Rewrite using `[Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]`. Use `(totalDegree_add _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans (add_le_add le_rfl ?_)` and prove the remaining obligations. Simplify using `only [dZ, mkDerivation_X]`. Consider the cases of `v with`.

Consider the case `inl x`. Simplify using `only [Sum.elim_inl]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)` and prove the remaining obligations. Use `(totalDegree_sub _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `(totalDegree_mul _ _).trans (by simp)`.

Conclude with `(totalDegree_mul _ _).trans (by simp)`. Consider the case `inr x`. Simplify using `only [Sum.elim_inr]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)` and prove the remaining obligations. Use `(totalDegree_sub _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Conclude with `(totalDegree_mul _ _).trans (by simp)`. Conclude with `(totalDegree_mul _ _).trans (by simp)`. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Rewrite using `[totalDegree_X]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sb_degmono {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (s : _) (a : ℂ) :
    (dZ ε Z (monomial s a)).totalDegree ≤ (monomial s a).totalDegree := by
  refine induction_on_monomial (motive := fun p => (dZ ε Z p).totalDegree ≤ p.totalDegree) ?_ ?_ s a
  · intro a
    have : dZ ε Z (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact (dZ ε Z).map_algebraMap a
    rw [this]; simp
  · intro p v ih
    by_cases hp : p = 0
    · simp [hp]
    rw [Derivation.leibniz, totalDegree_mul_of_isDomain hp (X_ne_zero v), totalDegree_X, smul_eq_mul, smul_eq_mul]
    refine (totalDegree_add _ _).trans (max_le ?_ ?_)
    · refine (totalDegree_mul _ _).trans (add_le_add le_rfl ?_)
      simp only [dZ, mkDerivation_X]
      cases v with
      | inl x =>
        simp only [Sum.elim_inl]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
      | inr x =>
        simp only [Sum.elim_inr]
        refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
        refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
        · exact (totalDegree_mul _ _).trans (by simp)
        · exact (totalDegree_mul _ _).trans (by simp)
    · refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_X]
      omega

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Rewrite using `[map_sum]`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)` and prove the remaining obligations. Use `(sb_degmono ε Z m _).trans ?_` and prove the remaining obligations. Conclude with `(totalDegree_monomial_le _ _).trans (le_totalDegree hm)`.
-/
theorem sb_degdz {n : ℕ} (ε : Fin n → Bool) (Z : Mat n) (P : Poly n) :
    (dZ ε Z P).totalDegree ≤ P.totalDegree := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine (sb_degmono ε Z m _).trans ?_
  exact (totalDegree_monomial_le _ _).trans (le_totalDegree hm)

/- English proof (translation)
Unfold `rP`. Use `(totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)` and prove the remaining obligations. Use `(totalDegree_mul _ _).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem sb_degrp {n : ℕ} (ε : Fin n → Bool) : (rP ε : Poly n).totalDegree ≤ 2 := by
  unfold rP
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun c _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  simp

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Establish `: D (C a) = 0`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `D.map_algebraMap a`.

Simplify using `only [this, eval_C, map_zero]`. Conclude with `hasDerivAt_const _ _`. Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p v hp`. Establish `h` using `hp.fun_mul (hγ v)`. Simplify using `only [map_mul, eval_X]`. Use `h.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sb_evderiv {σ : Type} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (γ : ℝ → σ → ℂ) (s : ℝ)
    (hγ : ∀ v, HasDerivAt (fun u => γ u v) (MvPolynomial.eval (γ s) (D (MvPolynomial.X v))) s) (P : MvPolynomial σ ℂ) :
    HasDerivAt (fun u => MvPolynomial.eval (γ u) P) (MvPolynomial.eval (γ s) (D P)) s := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have : D (C a) = 0 := by
      rw [← MvPolynomial.algebraMap_eq]; exact D.map_algebraMap a
    simp only [this, eval_C, map_zero]
    exact hasDerivAt_const _ _
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    have h := hp.fun_mul (hγ v)
    simp only [map_mul, eval_X]
    refine h.congr_deriv ?_
    rw [Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul, eval_X]
    ring

/- English proof (translation)
Set `: NormedRing (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedRing`. Set `: NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Set `: NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ)` to `Matrix.linftyOpNormedAlgebra`. Establish `h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s` using `hasDerivAt_exp_smul_const _ _`. Establish `h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s` using `hasDerivAt_exp_smul_const _ _`.

Establish `h3` using `(h1.mul_const g).mul h2`. Establish `hc : Commute Z (NormedSpace.exp (s • Z))` using `((Commute.refl Z).smul_right s).exp_right`. Establish `hc' : Commute (-Z) (NormedSpace.exp (s • (-Z)))` using `((Commute.refl (-Z)).smul_right s).exp_right`. Set `L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ` to `(Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap`. Establish `h4` using `L.hasFDerivAt.comp_hasDerivAt s h3`.

Simplify using `only [Function.comp_def] at h4`. Establish `e : ∀ u : ℝ, (u : ℂ) • Z = u • Z` using `fun u => by simp`. Simplify using `only [e, smul_neg] at *`. Use `HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_` and prove the remaining obligations. Use `show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) + NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _`.

Establish `hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) + NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) = NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z - Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z))`. Rewrite using `[← hc'.eq]`. Use `noncomm_ring`. Rewrite using `[hm]`.
-/
theorem sb_curve {n : ℕ} (Z g : Matrix (Fin n) (Fin n) ℂ) (s : ℝ) (a b : Fin n) :
    HasDerivAt (fun u : ℝ => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) a b)
      (((NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) * Z -
        Z * (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) a b) s := by
  let : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  let : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have h1 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • (-Z))) (NormedSpace.exp (s • (-Z)) * (-Z)) s :=
    hasDerivAt_exp_smul_const _ _
  have h2 : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • Z)) (NormedSpace.exp (s • Z) * Z) s :=
    hasDerivAt_exp_smul_const _ _
  have h3 := (h1.mul_const g).mul h2
  have hc : Commute Z (NormedSpace.exp (s • Z)) := ((Commute.refl Z).smul_right s).exp_right
  have hc' : Commute (-Z) (NormedSpace.exp (s • (-Z))) := ((Commute.refl (-Z)).smul_right s).exp_right
  let L : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℂ := (Matrix.entryLinearMap ℝ ℂ a b).toContinuousLinearMap
  have h4 := L.hasFDerivAt.comp_hasDerivAt s h3
  simp only [Function.comp_def] at h4
  have e : ∀ u : ℝ, (u : ℂ) • Z = u • Z := fun u => by simp
  simp only [e, smul_neg] at *
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => (NormedSpace.exp (-(u • Z)) * g * NormedSpace.exp (u • Z)) a b) h4 ?_
  show (NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z)) a b = _
  have hm : NormedSpace.exp (-(s • Z)) * -Z * g * NormedSpace.exp (s • Z) +
        NormedSpace.exp (-(s • Z)) * g * (NormedSpace.exp (s • Z) * Z) =
      NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z) * Z -
        Z * (NormedSpace.exp (-(s • Z)) * g * NormedSpace.exp (s • Z)) := by
    rw [← hc'.eq]; noncomm_ring
  rw [hm]

/- English proof (translation)
Use `sb_evderiv (dZ ε Z) (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P` and prove the remaining obligations. Establish `hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b)` using `fun a b => (hZ a b).symm`. Introduce and unpack `(x | x)`. Use `(sb_curve Z g s x.1 x.2).congr_deriv ?_` and prove the remaining obligations. Simplify using `[dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]`.

Use `(sb_curve Z g s x.1 x.2).star.congr_deriv ?_` and prove the remaining obligations. Simplify using `[dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']`.
-/
theorem sb_evcurve {n : ℕ} (ε : Fin n → Bool) (Z g : Mat n) (s : ℝ) (P : Poly n) (hZ : LieU ε Z) :
    HasDerivAt (fun u : ℝ => ev (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) P) (ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z P)) s := by
  refine sb_evderiv (dZ ε Z)
    (fun u : ℝ => Sum.elim (fun x : Fin n × Fin n => (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2) (fun x => star ((NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z)) x.1 x.2))) s ?_ P
  have hZ' : ∀ a b, barM ε Z a b = (starRingEnd ℂ) (Z a b) := fun a b => (hZ a b).symm
  rintro (x | x)
  · refine (sb_curve Z g s x.1 x.2).congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib]
  · refine (sb_curve Z g s x.1 x.2).star.congr_deriv ?_
    simp [dZ, mkDerivation_X, Matrix.mul_apply, Matrix.sub_apply, Finset.sum_sub_distrib, hZ', star_sum, star_mul']

/- English proof (translation)
Introduce `n ε Z H P hZ hH`. Use `⟨?_, fun g s => ?_⟩` and prove the remaining obligations. Establish `h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2)`. Use `Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩` and prove the remaining obligations. Use `(sb_degdz ε Z (rP ε)).trans (sb_degrp ε)` as an intermediate fact.

Conclude with `(totalDegree_mul _ _).trans (by omega)`. Establish `h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2)`. Use `Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩` and prove the remaining obligations. Conclude with `(sb_degdz ε Z P).trans (by omega)`. Establish `e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P)` using `rfl`.

Rewrite using `[e]`. Conclude with `Submodule.add_mem _ h1 h2`. Establish `hE` using `sb_evcurve ε Z g s (rP ε) hZ`. Simplify using `only [sb_evrp] at hE`. Take `⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε))` from `⟨_, rfl⟩`.

Rewrite `hE` using `[← hc]`. Establish `hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s`. Use `Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Establish `him : c.im = 0`.

Establish `h1` using `Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE`. Simplify using `[Function.comp_def] at h1`. Conclude with `h1.unique (hasDerivAt_const _ _)`. Establish `hcre : ((c.re : ℝ) : ℂ) = c` using `Complex.ext (by simp) (by simp [him])`. Establish `hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))` using `((hH.1.differentiable (by simp)) _).hasDerivAt`.

Establish `hcomp` using `(hHd.comp s hre).ofReal_comp`. Establish `hP` using `sb_evcurve ε Z g s P hZ`. Establish `htot` using `hcomp.fun_mul hP`. Use `htot.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [adBas, bas, map_mul, ← hc, Function.comp_apply]`.

Rewrite using `[← hcre]`. Simplify using `only [Complex.ofReal_re, Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cutoffPolynomial_conjugation_deriv_mem_shapeSpan : StBasDeriv := by
  intro n ε Z H P hZ hH
  refine ⟨?_, fun g s => ?_⟩
  · have h1 : bas ε (deriv H) (dZ ε Z (rP ε) * P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨deriv H, _, sb_derivcut H hH, ?_, rfl⟩
      have := (sb_degdz ε Z (rP ε)).trans (sb_degrp ε)
      exact (totalDegree_mul _ _).trans (by omega)
    have h2 : bas ε H (dZ ε Z P) ∈ ShapeM ε (P.totalDegree + 2) := by
      refine Submodule.subset_span ⟨H, _, hH, ?_, rfl⟩
      exact (sb_degdz ε Z P).trans (by omega)
    have e : adBas ε Z H P = bas ε (deriv H) (dZ ε Z (rP ε) * P) + bas ε H (dZ ε Z P) := rfl
    rw [e]
    exact Submodule.add_mem _ h1 h2
  · have hE := sb_evcurve ε Z g s (rP ε) hZ
    simp only [sb_evrp] at hE
    obtain ⟨c, hc⟩ : ∃ c, c = ev (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)) (dZ ε Z (rP ε)) := ⟨_, rfl⟩
    rw [← hc] at hE
    have hre : HasDerivAt (fun u : ℝ => rM ε (NormedSpace.exp (-((u : ℂ) • Z)) * g * NormedSpace.exp ((u : ℂ) • Z))) c.re s := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hE
      simpa [Function.comp_def] using this
    have him : c.im = 0 := by
      have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt s hE
      simp [Function.comp_def] at h1
      exact h1.unique (hasDerivAt_const _ _)
    have hcre : ((c.re : ℝ) : ℂ) = c := Complex.ext (by simp) (by simp [him])
    have hHd : HasDerivAt H (deriv H (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z)))) (rM ε (NormedSpace.exp (-((s : ℂ) • Z)) * g * NormedSpace.exp ((s : ℂ) • Z))) :=
      ((hH.1.differentiable (by simp)) _).hasDerivAt
    have hcomp := (hHd.comp s hre).ofReal_comp
    have hP := sb_evcurve ε Z g s P hZ
    have htot := hcomp.fun_mul hP
    refine htot.congr_deriv ?_
    simp only [adBas, bas, map_mul, ← hc, Function.comp_apply]
    rw [← hcre]
    simp only [Complex.ofReal_re, Complex.ofReal_mul]
    ring

end GlobalTheory.PsCo.Pc1.B
