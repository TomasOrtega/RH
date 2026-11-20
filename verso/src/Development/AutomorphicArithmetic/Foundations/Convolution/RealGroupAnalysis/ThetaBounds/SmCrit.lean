import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.FderivOfExp

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical ContDiff

namespace UpperTheory.ConvolutionTheory.R2.Ff

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

private noncomputable def invL (x : Lie E 2) : Lie E 2 := toL ((Matrix.of x)⁻¹)

/- English proof (translation)
Simplify using `[invL, Matrix.coe_units_inv]`.
-/
private theorem invL_val (u : GL (Fin 2) (Cinf E)) : invL (toL u.val) = toL (u⁻¹).val := by
  simp [invL, Matrix.coe_units_inv]

/- English proof (translation)
Establish `hdet : ContDiffOn ℝ ∞ (fun x : Lie E 2 => Ring.inverse (Matrix.of x).det) (invSet E 2)`. Introduce `x hx`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).1 hx`. Establish `h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (Matrix.of x).det` using `hu ▸ contDiffAt_ringInverse ℝ u`. Conclude with `(h1.comp x contDiff_det.contDiffAt).contDiffWithinAt`.

Establish `hent : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => x i j` using `fun i j => (contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)`. Establish `hadj : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => (Matrix.adjugate (Matrix.of x)) i j`. Introduce `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]`. Conclude with `hent 1 1`.

Conclude with `(hent 0 1).neg`. Conclude with `(hent 1 0).neg`. Conclude with `hent 0 0`. Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_` and prove the remaining obligations. Use `(hdet.mul (hadj i j).contDiffOn).congr fun x _ => ?_` and prove the remaining obligations.

Simplify using `[invL, Matrix.inv_def]`.
-/
private theorem contDiffOn_invL : ContDiffOn ℝ ∞ (invL (E := E)) (invSet E 2) := by
  have hdet : ContDiffOn ℝ ∞ (fun x : Lie E 2 => Ring.inverse (Matrix.of x).det) (invSet E 2) := by
    intro x hx
    obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).1 hx
    have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (Matrix.of x).det :=
      hu ▸ contDiffAt_ringInverse ℝ u
    exact (h1.comp x contDiff_det.contDiffAt).contDiffWithinAt
  have hent : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => x i j := fun i j =>
    (contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)
  have hadj : ∀ i j, ContDiff ℝ ∞ fun x : Lie E 2 => (Matrix.adjugate (Matrix.of x)) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.adjugate_fin_two]
    · exact hent 1 1
    · exact (hent 0 1).neg
    · exact (hent 1 0).neg
    · exact hent 0 0
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
  refine (hdet.mul (hadj i j).contDiffOn).congr fun x _ => ?_
  simp [invL, Matrix.inv_def]

/- English proof (translation)
Rewrite using `[← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]`.
-/
private theorem chart_eq (Φ : GL (Fin 2) (A E) → ℂ) (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    chart Φ g = chart Φ (g * infGL E 2 u) ∘ lmul (toL (u⁻¹).val) := by
  rw [← chart_mul, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]

/- English proof (translation)
Establish `e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E 2` using `u.inv_mul`. Establish `hd : DifferentiableAt ℝ (chart Φ (g * infGL E 2 u)) (lmul (toL (u⁻¹).val) (toL u.val))`. Rewrite using `[e1]`. Conclude with `(h _).1`. Establish `hc` using `hd.comp (toL u.val) (lmul (toL (u⁻¹).val)).differentiableAt`.

Rewrite `hc` using `[← chart_eq]`. Use `⟨hc, fun Z => ?_⟩` and prove the remaining obligations. Rewrite using `[chart_eq Φ g u, fderiv_comp _ hd (lmul (toL (u⁻¹).val)).differentiableAt, e1, ContinuousLinearMap.fderiv]`. Conclude with `(h _).2 _`.
-/
private theorem fd {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) (u : GL (Fin 2) (Cinf E)) :
    DifferentiableAt ℝ (chart Φ g) (toL u.val) ∧
      ∀ Z, fderiv ℝ (chart Φ g) (toL u.val) Z = T (lmul (toL (u⁻¹).val) Z) (g * infGL E 2 u) := by
  have e1 : lmul (toL (u⁻¹).val) (toL u.val) = oneL E 2 := u.inv_mul
  have hd : DifferentiableAt ℝ (chart Φ (g * infGL E 2 u)) (lmul (toL (u⁻¹).val) (toL u.val)) := by
    rw [e1]; exact (h _).1
  have hc := hd.comp (toL u.val) (lmul (toL (u⁻¹).val)).differentiableAt
  rw [← chart_eq] at hc
  refine ⟨hc, fun Z => ?_⟩
  rw [chart_eq Φ g u, fderiv_comp _ hd (lmul (toL (u⁻¹).val)).differentiableAt, e1,
    ContinuousLinearMap.fderiv]
  exact (h _).2 _

/- English proof (translation)
Introduce `x hx`. Take `⟨u, hu⟩` from `id hx`. Take `rfl : x = toL u.val` from `hu.symm`. Conclude with `(fd h g u).1.differentiableWithinAt`.
-/
private theorem diffOn {Φ : GL (Fin 2) (A E) → ℂ} {T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)}
    (h : ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (g : GL (Fin 2) (A E)) : DifferentiableOn ℝ (chart Φ g) (invSet E 2) := by
  intro x hx
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = toL u.val := hu.symm
  exact (fd h g u).1.differentiableWithinAt

/- English proof (translation)
Use `conv_lhs => rw [← b.sum_repr Y]`. Rewrite using `[map_sum, Finset.sum_apply]`. Simplify using `only [map_smul, Pi.smul_apply]`.
-/
private theorem T_apply (T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ)) (b : Module.Basis (Fin (Module.finrank ℝ (Lie E 2))) ℝ (Lie E 2))
    (Y : Lie E 2) (h : GL (Fin 2) (A E)) : T Y h = ∑ j, (b.repr Y j) • T (b j) h := by
  conv_lhs => rw [← b.sum_repr Y]
  rw [map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Introduce `Φ hΦ g`. Take `⟨T, -, h⟩` from `hS Φ hΦ`. Rewrite using `[Nat.cast_zero]`.

Conclude with `contDiffOn_zero.2 (diffOn h g).continuousOn`. Consider the case `succ n ih`. Introduce `Φ hΦ g`. Take `⟨T, hT, h⟩` from `hS Φ hΦ`. Rewrite using `[Nat.cast_add, Nat.cast_one]`.

Use `(contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet).2 ⟨diffOn h g, by simp, ?_⟩` and prove the remaining obligations. Use `contDiffOn_clm_apply.2 fun Z => ?_` and prove the remaining obligations. Set `b` to `Module.finBasis ℝ (Lie E 2)`. Establish `hinv : ContDiffOn ℝ n (invL (E` using `E)) (invSet E 2) := contDiffOn_invL.of_le (by exact_mod_cast le_top)`. Establish `key : ContDiffOn ℝ n (fun x => ∑ j, (b.repr (rmul Z (invL x)) j) • chart (T (b j)) g x) (invSet E 2)` using `ContDiffOn.sum fun j _ => ContDiffOn.smul ((LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn ((rmul Z).contDiff.comp_contDiffOn hinv)) (ih _ (hT _) g)`.

Use `key.congr fun x hx => ?_` and prove the remaining obligations. Take `⟨u, hu⟩` from `id hx`. Take `rfl : x = toL u.val` from `hu.symm`. Rewrite using `[(fd h g u).2 Z, T_apply T b, invL_val]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[chart_val]`. Both sides reduce to the same expression.
-/
private theorem smN (S : Submodule ℂ (GL (Fin 2) (A E) → ℂ))
    (hS : ∀ Φ ∈ S, ∃ T : Lie E 2 →ₗ[ℝ] (GL (Fin 2) (A E) → ℂ), (∀ X, T X ∈ S) ∧
      ∀ g, DifferentiableAt ℝ (chart Φ g) (oneL E 2) ∧ ∀ X, fderiv ℝ (chart Φ g) (oneL E 2) X = T X g)
    (n : ℕ) : ∀ Φ ∈ S, ∀ g, ContDiffOn ℝ n (chart Φ g) (invSet E 2) := by
  induction n with
  | zero =>
    intro Φ hΦ g
    obtain ⟨T, -, h⟩ := hS Φ hΦ
    rw [Nat.cast_zero]
    exact contDiffOn_zero.2 (diffOn h g).continuousOn
  | succ n ih =>
    intro Φ hΦ g
    obtain ⟨T, hT, h⟩ := hS Φ hΦ
    rw [Nat.cast_add, Nat.cast_one]
    refine (contDiffOn_succ_iff_fderiv_of_isOpen isOpen_invSet).2 ⟨diffOn h g, by simp, ?_⟩
    refine contDiffOn_clm_apply.2 fun Z => ?_
    let b := Module.finBasis ℝ (Lie E 2)
    have hinv : ContDiffOn ℝ n (invL (E := E)) (invSet E 2) :=
      contDiffOn_invL.of_le (by exact_mod_cast le_top)
    have key : ContDiffOn ℝ n (fun x => ∑ j, (b.repr (rmul Z (invL x)) j) • chart (T (b j)) g x) (invSet E 2) :=
      ContDiffOn.sum fun j _ => ContDiffOn.smul
        ((LinearMap.toContinuousLinearMap (b.coord j)).contDiff.comp_contDiffOn
          ((rmul Z).contDiff.comp_contDiffOn hinv)) (ih _ (hT _) g)
    refine key.congr fun x hx => ?_
    obtain ⟨u, hu⟩ := id hx
    obtain rfl : x = toL u.val := hu.symm
    rw [(fd h g u).2 Z, T_apply T b, invL_val]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chart_val]
    rfl

end UpperTheory.ConvolutionTheory.R2.Ff

/- English proof (translation)
Introduce `E _ _ _ S hc hd Φ hΦ g`. Use `contDiffOn_infty.2 fun n => smN S (fun Φ hΦ => ?_) n Φ hΦ g` and prove the remaining obligations. Take `⟨T, hT, h⟩` from `hd Φ hΦ`. Conclude with `⟨T, hT, smFre E Φ T (fun X g => hc _ (hT X) g) h⟩`.
-/
theorem UpperTheory.ConvolutionTheory.R2.Ff.smCrit :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E], SmCrit E := by
  intro E _ _ _ S hc hd Φ hΦ g
  refine contDiffOn_infty.2 fun n => smN S (fun Φ hΦ => ?_) n Φ hΦ g
  obtain ⟨T, hT, h⟩ := hd Φ hΦ
  exact ⟨T, hT, smFre E Φ T (fun X g => hc _ (hT X) g) h⟩
