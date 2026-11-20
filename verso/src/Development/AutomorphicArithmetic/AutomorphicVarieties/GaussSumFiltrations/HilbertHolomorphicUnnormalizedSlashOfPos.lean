import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaussSumFiltrations.EvenPos

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd GlobalTheory.HilbertThetaSeries
open scoped Matrix

noncomputable section

namespace GlobalTheory.HilbertThetaSeries.HolKeep

open UpperHalfPlane hiding I

variable {F : Type} [Field F] [NumberField F]

def U (F : Type) [Field F] [NumberField F] : Set (InfinitePlace F → ℂ) := {z | ∀ v, 0 < (z v).im}

/- English proof (translation)
Simplify using `[cmp, Matrix.GeneralLinearGroup.map_det]`.
-/
theorem cmp_det (h : GL (Fin 2) (InfinitePlace F → ℝ)) (v : InfinitePlace F) :
    ((cmp v h).det : ℝ) = (h : Matrix (Fin 2) (Fin 2) (InfinitePlace F → ℝ)).det v := by
  simp [cmp, Matrix.GeneralLinearGroup.map_det]

def mob (h : GL (Fin 2) (InfinitePlace F → ℝ)) (z : InfinitePlace F → ℂ) : InfinitePlace F → ℂ :=
  fun v => num (cmp v h) (z v) / denom (cmp v h) (z v)

/- English proof (translation)
Establish `hd : 0 < ((cmp v h).det : ℝ)`. Rewrite using `[cmp_det]`. Conclude with `hh v`. Establish `hzv : 0 < (z v).im` using `hz v`. Use `show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im`.

Rewrite using `[moebius_im]`. Conclude with `div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')`.
-/
theorem mob_im_pos {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) (v) :
    0 < (mob h z v).im := by
  have hd : 0 < ((cmp v h).det : ℝ) := by
    rw [cmp_det]
    exact hh v
  have hzv : 0 < (z v).im := hz v
  show 0 < (num (cmp v h) (z v) / denom (cmp v h) (z v)).im
  rw [moebius_im]
  exact div_pos (mul_pos hd hzv) (normSq_denom_pos _ hzv.ne')

/- English proof (translation)
Introduce `z hz`. Use `show ∀ v, 0 < (mob h z v).im`. Conclude with `fun v => mob_im_pos hh hz v`.
-/
theorem mob_mapsTo {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) : Set.MapsTo (mob h) (U F) (U F) := by
  intro z hz
  show ∀ v, 0 < (mob h z v).im
  exact fun v => mob_im_pos hh hz v

/- English proof (translation)
Rewrite using `[differentiableOn_pi]`. Introduce `v z hz`. Establish `hzv : (z v).im ≠ 0` using `(hz v).ne'`. Establish `hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z` using `differentiable_apply v z`. Establish `hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z` using `(hp.const_mul _).add_const _`.

Establish `hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z` using `(hp.const_mul _).add_const _`. Apply `DifferentiableAt.differentiableWithinAt` to reduce the goal to its premises. Use `show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z`. Simplify using `only [div_eq_mul_inv]`. Conclude with `hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))`.
-/
theorem mob_diff (h : GL (Fin 2) (InfinitePlace F → ℝ)) : DifferentiableOn ℂ (mob h) (U F) := by
  rw [differentiableOn_pi]
  intro v z hz
  have hzv : (z v).im ≠ 0 := (hz v).ne'
  have hp : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => w v) z := differentiable_apply v z
  have hn : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => num (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  have hd : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => denom (cmp v h) (w v)) z :=
    (hp.const_mul _).add_const _
  apply DifferentiableAt.differentiableWithinAt
  show DifferentiableAt ℂ (fun w => num (cmp v h) (w v) / denom (cmp v h) (w v)) z
  simp only [div_eq_mul_inv]
  exact hn.mul (hd.inv (denom_ne_zero_of_im _ hzv))

/- English proof (translation)
Use function extensionality and compare the values at `v`. Rewrite using `[act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]`. Apply `UpperHalfPlane.ext` to reduce the goal to its premises. Rewrite using `[coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]`. Both sides reduce to the same expression.
-/
theorem act_eq {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {z} (hz : z ∈ U F) :
    act h (fun v => ofComplex (z v)) = fun v => ofComplex (mob h z v) := by
  funext v
  rw [act.eq_1, ofComplex_apply_of_im_pos (hz v), ofComplex_apply_of_im_pos (mob_im_pos hh hz v)]
  apply UpperHalfPlane.ext
  rw [coe_smul_of_det_pos (by rw [cmp_det]; exact hh v)]
  rfl

/- English proof (translation)
Establish `hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F)` using `hf`. Establish `hcomp` using `hF.comp (mob_diff h) (mob_mapsTo hh)`. Establish `hden : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F)`. Introduce `z hz`. Establish `hne : (∏ v, denom (cmp v h) (z v)) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'`.

Establish `hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z`. Simplify using `only [denom]`. Use `fun_prop`. Conclude with `((hpr.inv hne).pow k).differentiableWithinAt`. Use `show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)`.

Use `(hden.mul hcomp).congr ?_` and prove the remaining obligations. Introduce `z hz`. Establish `hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v` using `fun v => by`. Rewrite using `[ofComplex_apply_of_im_pos (hz v)]`. Simplify using `only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]`.
-/
theorem hilbertHolomorphic_unnormalizedSlash_of_pos (k : ℕ) {h : GL (Fin 2) (InfinitePlace F → ℝ)} (hh : Pos h) {f : Hn F → ℂ} (hf : Hol f) :
    Hol (sl0 k h f) := by
  have hF : DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => f (fun v => ofComplex (z v))) (U F) := hf
  have hcomp := hF.comp (mob_diff h) (mob_mapsTo hh)
  have hden : DifferentiableOn ℂ
      (fun z : InfinitePlace F → ℂ => (∏ v, denom (cmp v h) (z v))⁻¹ ^ k) (U F) := by
    intro z hz
    have hne : (∏ v, denom (cmp v h) (z v)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun v _ => denom_ne_zero_of_im _ (hz v).ne'
    have hpr : DifferentiableAt ℂ (fun w : InfinitePlace F → ℂ => ∏ v, denom (cmp v h) (w v)) z := by
      simp only [denom]
      fun_prop
    exact ((hpr.inv hne).pow k).differentiableWithinAt
  show DifferentiableOn ℂ (fun z : InfinitePlace F → ℂ => sl0 k h f (fun v => ofComplex (z v))) (U F)
  refine (hden.mul hcomp).congr ?_
  intro z hz
  have hc : ∀ v, ((ofComplex (z v) : ℍ) : ℂ) = z v := fun v => by
    rw [ofComplex_apply_of_im_pos (hz v)]
  simp only [sl0.eq_1, act_eq hh hz, hc, Function.comp_apply, Pi.mul_apply]

/- English proof (translation)
Introduce `F _ _ k f g c hf hg`. Use `⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg, differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩` and prove the remaining obligations. Conclude with `DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (k : ℕ) (f g : Hn F → ℂ) (c : ℂ), Hol f → Hol g → Hol (f + g) ∧ Hol (c • f) ∧ Hol (f * g) ∧ Hol (1 : Hn F → ℂ) ∧ Hol (0 : Hn F → ℂ) ∧ ∀ h : GL (Fin 2) (InfinitePlace F → ℝ), Pos h → Hol (sl0 k h f) ∧ Hol (sl k h f) := by
  intro F _ _ k f g c hf hg
  refine ⟨DifferentiableOn.add hf hg, DifferentiableOn.const_smul hf c, DifferentiableOn.mul hf hg,
    differentiableOn_const 1, differentiableOn_const 0, fun h hh => ⟨hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf, ?_⟩⟩
  exact DifferentiableOn.mul (differentiableOn_const _) (hilbertHolomorphic_unnormalizedSlash_of_pos k hh hf)

end GlobalTheory.HilbertThetaSeries.HolKeep
