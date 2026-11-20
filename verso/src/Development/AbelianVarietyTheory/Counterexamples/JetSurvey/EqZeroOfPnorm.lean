import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupNormFromNet

noncomputable section

namespace GlobalTheory.NetNormExamples

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

/- English proof (translation)
The claim follows from `mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)`.
-/
theorem pnorm_nonneg (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) :
    0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (pnorm_fac_nonneg X la x)

/- English proof (translation)
Unfold `supN`. Rewrite using `[← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]`. Conclude with `le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p`.
-/
theorem pnorm_le_supN (U : Unf Xo c σ r) (la) {P : FDSec U.X} (hP : P ∈ holSub U.X la) (p : FPt U.X) :
    (U.X p.1).pnorm (la p.1) (P p.1) p.2 ≤ supN U.X la P := by
  unfold supN
  rw [← ENNReal.ofReal_le_iff_le_toReal (supE_ne_top _ _ hP)]
  exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (P p.1) p.2)) p

/- English proof (translation)
Establish `hne : ∀ τ i, dmin X.Gm x τ i ≠ 0` using `fun τ i e => by`. Use `(hx τ).2 i` as an intermediate fact. Rewrite `this` using `[e]`. Simplify using `at this`. Unfold `Data.pnorm at h0`.

Use `norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))` and prove the remaining obligations. Conclude with `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _`.
-/
theorem eq_zero_of_pnorm (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (h0 : X.pnorm la P x = 0) : P x = 0 := by
  have hne : ∀ τ i, dmin X.Gm x τ i ≠ 0 := fun τ i e => by
    have := (hx τ).2 i
    rw [e] at this; simp at this
  unfold Data.pnorm at h0
  refine norm_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (ne_of_gt ?_))
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hne _ _) (hne _ _))) _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Establish `e : (starRingEnd ℂ) H.rt0 = H.rt0`. Establish `h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0` using `h1`. Rewrite `h3` using `[show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2]`. Then use the resulting hypothesis.

Establish `him : H.rt0.im = 0` using `Complex.conj_eq_iff_im.mp e`. Establish `hre` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Simplify using `only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.

Introduce `h`. Use `goodEmb_goodOf c σ` as an intermediate fact. Unfold `goodOf at this`. Rewrite `this` using `[if_neg h]`. Then use the resulting hypothesis.
-/
theorem good_conj_iff (c : Coeff l) (σ : c.F →+* ℂ) : GoodEmb c (ComplexEmbedding.conjugate σ) ↔ ¬ GoodEmb c σ := by
  constructor
  · intro h1 h2
    have e : (starRingEnd ℂ) H.rt0 = H.rt0 := by
      have h3 : (starRingEnd ℂ) ((σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ) = H.rt0 := h1
      rwa [show (σ.comp (IntermediateField.inclusion c.le).toRingHom) (baseKA l).ρ = H.rt0 from h2] at h3
    have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.mp e
    have hre := congrArg Complex.re H.sqrt_neg_disc_sq
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  · intro h
    have := goodEmb_goodOf c σ
    unfold goodOf at this
    rwa [if_neg h] at this

/- English proof (translation)
Unfold `goodOf`. Distinguish the cases in `h : GoodEmb c σ`. Rewrite using `[if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate]`.

Rewrite using `[if_pos ((good_conj_iff c σ).2 h), if_neg h]`. Both sides reduce to the same expression.
-/
theorem goodOf_conj (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (ComplexEmbedding.conjugate σ) = goodOf c σ := by
  unfold goodOf
  by_cases h : GoodEmb c σ
  · rw [if_neg (fun h' => (good_conj_iff c σ).1 h' h), if_pos h]
    ext x; simp [ComplexEmbedding.conjugate]
  · rw [if_pos ((good_conj_iff c σ).2 h), if_neg h]; rfl

def coordAt (U : Unf Xo c σ r) (a : ℝ) (p : FPt U.X) : Rul Xo c →ₛₗ[σ] ℂ where
  toFun f := (a : ℂ) * rdU U f p.1 p.2
  map_add' f g := by rw [map_add, Pi.add_apply, Pi.add_apply, mul_add]
  map_smul' x f := by rw [map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]

end GlobalTheory.NetNormExamples
