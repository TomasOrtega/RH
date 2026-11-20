import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltNormUltrametricEqZero
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.TiltAbs

/- English proof (translation)
Introduce `l _ o ζ ζ' ho h1 h2 hne`. Establish `hl : 1 < l` using `(Fact.out : l.Prime).one_lt`. Use `set d : Formalism.Per.Fl l := ζ - ζ' with hd`. Establish `hdpow : d ^ (l ^ o) = d`. Rewrite using `[hd, sub_pow_char_pow, h1, h2]`.

Establish `hd0 : d ≠ 0` using `sub_ne_zero.2 hne`. Use `set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha`. Establish `ha0 : a ≠ 0`. Introduce `h`. Apply `hd0` to reduce the goal to its premises.

Use `(untilt_ultrametric_definite l d 0).2 ?_` and prove the remaining obligations. Establish `: ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0` using `norm_eq_zero.1 h`. Conclude with `Subtype.ext this`. Establish `hapow : a ^ (l ^ o) = a`. Use `congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow` as an intermediate fact.

Simplify using `only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this`. Conclude with `this`. Establish `hlo : 1 ≤ l ^ o` using `Nat.one_le_pow _ _ (by omega)`. Establish `hlo' : l ^ o - 1 ≠ 0`. Establish `: 1 < l ^ o` using `Nat.one_lt_pow (by omega) hl`.

Use linear arithmetic over natural numbers and integers. Establish `hsub : a ^ (l ^ o - 1) = 1`. Establish `: a ^ (l ^ o - 1) * a = 1 * a`. Rewrite using `[← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]`. Conclude with `mul_right_cancel₀ ha0 this`.

Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub`.
-/
theorem norm_untilt_sub_eq_one_of_pow_fixed :
    ∀ (l : ℕ) [Fact l.Prime] (o : ℕ) (ζ ζ' : Formalism.Per.Fl l), 0 < o → ζ ^ (l ^ o) = ζ →
      ζ' ^ (l ^ o) = ζ' → ζ ≠ ζ' → ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 := by
  intro l _ o ζ ζ' ho h1 h2 hne
  have hl : 1 < l := (Fact.out : l.Prime).one_lt
  set d : Formalism.Per.Fl l := ζ - ζ' with hd
  have hdpow : d ^ (l ^ o) = d := by
    rw [hd, sub_pow_char_pow, h1, h2]
  have hd0 : d ≠ 0 := sub_ne_zero.2 hne
  set a : ℝ := ‖((d.untilt : Formalism.Per.OC l) : ℂ_[l])‖ with ha
  have ha0 : a ≠ 0 := by
    intro h
    apply hd0
    refine (untilt_ultrametric_definite l d 0).2 ?_
    have : ((d.untilt : Formalism.Per.OC l) : ℂ_[l]) = 0 := norm_eq_zero.1 h
    exact Subtype.ext this
  have hapow : a ^ (l ^ o) = a := by
    have := congrArg (fun x : Formalism.Per.Fl l => ‖((x.untilt : Formalism.Per.OC l) : ℂ_[l])‖) hdpow
    simp only [map_pow, SubmonoidClass.coe_pow, norm_pow] at this
    exact this
  have hlo : 1 ≤ l ^ o := Nat.one_le_pow _ _ (by omega)
  have hlo' : l ^ o - 1 ≠ 0 := by
    have : 1 < l ^ o := Nat.one_lt_pow (by omega) hl
    omega
  have hsub : a ^ (l ^ o - 1) = 1 := by
    have : a ^ (l ^ o - 1) * a = 1 * a := by
      rw [← pow_succ, Nat.sub_add_cancel hlo, hapow, one_mul]
    exact mul_right_cancel₀ ha0 this
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hlo').1 hsub

end GlobalTheory.TiltAbs
