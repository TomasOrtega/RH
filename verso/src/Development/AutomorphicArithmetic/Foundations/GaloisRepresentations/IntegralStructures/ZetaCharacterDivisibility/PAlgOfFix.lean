import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExponentHeckeCharCompNormConjEmbedding
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

open GlobalTheory.CuspRep.InfType GlobalTheory.CuspRep.AlgExpo

/- English proof (translation)
Rewrite using `[← chiInf_expU_atEmb]`. Establish `h1 : cj E (infId E (expU (atEmb τ z))) = infId E (expU (atEmb τ z))`. Use `(GlobalTheory.NormExpo.conjAd_infId E _).trans ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.NormExpo.star_expU_atEmb, hs]`. Establish `h2 : chiInf χ (expU (atEmb τ z)) = 1` using `hfix _ h1`.

Rewrite using `[h2]`. Both sides reduce to the same expression.
-/
private theorem chi_fixed {E : Type} [Field E] [NumberField E] [IsCMField E] (χ : HChar E)
    (hfix : ∀ z, cj E z = z → χ.1 z = 1) (τ : E →+* ℂ) (z : ℂ)
    (hs : expU (atEmb τ (starRingEnd ℂ z)) = expU (atEmb τ z)) :
    Complex.exp (expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z) = 1 := by
  rw [← chiInf_expU_atEmb]
  have h1 : cj E (infId E (expU (atEmb τ z))) = infId E (expU (atEmb τ z)) := by
    refine (GlobalTheory.NormExpo.conjAd_infId E _).trans ?_
    rw [GlobalTheory.NormExpo.star_expU_atEmb, hs]
  have h2 : chiInf χ (expU (atEmb τ z)) = 1 := hfix _ h1
  rw [h2]
  rfl

/- English proof (translation)
Use `Units.ext (funext fun w => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Complex.exp (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I)) w) = Complex.exp (atEmb τ ((Real.pi : ℂ) * Complex.I) w)`. Unfold `atEmb`. Distinguish the cases in `hw : w = InfinitePlace.mk τ`. Apply the tactic sequence `subst hw split_ifs <;> simp [Complex.exp_neg, Complex.exp_pi_mul_I]`.

Simplify using `[Pi.single_eq_of_ne hw]`.
-/
private theorem expU_neg_pi {E : Type} [Field E] [NumberField E] [IsCMField E] (τ : E →+* ℂ) :
    expU (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I))) = expU (atEmb τ ((Real.pi : ℂ) * Complex.I)) := by
  classical
  refine Units.ext (funext fun w => ?_)
  change Complex.exp (atEmb τ (starRingEnd ℂ ((Real.pi : ℂ) * Complex.I)) w) =
    Complex.exp (atEmb τ ((Real.pi : ℂ) * Complex.I) w)
  unfold atEmb
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw
    split_ifs <;> simp [Complex.exp_neg, Complex.exp_pi_mul_I]
  · simp [Pi.single_eq_of_ne hw]

/- English proof (translation)
Establish `hf : (fun t : ℝ => Complex.exp ((p + q) * t)) = fun _ => 1`. Use function extensionality and compare the values at `t`. Use `h t` as an intermediate fact. Rewrite `this` using `[Complex.conj_ofReal]`. Rewrite using `[add_mul]`.

Conclude with `this`. Establish `hd : HasDerivAt (fun t : ℝ => Complex.exp ((p + q) * t)) (Complex.exp ((p + q) * ((0 : ℝ) : ℂ)) * ((p + q) * 1)) 0`. Establish `h0 : HasDerivAt (fun t : ℝ => (p + q) * (t : ℂ)) ((p + q) * 1) 0` using `(Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (p + q)`. Conclude with `h0.cexp`. Rewrite `hd` using `[hf]`.

Use `hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))` as an intermediate fact. Simplify using `using this`.
-/
private theorem add_eq_zero_of {p q : ℂ} (h : ∀ t : ℝ, Complex.exp (p * t + q * starRingEnd ℂ (t : ℂ)) = 1) : p + q = 0 := by
  have hf : (fun t : ℝ => Complex.exp ((p + q) * t)) = fun _ => 1 := by
    funext t
    have := h t
    rw [Complex.conj_ofReal] at this
    rw [add_mul]; exact this
  have hd : HasDerivAt (fun t : ℝ => Complex.exp ((p + q) * t)) (Complex.exp ((p + q) * ((0 : ℝ) : ℂ)) * ((p + q) * 1)) 0 := by
    have h0 : HasDerivAt (fun t : ℝ => (p + q) * (t : ℂ)) ((p + q) * 1) 0 :=
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (p + q)
    exact h0.cexp
  rw [hf] at hd
  have := hd.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using this

/- English proof (translation)
Introduce `E _ _ _ χ hfix`. Establish `key : ∀ τ : E →+* ℂ, ∃ n : ℤ, expo χ τ = n`. Introduce `τ`. Establish `hpq : expo χ τ + expo χ (ComplexEmbedding.conjugate τ) = 0` using `add_eq_zero_of fun t => chi_fixed χ hfix τ t (by rw [Complex.conj_ofReal])`. Establish `h` using `chi_fixed χ hfix τ _ (expU_neg_pi τ)`.

Establish `hq : expo χ (ComplexEmbedding.conjugate τ) = - expo χ τ` using `by linear_combination hpq`. Rewrite `h` using `[hq]`. Take `⟨n, hn⟩` from `Complex.exp_eq_one_iff.1 h`. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hpi : (Real.pi : ℂ) ≠ 0` using `by exact_mod_cast Real.pi_ne_zero`.

Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `by simp [hpi, Complex.I_ne_zero]`. Apply `mul_right_cancel₀ h2` to reduce the goal to its premises. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn`. Take the linear combination `hn`. Use `choose n hn using key`.

Conclude with `⟨n, isAlgPos_of_expo E χ n hn⟩`.
-/
theorem UpperTheory.Gal.Int.Div.algOfFix_of :
    AlgOfFix := by
  intro E _ _ _ χ hfix
  have key : ∀ τ : E →+* ℂ, ∃ n : ℤ, expo χ τ = n := by
    intro τ
    have hpq : expo χ τ + expo χ (ComplexEmbedding.conjugate τ) = 0 :=
      add_eq_zero_of fun t => chi_fixed χ hfix τ t (by rw [Complex.conj_ofReal])
    have h := chi_fixed χ hfix τ _ (expU_neg_pi τ)
    have hq : expo χ (ComplexEmbedding.conjugate τ) = - expo χ τ := by linear_combination hpq
    rw [hq] at h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
    refine ⟨n, ?_⟩
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ h2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I] at hn
    linear_combination hn
  choose n hn using key
  exact ⟨n, isAlgPos_of_expo E χ n hn⟩
