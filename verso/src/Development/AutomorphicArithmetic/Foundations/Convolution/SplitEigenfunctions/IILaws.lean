import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.SplitEig
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanLaws
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UILaws
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousAdelicGL2OfContinuousEntries
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.H UpperTheory.V.Z.Bc
open UpperTheory.V.Af.Smo (Eig EigAt)
open UpperTheory.ConvolutionTheory.RankTwoDescent

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

variable {E : Type} [Field E] [NumberField E]

private noncomputable def mm (N : MeasE E) (Ψ : GL (Fin 2) (A E) → ℂ) (y : GL (Fin 2) (A E)) : ℂ :=
  mean N fun x => Ψ (x * y)

/- English proof (translation)
The claim follows from `h.comp continuous_aE`.
-/
private theorem beta_cont {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : Continuous fun y => mean N fun x => Ψ (x * y)) : Continuous fun t : (A E)ˣ => mm N Ψ (aE t) :=
  h.comp continuous_aE

/- English proof (translation)
Take `⟨γ, hγ⟩` from `exists_ratGL_aE (F := E) e`. Rewrite using `[aE_mul, ← hγ]`. Conclude with `h γ _`.
-/
private theorem beta_inv {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : ∀ γ y, (mean N fun x => Ψ (x * (ratGL E 2 γ * y))) = mean N fun x => Ψ (x * y))
    (e : Eˣ) (t : (A E)ˣ) : mm N Ψ (aE (IdeleGroup.diagonal E e * t)) = mm N Ψ (aE t) := by
  obtain ⟨γ, hγ⟩ := exists_ratGL_aE (F := E) e
  rw [aE_mul, ← hγ]
  exact h γ _

/- English proof (translation)
Take `⟨g, hg⟩` from `exists_gl_mul_aE y`. Use `conv_lhs => rw [hg]`. Conclude with `h g _`.
-/
private theorem mm_det {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ}
    (h : ∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y))
    (y : GL (Fin 2) (A E)) : mm N Ψ y = mm N Ψ (aE (Matrix.GeneralLinearGroup.det y)) := by
  obtain ⟨g, hg⟩ := exists_gl_mul_aE y
  conv_lhs => rw [hg]
  exact h g _

/- English proof (translation)
Use `set c : GL (Fin 2) (A E) := GroundTheory.Automorphic.Reduction.centralSection E 2 s with hc`. Establish `e1 : mm N Ψ (c * aE t) = mm N Ψ (aE t)`. Unfold `mm`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Establish `: x * (c * aE t) = c * (x * aE t)`. Rewrite using `[← mul_assoc, ← mul_assoc]`. Use `congr 1`. Conclude with `(GroundTheory.Automorphic.Reduction.centralSection_mul_comm s x).symm`. Rewrite using `[this]`.

Conclude with `hP s _`. Rewrite using `[← e1, mm_det h (c * aE t), map_mul, det_aE, mul_comm]`.
-/
private theorem mm_central {N : MeasE E} {Ψ : GL (Fin 2) (A E) → ℂ} (hP : PosC Ψ)
    (h : ∀ (h : G1 E) y, (mean N fun x => Ψ (x * (gl h * y))) = mean N fun x => Ψ (x * y))
    (s : {r : ℝ // 0 < r}) (t : (A E)ˣ) :
    mm N Ψ (aE (t * Matrix.GeneralLinearGroup.det
      (GroundTheory.Automorphic.Reduction.centralSection E 2 s : GL (Fin 2) (A E)))) = mm N Ψ (aE t) := by
  set c : GL (Fin 2) (A E) := GroundTheory.Automorphic.Reduction.centralSection E 2 s with hc
  have e1 : mm N Ψ (c * aE t) = mm N Ψ (aE t) := by
    unfold mm
    congr 1
    funext x
    have : x * (c * aE t) = c * (x * aE t) := by
      rw [← mul_assoc, ← mul_assoc]
      congr 1
      exact (GroundTheory.Automorphic.Reduction.centralSection_mul_comm s x).symm
    rw [this]
    exact hP s _
  rw [← e1, mm_det h (c * aE t), map_mul, det_aE, mul_comm]

/- English proof (translation)
Unfold `UI`. Rewrite using `[integral_add h (h'.const_mul c), integral_const_mul]`.
-/
private theorem ui_add {β β' : (A E)ˣ → ℂ} (c : ℂ)
    (h : IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E))
    (h' : IntegrableOn (fun z : IdeleGroup.normOneSubgroup E => β' (z : IdeleGroup E)) (normOneFundamentalDomain E) (normOneMeasure E)) :
    (UI fun t => β t + c * β' t) = UI β + c * UI β' := by
  unfold UI
  rw [integral_add h (h'.const_mul c), integral_const_mul]

/- English proof (translation)
Unfold `mean`. Rewrite using `[integral_add h (h'.const_mul c), integral_const_mul]`.
-/
private theorem mean_add {N : MeasE E} {f f' : GL (Fin 2) (A E) → ℂ} (c : ℂ)
    (h : IntegrableOn (fun x => f (gl x)) N.D N.μ) (h' : IntegrableOn (fun x => f' (gl x)) N.D N.μ) :
    (mean N fun x => f x + c * f' x) = mean N f + c * mean N f' := by
  unfold mean
  rw [integral_add h (h'.const_mul c), integral_const_mul]

end UpperTheory.ConvolutionTheory.RankTwoDescent

/- English proof (translation)
Introduce `E _ _ N Ψ hΨ`. Take `⟨i1, c1, s1, r1⟩` from `meanLaws E N Ψ hΨ`. Establish `hβ` using `uiLaws E (fun t => mm N Ψ (aE t)) (beta_cont c1) (beta_inv r1)`. Use `⟨fun Ψ' hΨ' c => ?_, fun hP g => ?_⟩` and prove the remaining obligations. Take `⟨i2, c2, s2, r2⟩` from `meanLaws E N Ψ' hΨ'`.

Establish `hβ'` using `uiLaws E (fun t => mm N Ψ' (aE t)) (beta_cont c2) (beta_inv r2)`. Establish `e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t) + c * Ψ' (x * aE t)) = fun t => mm N Ψ (aE t) + c * mm N Ψ' (aE t)`. Use function extensionality and compare the values at `t`. Conclude with `mean_add (f := fun x => Ψ (x * aE t)) (f' := fun x => Ψ' (x * aE t)) c (i1 _) (i2 _)`. Unfold `II`.

Rewrite using `[e]`. Conclude with `ui_add c hβ.1 hβ'.1`. Use `set d₀ : (A E)ˣ := Matrix.GeneralLinearGroup.det g with hd₀ set s : {r : ℝ // 0 < r} := (IdeleGroup.ideleModule E d₀)⁻¹ with hs set d₁ : (A E)ˣ := Matrix.GeneralLinearGroup.det (GroundTheory.Automorphic.Reduction.centralSection E 2 s : GL (Fin 2) (A E)) with hd₁`. Establish `hm : IdeleGroup.ideleModule E d₁ = s` using `GroundTheory.Automorphic.Reduction.detModule_centralSection (K := E) (n := 2) (by norm_num) s`. Establish `hab : ab (d₀ * d₁) = 1`.

Establish `: IdeleGroup.ideleModule E (d₀ * d₁) = 1` using `by rw [map_mul, hm, hs, mul_inv_cancel]`. Conclude with `congrArg Subtype.val this`. Establish `e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t * g)) = fun t => mm N Ψ (aE (t * (d₀ * d₁)))`. Use function extensionality and compare the values at `t`. Establish `e1 : (mean N fun x => Ψ (x * aE t * g)) = mm N Ψ (aE t * g)`.

Unfold `mm`. Simplify using `only [mul_assoc]`. Rewrite using `[e1, mm_det s1, map_mul, det_aE, ← mul_assoc]`. Conclude with `(mm_central hP s1 s _).symm`. Unfold `II`.

Rewrite using `[e]`. Conclude with `hβ.2.2 _ hab`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.iiLaws :
    IILaws := by
  intro E _ _ N Ψ hΨ
  obtain ⟨i1, c1, s1, r1⟩ := meanLaws E N Ψ hΨ
  have hβ := uiLaws E (fun t => mm N Ψ (aE t)) (beta_cont c1) (beta_inv r1)
  refine ⟨fun Ψ' hΨ' c => ?_, fun hP g => ?_⟩
  · obtain ⟨i2, c2, s2, r2⟩ := meanLaws E N Ψ' hΨ'
    have hβ' := uiLaws E (fun t => mm N Ψ' (aE t)) (beta_cont c2) (beta_inv r2)
    have e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t) + c * Ψ' (x * aE t)) =
        fun t => mm N Ψ (aE t) + c * mm N Ψ' (aE t) := by
      funext t
      exact mean_add (f := fun x => Ψ (x * aE t)) (f' := fun x => Ψ' (x * aE t)) c (i1 _) (i2 _)
    unfold II
    rw [e]
    exact ui_add c hβ.1 hβ'.1
  · set d₀ : (A E)ˣ := Matrix.GeneralLinearGroup.det g with hd₀
    set s : {r : ℝ // 0 < r} := (IdeleGroup.ideleModule E d₀)⁻¹ with hs
    set d₁ : (A E)ˣ := Matrix.GeneralLinearGroup.det
      (GroundTheory.Automorphic.Reduction.centralSection E 2 s : GL (Fin 2) (A E)) with hd₁
    have hm : IdeleGroup.ideleModule E d₁ = s :=
      GroundTheory.Automorphic.Reduction.detModule_centralSection (K := E) (n := 2) (by norm_num) s
    have hab : ab (d₀ * d₁) = 1 := by
      have : IdeleGroup.ideleModule E (d₀ * d₁) = 1 := by rw [map_mul, hm, hs, mul_inv_cancel]
      exact congrArg Subtype.val this
    have e : (fun t : (A E)ˣ => mean N fun x => Ψ (x * aE t * g)) = fun t => mm N Ψ (aE (t * (d₀ * d₁))) := by
      funext t
      have e1 : (mean N fun x => Ψ (x * aE t * g)) = mm N Ψ (aE t * g) := by
        unfold mm
        simp only [mul_assoc]
      rw [e1, mm_det s1, map_mul, det_aE, ← mul_assoc]
      exact (mm_central hP s1 s _).symm
    unfold II
    rw [e]
    exact hβ.2.2 _ hab
