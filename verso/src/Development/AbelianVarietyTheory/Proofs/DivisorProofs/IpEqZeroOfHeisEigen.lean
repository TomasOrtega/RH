import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RealIdemMulOfReal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.CosetOrth

section General

variable {E : Type} [Field E] [NumberField E]

def InHat (I : FractionalIdeal (𝓞 E)⁰ E) (x : FiniteAdeleRing (𝓞 E) E) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Valued.v (x w) ≤ WithZero.exp (-(FractionalIdeal.count E w I))

/- English proof (translation)
Simplify using `only [InHat, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]`.
-/
theorem inHat_one_iff (x : FiniteAdeleRing (𝓞 E) E) : InHat 1 x ↔ ∀ w, Valued.v (x w) ≤ 1 := by
  simp only [InHat, FractionalIdeal.count_one, neg_zero, WithZero.exp_zero]

/- English proof (translation)
Introduce `w` and use `by have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl rw [this, map_zero]; exact zero_le`.
-/
theorem inHat_zero (I : FractionalIdeal (𝓞 E)⁰ E) : InHat I 0 := fun w => by
  have : (0 : FiniteAdeleRing (𝓞 E) E) w = 0 := rfl
  rw [this, map_zero]; exact zero_le

/- English proof (translation)
Introduce `w` and use `by have : (t * x) w = t w * x w := rfl rw [this, map_mul] exact (mul_le_of_le_one_left' ((inHat_one_iff t).1 ht w)).trans (hx w)`.
-/
theorem InHat.mul_left {I : FractionalIdeal (𝓞 E)⁰ E} {t x : FiniteAdeleRing (𝓞 E) E} (ht : InHat 1 t) (hx : InHat I x) :
    InHat I (t * x) := fun w => by
  have : (t * x) w = t w * x w := rfl
  rw [this, map_mul]
  exact (mul_le_of_le_one_left' ((inHat_one_iff t).1 ht w)).trans (hx w)

/- English proof (translation)
Introduce `w` and use `by have : (x + y) w = x w + y w := rfl rw [this] exact (Valued.v.map_add _ _).trans (max_le (hx w) (hy w))`.
-/
theorem InHat.add {I : FractionalIdeal (𝓞 E)⁰ E} {x y : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) (hy : InHat I y) :
    InHat I (x + y) := fun w => by
  have : (x + y) w = x w + y w := rfl
  rw [this]
  exact (Valued.v.map_add _ _).trans (max_le (hx w) (hy w))

/- English proof (translation)
Introduce `w` and use `by have : (-x) w = -x w := rfl rw [this, Valuation.map_neg] exact hx w`.
-/
theorem InHat.neg {I : FractionalIdeal (𝓞 E)⁰ E} {x : FiniteAdeleRing (𝓞 E) E} (hx : InHat I x) : InHat I (-x) := fun w => by
  have : (-x) w = -x w := rfl
  rw [this, Valuation.map_neg]
  exact hx w

end General

variable {D : D7}

abbrev FA (D : D7) : Type := FiniteAdeleRing (𝓞 D.host.E) D.host.E

def fe (D : D7) : AE D →+* FA D := (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fe_apply (x : AE D) : fe D x = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D x) := rfl

def skewId (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E :=
  (𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
    ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)

def HatPt {S T : HSp D} (r : D.host.E) (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) (u : WO S T) : Prop :=
  u.map (infPart D) = 0 ∧ ∀ i j, InHat I (algebraMap D.host.E (FA D) r * fe D (u i j))

def finMat {n : ℕ} (y : Formalism.MainNotions.StandardLatticesGL3.GA D n) : Matrix (Fin n) (Fin n) (FA D) :=
  ((y : GL (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin n) (Fin n) (Formalism.MainNotions.StandardLatticesGL3.AE D)).map (GlobalTheory.BotFormula.toFinE D)

/- English proof (translation)
Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Use `⟨e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s), ?_, ?_⟩` and prove the remaining obligations. Conclude with `(he _).1.symm.trans (by rw [e.apply_symm_apply])`. Establish `: finPart D (e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)) = (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s` using `(he _).2.symm.trans (by rw [e.apply_symm_apply])`. Rewrite using `[fe_apply, this, RingEquiv.apply_symm_apply]`.
-/
theorem exists_fe (s : FA D) : ∃ σ : AE D, infPart D σ = 0 ∧ fe D σ = s := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  refine ⟨e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s), ?_, ?_⟩
  · exact (he _).1.symm.trans (by rw [e.apply_symm_apply])
  · have : finPart D (e.symm (0, (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s)) =
        (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm s := (he _).2.symm.trans (by rw [e.apply_symm_apply])
    rw [fe_apply, this, RingEquiv.apply_symm_apply]

/- English proof (translation)
Establish `key` using `GlobalTheory.Size.ipO_heisO hψ hν.1 hν.2.1 h₁ h₂ v`. Rewrite `key` using `[e₁, e₂]`. Establish `e : GlobalTheory.Ker.ipO ν 𝓕 (α • f₁) (β • f₂) = (α * starRingEnd ℂ β) * ip A B ν 𝓕 f₁ f₂`. Unfold `GlobalTheory.Ker.ipO ip`. Rewrite using `[← integral_const_mul]`.

Use `integral_congr_ae (.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, smul_eq_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `e' : GlobalTheory.Ker.ipO ν 𝓕 f₁ f₂ = ip A B ν 𝓕 f₁ f₂` using `rfl`. Rewrite `key` using `[e, e']`.

Establish `hb : starRingEnd ℂ β * β = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]`. Simplify using the standard rewrite rules. Establish `hne' : α * starRingEnd ℂ β ≠ 1` using `fun h => hne (by`. Use `congrArg (· * β) h` as an intermediate fact.

Simplify using `only [one_mul, mul_assoc, hb, mul_one] at this`. Conclude with `this)`. Establish `: (α * starRingEnd ℂ β - 1) * ip A B ν 𝓕 f₁ f₂ = 0` using `by rw [sub_mul, key, one_mul, sub_self]`. Conclude with `(mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')`.
-/
theorem ip_eq_zero_of_heis_eigen {A B : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ν : Measure (WO A B)} {𝓕 : Set (WO A B)} (hν : IsCovolOne (ratL B A) ν 𝓕) {f₁ f₂ : WO A B → ℂ}
    (h₁ : IsThetaFunO ψ A B f₁) (h₂ : IsThetaFunO ψ A B f₂) (v : WO A B) {α β : ℂ}
    (e₁ : heisO ψ A B v f₁ = α • f₁) (e₂ : heisO ψ A B v f₂ = β • f₂) (hβ : ‖β‖ = 1) (hne : α ≠ β) :
    ip A B ν 𝓕 f₁ f₂ = 0 := by
  have key := GlobalTheory.Size.ipO_heisO hψ hν.1 hν.2.1 h₁ h₂ v
  rw [e₁, e₂] at key
  have e : GlobalTheory.Ker.ipO ν 𝓕 (α • f₁) (β • f₂) = (α * starRingEnd ℂ β) * ip A B ν 𝓕 f₁ f₂ := by
    unfold GlobalTheory.Ker.ipO ip
    rw [← integral_const_mul]
    refine integral_congr_ae (.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  have e' : GlobalTheory.Ker.ipO ν 𝓕 f₁ f₂ = ip A B ν 𝓕 f₁ f₂ := rfl
  rw [e, e'] at key
  have hb : starRingEnd ℂ β * β = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hβ]; simp
  have hne' : α * starRingEnd ℂ β ≠ 1 := fun h => hne (by
    have := congrArg (· * β) h
    simp only [one_mul, mul_assoc, hb, mul_one] at this
    exact this)
  have : (α * starRingEnd ℂ β - 1) * ip A B ν 𝓕 f₁ f₂ = 0 := by rw [sub_mul, key, one_mul, sub_self]
  exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')

end GlobalTheory.CosetOrth
