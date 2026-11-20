import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPeriodSq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBinaryEqAdicCompletion
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostCmData

open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

/- English proof (translation)
The claim follows from `Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData D.R D.host).cmUnram.2.2 P hP refine ⟨θ, ?_⟩ have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t := RingOfIntegers.ext e1. …`.
-/
theorem unram (D : D7) : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E) :=
  Formalism.L2.Pj.unramBridge_holds D.host.E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := (GlobalTheory.Mem.host_cmData D.R D.host).cmUnram.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj D.host.E : D.host.E ≃+* D.host.E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[IsCMField.complexEmbedding_complexConj]`. Conclude with `(Formalism.HC.HostAx.conjE_apply _ _ _).symm`.
-/
theorem cc_eq_conj (D : D7) (x : D.host.E) : IsCMField.complexConj D.host.E x = D.host.conj x := by
  apply D.host.φ₀.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (Formalism.HC.HostAx.conjE_apply _ _ _).symm

end GlobalTheory.NormRatio

namespace GlobalTheory.NormRatio

open scoped Pointwise nonZeroDivisors

/- English proof (translation)
Rewrite using `[← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]`. Use `congr 2`. Use `RingHom.ext fun x => RingOfIntegers.ext ?_` and prove the remaining obligations. Use `show ((Formalism.L2.Pj.barE D x : 𝓞 D.host.E) : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)`. Rewrite using `[Formalism.L2.Pj.barE_eq_conj]`.

Conclude with `(Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul D.host.conj x).symm`.
-/
theorem map_mul_bar (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
      (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map
        ((Formalism.L2.Pj.hostOf D hU).bar : 𝓞 D.host.E →+* 𝓞 D.host.E) =
    Ideal.span {((Ideal.absNorm cc : ℕ) : 𝓞 D.host.E)} := by
  rw [← Formalism.MainNotions.UnusedSlot33.normK_holds D cc hc, Ideal.pointwise_smul_def]
  congr 2
  refine RingHom.ext fun x => RingOfIntegers.ext ?_
  show ((Formalism.L2.Pj.barE D x : 𝓞 D.host.E) : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
  rw [Formalism.L2.Pj.barE_eq_conj]
  exact (Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul D.host.conj x).symm

/- English proof (translation)
Introduce `h0` and use `h (Ideal.absNorm_eq_zero_iff.1 h0)`.
-/
theorem absNorm_ne_zero {K : Type*} [Field K] [NumberField K] {I : Ideal (𝓞 K)} (h : I ≠ ⊥) :
    (Ideal.absNorm I : ℕ) ≠ 0 := fun h0 => h (Ideal.absNorm_eq_zero_iff.1 h0)

/- English proof (translation)
Introduce `h0`. Establish `h` using `map_mul_bar D hU cc hc`. Rewrite `h` using `[h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot]`. Conclude with `absNorm_ne_zero hc (by exact_mod_cast h)`.
-/
theorem map_ne_bot (D : D7) (hU : Algebra.Unramified (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E))
    (cc : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) :
    Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ := by
  intro h0
  have h := map_mul_bar D hU cc hc
  rw [h0, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h
  exact absNorm_ne_zero hc (by exact_mod_cast h)

/- English proof (translation)
Establish `hU` using `unram D`. Use `set H := Formalism.L2.Pj.hostOf D hU`. Use `set F := maximalRealSubfield D.host.E`. Establish `hn0 : ((Ideal.absNorm c0 : ℕ) : F) ≠ 0` using `by exact_mod_cast absNorm_ne_zero h0`. Establish `hn : ((Ideal.absNorm cc : ℕ) : F) ≠ 0` using `by exact_mod_cast absNorm_ne_zero hc`.

Use `set x : F := ((Ideal.absNorm cc : ℕ) : F) / ((Ideal.absNorm c0 : ℕ) : F) with hxdef`. Establish `hx : x ≠ 0` using `div_ne_zero hn hn0`. Establish `hid : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x : D.host.E)) * ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0 * (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host. …`. Rewrite using `[map_mul_bar D hU c0 h0, map_mul_bar D hU cc hc, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]`. Use `congr 1`.

Establish `hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast absNorm_ne_zero h0`. Rewrite using `[hxdef]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hloc` using `GlobalTheory.local_norm_of_ideal_norm D.host.E H x hx ⟨_, _, map_ne_bot D hU c0 h0, map_ne_bot D hU cc hc, hid⟩`.

Establish `hreal : ∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ (-(H.d : F)) * b ^ 2`. Introduce `σ`. Establish `hpos : 0 ≤ σ x`. Rewrite using `[hxdef, map_div₀, map_natCast, map_natCast]`. Check the signs of the components of the expression.

Conclude with `⟨Real.sqrt (σ x), 0, by rw [Real.sq_sqrt hpos]; ring⟩`. Establish `hd : (-(H.d : F)) ≠ 0`. Establish `: (H.d : F) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Conclude with `neg_ne_zero.2 this`. Take `⟨a, b, hab⟩` from `GlobalTheory.QNorm.hasseNormSt F (-(H.d : F)) x hd hx hreal hloc`.

Use `⟨(a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD, ?_⟩` and prove the remaining obligations. Establish `ha : D.host.conj (a : D.host.E) = a`. Rewrite using `[← cc_eq_conj]`. Conclude with `(IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2`. Establish `hb : D.host.conj (b : D.host.E) = b`.

Rewrite using `[← cc_eq_conj]`. Conclude with `(IsCMField.complexConj_eq_self_iff D.host.E _).2 b.2`. Establish `hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD` using `Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D`. Establish `hs2` using `D.host.sqrtMinusD_sq`. Establish `hxE : (x : D.host.E) = (a : D.host.E) ^ 2 + (D.host.d : D.host.E) * (b : D.host.E) ^ 2`.

Use `congrArg (fun t : F => (t : D.host.E)) hab` as an intermediate fact. Move the coercions through the operations in `at this`. Rewrite using `[this]`. Establish `hHd : ((H.d : ℕ) : D.host.E) = (D.host.d : D.host.E)` using `rfl`. Rewrite using `[hHd]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0` using `by exact_mod_cast absNorm_ne_zero h0`. Establish `hxE' : (x : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) / ((Ideal.absNorm c0 : ℕ) : D.host.E)`. Rewrite using `[hxdef]`. Use `push_cast`.

Apply the tactic sequence `try rfl`. Rewrite using `[map_add, map_mul, ha, hb, hs]`. Establish `key : ((a : D.host.E) + b * D.host.sqrtMinusD) * (a + b * -D.host.sqrtMinusD) = x`. Rewrite using `[hxE]`. Take the linear combination `(-(b : D.host.E) ^ 2) * hs2`.

Rewrite using `[key, hxE']`. Clear the denominators using the available nonvanishing facts.
-/
theorem exists_mul_conj (D : D7) (cc c0 : Ideal (𝓞 D.host.K)) (hc : cc ≠ ⊥) (h0 : c0 ≠ ⊥) :
    ∃ r : D.host.E, r * D.host.conj r * ((Ideal.absNorm c0 : ℕ) : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) := by
  have hU := unram D
  set H := Formalism.L2.Pj.hostOf D hU
  set F := maximalRealSubfield D.host.E
  have hn0 : ((Ideal.absNorm c0 : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hn : ((Ideal.absNorm cc : ℕ) : F) ≠ 0 := by exact_mod_cast absNorm_ne_zero hc
  set x : F := ((Ideal.absNorm cc : ℕ) : F) / ((Ideal.absNorm c0 : ℕ) : F) with hxdef
  have hx : x ≠ 0 := div_ne_zero hn hn0
  have hid : FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ ((x : D.host.E)) *
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0 *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) c0).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) =
      ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc *
        (Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc).map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
    rw [map_mul_bar D hU c0 h0, map_mul_bar D hU cc hc, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton]
    congr 1
    have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
    rw [hxdef]
    push_cast
    field_simp
  have hloc := GlobalTheory.local_norm_of_ideal_norm D.host.E H x hx
    ⟨_, _, map_ne_bot D hU c0 h0, map_ne_bot D hU cc hc, hid⟩
  have hreal : ∀ σ : F →+* ℝ, ∃ a b : ℝ, σ x = a ^ 2 - σ (-(H.d : F)) * b ^ 2 := by
    intro σ
    have hpos : 0 ≤ σ x := by
      rw [hxdef, map_div₀, map_natCast, map_natCast]; positivity
    exact ⟨Real.sqrt (σ x), 0, by rw [Real.sq_sqrt hpos]; ring⟩
  have hd : (-(H.d : F)) ≠ 0 := by
    have : (H.d : F) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
    exact neg_ne_zero.2 this
  obtain ⟨a, b, hab⟩ := GlobalTheory.QNorm.hasseNormSt F (-(H.d : F)) x hd hx hreal hloc
  refine ⟨(a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD, ?_⟩
  have ha : D.host.conj (a : D.host.E) = a := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 a.2
  have hb : D.host.conj (b : D.host.E) = b := by
    rw [← cc_eq_conj]; exact (IsCMField.complexConj_eq_self_iff D.host.E _).2 b.2
  have hs : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.MainNotions.UnusedSlot33.PolarisationData.conj_b D
  have hs2 := D.host.sqrtMinusD_sq
  have hxE : (x : D.host.E) = (a : D.host.E) ^ 2 + (D.host.d : D.host.E) * (b : D.host.E) ^ 2 := by
    have := congrArg (fun t : F => (t : D.host.E)) hab
    push_cast at this
    rw [this]
    have hHd : ((H.d : ℕ) : D.host.E) = (D.host.d : D.host.E) := rfl
    rw [hHd]; ring
  have hn0' : ((Ideal.absNorm c0 : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast absNorm_ne_zero h0
  have hxE' : (x : D.host.E) = ((Ideal.absNorm cc : ℕ) : D.host.E) / ((Ideal.absNorm c0 : ℕ) : D.host.E) := by
    rw [hxdef]
    push_cast
    try rfl
  rw [map_add, map_mul, ha, hb, hs]
  have key : ((a : D.host.E) + b * D.host.sqrtMinusD) * (a + b * -D.host.sqrtMinusD) = x := by
    rw [hxE]; linear_combination (-(b : D.host.E) ^ 2) * hs2
  rw [key, hxE']
  field_simp

end GlobalTheory.NormRatio

/- English proof (translation)
Introduce `D cc hcc` and use `GlobalTheory.NormRatio.exists_mul_conj D cc D.host.ccK hcc.1 D.host.ccK_ne_bot`.
-/
theorem GlobalTheory.NormRatio.exists_scale : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)), Formalism.MainNotions.TaylorLogMetric.IsCurveIdeal D cc → ∃ r : D.host.E, IsScale D cc r :=
  fun D cc hcc => GlobalTheory.NormRatio.exists_mul_conj D cc D.host.ccK hcc.1 D.host.ccK_ne_bot
