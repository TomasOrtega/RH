import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIndicatorProjFinSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemClosureSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

section Helpers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

/- English proof (translation)
Use function extensionality and compare the values at `y`. Establish `hs : MeasurableSet ((fun x => y⁻¹ * x) ⁻¹' (K : Set G))` using `(ho.preimage (continuous_const.mul continuous_id)).measurableSet`. Establish `e : (fun x => f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y)) = ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)).indicator (fun _ => f y)`. Use function extensionality and compare the values at `x`. Rewrite using `[GlobalTheory.InvBilinTest.cosetInd_apply]`.

Distinguish the cases in `hx : y⁻¹ * x ∈ K`. Establish `h1 : x⁻¹ * y * 1⁻¹ ∈ K` using `by simpa using K.inv_mem hx`. Rewrite using `[if_pos h1, Set.indicator_of_mem (show x ∈ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_one]`. Use `hf _ hx y` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel_left]`. Then use the resulting hypothesis.

Establish `h1 : ¬ x⁻¹ * y * 1⁻¹ ∈ K` using `fun h => hx (by simpa using K.inv_mem h)`. Rewrite using `[if_neg h1, Set.indicator_of_notMem (show x ∉ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_zero]`. Use `show ∫ x, f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y) ∂μ = _`. Rewrite using `[e, integral_indicator_const _ hs]`. Simplify using `only [Measure.real, measure_preimage_mul, Complex.real_smul]`.
-/
theorem conv_cosetInd_eq_smul (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) :
    conv μ f (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 = fun y => (μ.real K : ℂ) * f y := by
  classical
  funext y
  have hs : MeasurableSet ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)) :=
    (ho.preimage (continuous_const.mul continuous_id)).measurableSet
  have e : (fun x => f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y)) =
      ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)).indicator (fun _ => f y) := by
    funext x
    rw [GlobalTheory.InvBilinTest.cosetInd_apply]
    by_cases hx : y⁻¹ * x ∈ K
    · have h1 : x⁻¹ * y * 1⁻¹ ∈ K := by simpa using K.inv_mem hx
      rw [if_pos h1, Set.indicator_of_mem (show x ∈ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_one]
      have := hf _ hx y
      rwa [mul_inv_cancel_left] at this
    · have h1 : ¬ x⁻¹ * y * 1⁻¹ ∈ K := fun h => hx (by simpa using K.inv_mem h)
      rw [if_neg h1, Set.indicator_of_notMem (show x ∉ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_zero]
  show ∫ x, f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y) ∂μ = _
  rw [e, integral_indicator_const _ hs]
  simp only [Measure.real, measure_preimage_mul, Complex.real_smul]

/- English proof (translation)
Introduce `v l`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Simplify `(hA v l).1.const_mul c` using `only [mul_assoc]`. Rewrite using `[LinearMap.smul_apply, map_smul, smul_eq_mul, (hA v l).2, ← integral_const_mul]`. Simplify using `only [mul_assoc]`.
-/
theorem isIntegralOp_const_mul {W : Type} [AddCommGroup W] [Module ℂ W] {μ : Measure G}
    {σ : Representation ℂ G W} {f : G → ℂ} {A : W →ₗ[ℂ] W} (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A) (c : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun g => c * f g) (c • A) := by
  intro v l
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using (hA v l).1.const_mul c
  · rw [LinearMap.smul_apply, map_smul, smul_eq_mul, (hA v l).2, ← integral_const_mul]
    simp only [mul_assoc]

end Helpers

open Classical in

/- English proof (translation)
Introduce `D V lam S M T U μa μf μ _ _ fa ff hT ν hν H _ _ _ π hπ W _ _ σ hirr hadm hcopy c hc`. Take `⟨-, -, -, -, hres, harch, hfin⟩` from `hT`. Establish `hff` using `hfin.isFinFamily`. Use `haveI : ν.IsHaarMeasure := hν.1`. Take `⟨Tm, hTm, hinj, hdense⟩` from `hcopy`.

Establish `hTm' : Tm ∈ homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) π ⊤` using `hTm`. Take `⟨A, hA, hAtr⟩` from `hc`. Establish `hσ : GlobalTheory.PRep.IsSmooth σ` using `hadm.1`. Establish `hX` using `GlobalTheory.TrOpTensor.opTensor D V S M μa μf μ hres ν hν fa ff harch.mem hff W σ hσ H π hπ.unitary Tm hTm A hA`. Take `⟨hlc, hcs⟩` from `GlobalTheory.FinTrace.finFn_mem_SB V hff`.

Take `⟨U₀, hU₀, hbi⟩` from `GlobalTheory.Orb.exists_biinvariant (f := finFn V ff) ⟨hlc, hcs⟩`. Take `⟨K₀, hK₀o, hK₀c⟩` from `GlobalTheory.CuspDec.exists_compact_open V`. Take `⟨K, hKdef⟩ : ∃ K : Subgroup (GfC V), K = U₀ ⊓ K₀` from `⟨_, rfl⟩`. Establish `hKo : IsOpen (K : Set (GfC V))` using `hKdef ▸ hU₀.inter hK₀o`. Establish `hKc : IsCompact (K : Set (GfC V))` using `hKdef ▸ hK₀c.inter_left (U₀.isClosed_of_isOpen hU₀)`.

Establish `hKU : ∀ k ∈ K, k ∈ U₀` using `fun k hk => (Subgroup.mem_inf.1 (hKdef ▸ hk)).1`. Establish `hZ : FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K)` using `hadm.2 K hKo hKc`. Establish `hrange : LinearMap.range A ≤ GlobalTheory.PRep.fixed σ K`. Introduce and unpack `_ ⟨w, rfl⟩`. Conclude with `GlobalTheory.IwahoriRel.isIntegralOp_mem_fixed hA (fun k hk g => (hbi k (hKU k hk) g).1) w`.

Take `⟨e, he⟩ : ∃ e, e = GlobalTheory.InvBilinTest.cosetInd K hKo hKc 1` from `⟨_, rfl⟩`. Take `⟨P, hPdef⟩ : ∃ P, P = smoothOp σ ν e.1` from `⟨_, rfl⟩`. Establish `hP : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ e.1 P`. Introduce `v l`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Establish `h` using `GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.smoothOp_integrand e.2.1 e.2.2 v).1 (hσ.smoothOp_integrand e.2.1 e.2.2 v).2 l l.map_zero`. Simplify `h` using `only [map_smul, smul_eq_mul]`. Rewrite using `[hPdef, hσ.map_smoothOp e.2.1 e.2.2 l v]`. Simplify using `only [smul_eq_mul]`. Establish `hconv` using `(GlobalTheory.OpConv.isIntegralOp_conv_and_translate _ ν W σ hσ _ ⟨hlc, hcs⟩ e.1 e.2 A P hA hP).1`.

Rewrite `hconv` using `[he, conv_cosetInd_eq_smul ν K hKo hKc _ (fun k hk g => (hbi k (hKU k hk) g).2)]`. Establish `hAP : A ∘ₗ P = (ν.real K : ℂ) • A` using `hconv.unique (isIntegralOp_const_mul hA _)`. Establish `hvol : (ν.real K : ℂ) ≠ 0`. Establish `h1 : ν K ≠ 0` using `(hKo.measure_pos ν ⟨1, K.one_mem⟩).ne'`. Establish `h2 : ν.real K ≠ 0` using `ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_ne_top⟩`.

Conclude with `h2` after adjusting the coercions. Establish `hδ : ∀ τ, IsIrrUnitary (dsRep M τ)` using `isIrrUnitary_dsRep M`. Establish `hinner : ∀ w w' y y', inner ℂ (Tm w' y') (Tm w y) = bePi (Tm w) (Tm w') * ∏ τ, inner ℂ (y' τ) (y τ)` using `fun w w' y y' => inner_eq_bePi hδ hπ.unitary (hTm'.1 w) (hTm'.1 w') y y'`. Establish `hcond : ∀ w, (∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm w) (Tm z) = 0) → A w = 0`. Introduce `w hw`.

Establish `hPw : P w ∈ GlobalTheory.PRep.fixed σ K` using `hPdef ▸ hσ.smoothOp_mem_fixed (μ := ν) e.2.1 e.2.2 (fun k hk g => by`. Simplify using `only [he, GlobalTheory.InvBilinTest.cosetInd_apply, inv_one, mul_one, K.mul_mem_cancel_left hk]) w`. Establish `hβP : ∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm (P w)) (Tm z) = (ν.real K : ℂ) * bePi (Tm w) (Tm z)`. Introduce `z hz`. Set `l : W →ₗ[ℂ] ℂ` to `{ toFun := fun v => bePi (Tm v) (Tm z) map_add' := fun a b => by simp [bePi, inner_add_right] map_smul' := fun a b => by simp [bePi, inner_smul_right] }`.

Establish `hl : ∀ g ∈ K, l (σ g w) = l w` using `fun g hg => by`. Establish `hz' : σ g z = z` using `mem_fixed.1 hz g hg`. Use `show bePi (Tm (σ g w)) (Tm z) = bePi (Tm w) (Tm z)`. Simplify using `only [bePi]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[(mem_homTensorPi.1 hTm').2.1, (mem_homTensorPi.1 hTm').2.1]`. Both sides reduce to the same expression. Use `_ = _ := inner_map_map hπ.unitary _ _ _`. Establish `h1` using `(hP w l).2`. Establish `h2 : ∫ g, e.1 g * l (σ g w) ∂ν = ∫ g, (if g ∈ K then l w else 0) ∂ν`.

Use `integral_congr_ae (.of_forall fun g => ?_)` and prove the remaining obligations. Distinguish the cases in `hg : g ∈ K`. Simplify using `[he, GlobalTheory.InvBilinTest.cosetInd_apply, hg, hl g hg]`. Simplify using `[he, GlobalTheory.InvBilinTest.cosetInd_apply, hg]`. Rewrite `h1` using `[h2, GlobalTheory.InvBilinTest.integral_ite K hKo]`.

Conclude with `h1`. Establish `h0 : P w = 0`. Assume the negation of the conclusion as `hne`. Establish `hT0 : Tm (P w) ≠ 0` using `fun h => hne (hinj (h.trans (map_zero Tm).symm))`. Establish `hpos` using `bePi_self_pos hδ hπ.unitary (hTm'.1 (P w)) hT0`.

Rewrite `hpos` using `[hβP (P w) hPw, hw (P w) hPw, mul_zero]`. Conclude with `lt_irrefl _ hpos`. Establish `h3` using `LinearMap.congr_fun hAP w`. Rewrite `h3` using `[LinearMap.comp_apply, h0, map_zero, LinearMap.smul_apply]`. Conclude with `(smul_eq_zero.1 h3.symm).resolve_left hvol`.

Use `haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1`. Establish `key` using `GlobalTheory.TensorTrace.hasTrace_finiteRank_tensor D.what₂.Tau M.H H W Tm (fun w w' => bePi (Tm w) (Tm w')) hinner hinj hdense A c hAtr (GlobalTheory.PRep.fixed σ K) hZ hrange hcond (fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ))) (fun _ => 1) (fun τ => (harch …`. Simplify using `using key`.
-/
theorem hasTrace_repOp_of_isCopyFinDS : ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ ν, IsFinMeas V μf ν → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), σ.IsIrreducible → IsAdmissible σ → IsCopyFinDS σ M π ⊤ → ∀ c, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V ff) c → HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c := by
  intro D V lam S M T U μa μf μ _ _ fa ff hT ν hν H _ _ _ π hπ W _ _ σ hirr hadm hcopy c hc
  obtain ⟨-, -, -, -, hres, harch, hfin⟩ := hT
  have hff := hfin.isFinFamily
  haveI : ν.IsHaarMeasure := hν.1
  obtain ⟨Tm, hTm, hinj, hdense⟩ := hcopy
  have hTm' : Tm ∈ homTensorPi (GfC V).subtype (fun τ => embW V (placeOf D τ)) σ (dsRep M) π ⊤ := hTm
  obtain ⟨A, hA, hAtr⟩ := hc
  have hσ : GlobalTheory.PRep.IsSmooth σ := hadm.1
  have hX := GlobalTheory.TrOpTensor.opTensor D V S M μa μf μ hres ν hν fa ff harch.mem hff W σ hσ H π hπ.unitary Tm hTm A hA
  obtain ⟨hlc, hcs⟩ := GlobalTheory.FinTrace.finFn_mem_SB V hff
  obtain ⟨U₀, hU₀, hbi⟩ := GlobalTheory.Orb.exists_biinvariant (f := finFn V ff) ⟨hlc, hcs⟩
  obtain ⟨K₀, hK₀o, hK₀c⟩ := GlobalTheory.CuspDec.exists_compact_open V
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup (GfC V), K = U₀ ⊓ K₀ := ⟨_, rfl⟩
  have hKo : IsOpen (K : Set (GfC V)) := hKdef ▸ hU₀.inter hK₀o
  have hKc : IsCompact (K : Set (GfC V)) := hKdef ▸ hK₀c.inter_left (U₀.isClosed_of_isOpen hU₀)
  have hKU : ∀ k ∈ K, k ∈ U₀ := fun k hk => (Subgroup.mem_inf.1 (hKdef ▸ hk)).1
  have hZ : FiniteDimensional ℂ (GlobalTheory.PRep.fixed σ K) := hadm.2 K hKo hKc
  have hrange : LinearMap.range A ≤ GlobalTheory.PRep.fixed σ K := by
    rintro _ ⟨w, rfl⟩
    exact GlobalTheory.IwahoriRel.isIntegralOp_mem_fixed hA (fun k hk g => (hbi k (hKU k hk) g).1) w

  obtain ⟨e, he⟩ : ∃ e, e = GlobalTheory.InvBilinTest.cosetInd K hKo hKc 1 := ⟨_, rfl⟩
  obtain ⟨P, hPdef⟩ : ∃ P, P = smoothOp σ ν e.1 := ⟨_, rfl⟩
  have hP : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ e.1 P := by
    intro v l
    refine ⟨?_, ?_⟩
    · have h := GlobalTheory.OpTrace.integrable_map (μ := ν) (hσ.smoothOp_integrand e.2.1 e.2.2 v).1
        (hσ.smoothOp_integrand e.2.1 e.2.2 v).2 l l.map_zero
      simpa only [map_smul, smul_eq_mul] using h
    · rw [hPdef, hσ.map_smoothOp e.2.1 e.2.2 l v]
      simp only [smul_eq_mul]
  have hconv := (GlobalTheory.OpConv.isIntegralOp_conv_and_translate _ ν W σ hσ _ ⟨hlc, hcs⟩ e.1 e.2 A P hA hP).1
  rw [he, conv_cosetInd_eq_smul ν K hKo hKc _ (fun k hk g => (hbi k (hKU k hk) g).2)] at hconv
  have hAP : A ∘ₗ P = (ν.real K : ℂ) • A := hconv.unique (isIntegralOp_const_mul hA _)
  have hvol : (ν.real K : ℂ) ≠ 0 := by
    have h1 : ν K ≠ 0 := (hKo.measure_pos ν ⟨1, K.one_mem⟩).ne'
    have h2 : ν.real K ≠ 0 := ENNReal.toReal_ne_zero.2 ⟨h1, hKc.measure_ne_top⟩
    exact_mod_cast h2
  have hδ : ∀ τ, IsIrrUnitary (dsRep M τ) := isIrrUnitary_dsRep M
  have hinner : ∀ w w' y y', inner ℂ (Tm w' y') (Tm w y) = bePi (Tm w) (Tm w') * ∏ τ, inner ℂ (y' τ) (y τ) :=
    fun w w' y y' => inner_eq_bePi hδ hπ.unitary (hTm'.1 w) (hTm'.1 w') y y'
  have hcond : ∀ w, (∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm w) (Tm z) = 0) → A w = 0 := by
    intro w hw
    have hPw : P w ∈ GlobalTheory.PRep.fixed σ K := hPdef ▸ hσ.smoothOp_mem_fixed (μ := ν) e.2.1 e.2.2 (fun k hk g => by
      simp only [he, GlobalTheory.InvBilinTest.cosetInd_apply, inv_one, mul_one, K.mul_mem_cancel_left hk]) w
    have hβP : ∀ z ∈ GlobalTheory.PRep.fixed σ K, bePi (Tm (P w)) (Tm z) = (ν.real K : ℂ) * bePi (Tm w) (Tm z) := by
      intro z hz
      let l : W →ₗ[ℂ] ℂ :=
        { toFun := fun v => bePi (Tm v) (Tm z)
          map_add' := fun a b => by simp [bePi, inner_add_right]
          map_smul' := fun a b => by simp [bePi, inner_smul_right] }
      have hl : ∀ g ∈ K, l (σ g w) = l w := fun g hg => by
        have hz' : σ g z = z := mem_fixed.1 hz g hg
        show bePi (Tm (σ g w)) (Tm z) = bePi (Tm w) (Tm z)
        simp only [bePi]
        calc inner ℂ (Tm z fun i => unitVec (M.H i)) (Tm (σ g w) fun i => unitVec (M.H i))
            = inner ℂ (Tm (σ g z) fun i => unitVec (M.H i)) (Tm (σ g w) fun i => unitVec (M.H i)) := by rw [hz']
          _ = inner ℂ (π g (Tm z fun i => unitVec (M.H i))) (π g (Tm w fun i => unitVec (M.H i))) := by
            rw [(mem_homTensorPi.1 hTm').2.1, (mem_homTensorPi.1 hTm').2.1]; rfl
          _ = _ := inner_map_map hπ.unitary _ _ _
      have h1 := (hP w l).2
      have h2 : ∫ g, e.1 g * l (σ g w) ∂ν = ∫ g, (if g ∈ K then l w else 0) ∂ν := by
        refine integral_congr_ae (.of_forall fun g => ?_)
        by_cases hg : g ∈ K
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg, hl g hg]
        · simp [he, GlobalTheory.InvBilinTest.cosetInd_apply, hg]
      rw [h2, GlobalTheory.InvBilinTest.integral_ite K hKo] at h1
      exact h1
    have h0 : P w = 0 := by
      by_contra hne
      have hT0 : Tm (P w) ≠ 0 := fun h => hne (hinj (h.trans (map_zero Tm).symm))
      have hpos := bePi_self_pos hδ hπ.unitary (hTm'.1 (P w)) hT0
      rw [hβP (P w) hPw, hw (P w) hPw, mul_zero] at hpos
      exact lt_irrefl _ hpos
    have h3 := LinearMap.congr_fun hAP w
    rw [LinearMap.comp_apply, h0, map_zero, LinearMap.smul_apply] at h3
    exact (smul_eq_zero.1 h3.symm).resolve_left hvol
  haveI : ∀ τ, CompleteSpace (M.H τ) := fun τ => (M.ds τ).1
  have key := GlobalTheory.TensorTrace.hasTrace_finiteRank_tensor D.what₂.Tau M.H H W Tm (fun w w' => bePi (Tm w) (Tm w')) hinner hinj hdense A c hAtr
    (GlobalTheory.PRep.fixed σ K) hZ hrange hcond (fun τ => repOp (dsRep M τ) (μa (placeOf D τ)) (fa (placeOf D τ)))
    (fun _ => 1) (fun τ => (harch τ).trace_self) (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) hX
  simpa using key

end GlobalTheory.AutMult
