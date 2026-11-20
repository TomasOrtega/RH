import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsComponentFiniteDimensionalAndSpanned
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormPairQuotientHorizontalGeneratorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReadingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HorizontalGeneratorZpowMulCuspFormMemSpan
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndicatorMemSSAndDomSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuliLawsOfPrincipalLevelFieldOfDefinition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrincipalCongruenceBackTriangularFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.RealPlaceEmbeddings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GGConn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStatementPfLA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientDomain

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CentreCusp

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlatCore

section Zeros

open Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

/- English proof (translation)
Set `e : Frame X.Ψ r ≃L[ℂ] (Fin (Module.finrank ℂ (Frame X.Ψ r)) → ℂ)` to `(Module.finBasis ℂ (Frame X.Ψ r)).equivFun.toContinuousLinearEquiv`. Establish `hU : IsOpen (e.symm ⁻¹' X.dom)` using `(FourierCoefficientDomain.isOpen_dom X).preimage e.symm.continuous`. Establish `hd : DifferentiableOn ℂ (F ∘ e.symm) (e.symm ⁻¹' X.dom)` using `hF.comp e.symm.differentiableOn (fun _ h => h)`. Establish `ha` using `ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU hd`. Introduce `z hz`.

Establish `hF' : F = (F ∘ e.symm) ∘ e` using `by ext y; simp`. Rewrite using `[hF']`. Conclude with `(ha (e z) (by simpa using hz)).comp (e.toContinuousLinearMap.analyticAt z)`.
-/
theorem analyticOnNhd_frames (X : Data E r) {F : Frame X.Ψ r → ℂ} (hF : DifferentiableOn ℂ F X.dom) :
    AnalyticOnNhd ℂ F X.dom := by
  let e : Frame X.Ψ r ≃L[ℂ] (Fin (Module.finrank ℂ (Frame X.Ψ r)) → ℂ) :=
    (Module.finBasis ℂ (Frame X.Ψ r)).equivFun.toContinuousLinearEquiv
  have hU : IsOpen (e.symm ⁻¹' X.dom) := (FourierCoefficientDomain.isOpen_dom X).preimage e.symm.continuous
  have hd : DifferentiableOn ℂ (F ∘ e.symm) (e.symm ⁻¹' X.dom) :=
    hF.comp e.symm.differentiableOn (fun _ h => h)
  have ha := ReciprocityTheory.AnForm.Osgood.osgood _ _ _ hU hd
  intro z hz
  have hF' : F = (F ∘ e.symm) ∘ e := by ext y; simp
  rw [hF']
  exact (ha (e z) (by simpa using hz)).comp (e.toContinuousLinearMap.analyticAt z)

/- English proof (translation)
Establish `hA` using `analyticOnNhd_frames X hF`. Establish `hc : IsPreconnected X.dom` using `(ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) r X).isPreconnected`. Establish `hO` using `FourierCoefficientDomain.isOpen_dom X`. Assume the negation of the conclusion as `hU`. Take `⟨y, hy⟩` from `Set.nonempty_iff_ne_empty.2 hU`.

Establish `hyc : y ∈ closure X.dom` using `closure_mono (fun x hx => hx.1) (interior_subset hy)`. Take `⟨z, hzV, hzd⟩` from `mem_closure_iff_nhds.1 hyc _ (isOpen_interior.mem_nhds hy)`. Establish `hev : F =ᶠ[𝓝 z] 0` using `by filter_upwards [isOpen_interior.mem_nhds hzV, hO.mem_nhds hzd] with w hwV hwd`. Establish `hcont : ContinuousAt F w` using `(hF.differentiableAt (hO.mem_nhds hwd)).continuousAt`. Assume the negation of the conclusion as `hw0`.

Establish `hfr` using `mem_closure_iff_frequently.1 (interior_subset hwV)`. Take `⟨v, hv0, hvZ⟩` from `((hcont.eventually_ne hw0).and_frequently hfr).exists`. Conclude with `hv0 hvZ.2`. Take `⟨x, hx, hx0⟩` from `hne`. Conclude with `hx0 (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzd hev hx)`.
-/
theorem interior_closure_zeros (X : Data E r) {F : Frame X.Ψ r → ℂ} (hF : DifferentiableOn ℂ F X.dom)
    (hne : ∃ x ∈ X.dom, F x ≠ 0) : interior (closure {x | x ∈ X.dom ∧ F x = 0}) = ∅ := by
  have hA := analyticOnNhd_frames X hF
  have hc : IsPreconnected X.dom := (ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.flag_domain_frames_connected (E := E) r X).isPreconnected
  have hO := FourierCoefficientDomain.isOpen_dom X
  by_contra hU
  obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.2 hU
  have hyc : y ∈ closure X.dom := closure_mono (fun x hx => hx.1) (interior_subset hy)
  obtain ⟨z, hzV, hzd⟩ := mem_closure_iff_nhds.1 hyc _ (isOpen_interior.mem_nhds hy)
  have hev : F =ᶠ[𝓝 z] 0 := by
    filter_upwards [isOpen_interior.mem_nhds hzV, hO.mem_nhds hzd] with w hwV hwd
    have hcont : ContinuousAt F w := (hF.differentiableAt (hO.mem_nhds hwd)).continuousAt
    by_contra hw0
    have hfr := mem_closure_iff_frequently.1 (interior_subset hwV)
    obtain ⟨v, hv0, hvZ⟩ := ((hcont.eventually_ne hw0).and_frequently hfr).exists
    exact hv0 hvZ.2
  obtain ⟨x, hx, hx0⟩ := hne
  exact hx0 (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc hzd hev hx)

end Zeros

section Cancel

open Filter Topology

/- English proof (translation)
Use `haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)`. Establish `hrad : b ∉ (⊥ : Ideal R).jacobson`. Rewrite using `[← Ideal.radical_eq_jacobson]`. Introduce `h`. Take `⟨n, hn⟩` from `Ideal.mem_radical_iff.1 h`.

Conclude with `hb ⟨n, by simpa using hn⟩`. Rewrite `hrad` using `[Ideal.jacobson, Submodule.mem_sInf]`. Use `push_neg at hrad`. Take `⟨m, ⟨-, hm⟩, hbm⟩` from `hrad`. Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`.

Use `haveI : Algebra.FiniteType K (R ⧸ m) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)`. Use `haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)`. Use `haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Set `ψ : (R ⧸ m) →ₐ[K] ℂ` to `IsAlgClosed.lift`.

Use `⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a`. Rewrite using `[AlgHom.commutes, AlgHom.commutes]`. Both sides reduce to the same expression. Use `show ψ (Ideal.Quotient.mk m b) ≠ 0`.

Rewrite using `[map_ne_zero_iff ψ ψ.toRingHom.injective]`. Conclude with `fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)`.
-/
theorem exists_ringHom_ne_zero_of_not_isNilpotent' {K R : Type} [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (σ : K →+* ℂ) {b : R} (hb : ¬ IsNilpotent b) :
    ∃ φ : R →+* ℂ, φ.comp (algebraMap K R) = σ ∧ φ b ≠ 0 := by
  haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hrad : b ∉ (⊥ : Ideal R).jacobson := by
    rw [← Ideal.radical_eq_jacobson]
    intro h
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.1 h
    exact hb ⟨n, by simpa using hn⟩
  rw [Ideal.jacobson, Submodule.mem_sInf] at hrad
  push_neg at hrad
  obtain ⟨m, ⟨-, hm⟩, hbm⟩ := hrad
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)
  letI : Algebra K ℂ := σ.toAlgebra
  let ψ : (R ⧸ m) →ₐ[K] ℂ := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩
  · ext a
    show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · show ψ (Ideal.Quotient.mk m b) ≠ 0
    rw [map_ne_zero_iff ψ ψ.toRingHom.injective]
    exact fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)

/- English proof (translation)
Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem P h => exact (h k).1.1.1`. Consider the case `zero => exact differentiableOn_const 0`. Consider the case `add P Q _ _ hP hQ => exact hP.add hQ`. Consider the case `smul a P _ hP => exact hP.const_smul a`.
-/
theorem differentiableOn_of_mem_holSub' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {C : Type}
    {X : C → Data E r} {la : ∀ k, Wt (X k).Ψ r} {P : FDSec X} (hP : P ∈ holSub X la) (k : C) :
    DifferentiableOn ℂ (P k) (X k).dom := by
  induction hP using Submodule.span_induction with
  | mem P h => exact (h k).1.1.1
  | zero => exact differentiableOn_const 0
  | add P Q _ _ hP hQ => exact hP.add hQ
  | smul a P _ hP => exact hP.const_smul a

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {G : WTZ E} {f : Rul Xo c}

/- English proof (translation)
Establish `hG : GenFrEx Xo c` using `(GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1`. Introduce `h0`. Use `hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)` and prove the remaining obligations. Distinguish the cases in `hZ : Z' = Z`. Rewrite using `[hZ]`.

Conclude with `h0`. Rewrite using `[genVal_apply hG]`. Conclude with `evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2`.
-/
theorem genVal_ne_zero_of_mem_cuspOn' (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) : genVal Z f ≠ 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  intro h0
  refine hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)
  by_cases hZ : Z' = Z
  · rw [hZ]; exact h0
  · rw [genVal_apply hG]; exact evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2

/- English proof (translation)
Establish `hG : GenFrEx Xo c` using `(GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1`. Establish `h1 : genVal Z s = 0`. Establish `h2` using `congrArg (genVal Z) hsf`. Rewrite `h2` using `[map_mul, map_zero]`. Conclude with `(mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn' hf hf0)`.

Use `secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hZ : Z' = Z`. Rewrite using `[hZ, h1, mul_zero]`. Rewrite using `[genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]`.
-/
theorem idem_mul_eq_zero_of_mul_eq_zero' (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} {s : Rul Xo c}
    (hs : s ∈ secZ Xo c e') (hsf : s * f = 0) : idem Z * s = 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have h1 : genVal Z s = 0 := by
    have h2 := congrArg (genVal Z) hsf
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn' hf hf0)
  refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_
  rw [map_mul]
  by_cases hZ : Z' = Z
  · rw [hZ, h1, mul_zero]
  · rw [genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]

/- English proof (translation)
Establish `hfs : f ∈ secZ Xo c (exZ Dw G)` using `cuspW_le_secZ G (Submodule.mem_inf.1 hf).1`. Take `⟨R, hR, t, hmem, hφ⟩` from `GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z`. Set `b : R` to `⟨_, hmem _ f hfs⟩`. Establish `hb : ¬ IsNilpotent b` using `fun h => by`. Establish `h2 : ((b : Om Z)) = 0` using `by rw [h.eq_zero]; rfl`.

Conclude with `genVal_ne_zero_of_mem_cuspOn' hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))`. Take `⟨φ, hφσ, hφb⟩` from `exists_ringHom_ne_zero_of_not_isNilpotent' σ hb`. Take `⟨z, hz, s, hread⟩` from `hφ φ hφσ`. Use `⟨z, hz, fun h0 => hφb ?_⟩` and prove the remaining obligations. Rewrite using `[hread _ f hfs b rfl, h0, mul_zero]`.
-/
theorem exists_framesOn_rdU_ne_zero' (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) : ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f z.1 z.2 ≠ 0 := by
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G (Submodule.mem_inf.1 hf).1
  obtain ⟨R, hR, t, hmem, hφ⟩ :=
    GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z
  let b : R := ⟨_, hmem _ f hfs⟩
  have hb : ¬ IsNilpotent b := fun h => by
    have h2 : ((b : Om Z)) = 0 := by rw [h.eq_zero]; rfl
    exact genVal_ne_zero_of_mem_cuspOn' hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))
  obtain ⟨φ, hφσ, hφb⟩ := exists_ringHom_ne_zero_of_not_isNilpotent' σ hb
  obtain ⟨z, hz, s, hread⟩ := hφ φ hφσ
  refine ⟨z, hz, fun h0 => hφb ?_⟩
  rw [hread _ f hfs b rfl, h0, mul_zero]

/- English proof (translation)
Take `⟨k, hk⟩` from `framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ`. Establish `hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0`. Take `⟨⟨k₀, y₀⟩, hz₀, hne⟩` from `exists_framesOn_rdU_ne_zero' hL hσ hf hf0`. Rewrite `hz₀` using `[hk]`. Take `⟨h1, hy₀⟩` from `hz₀`.

Substitute `h1` using the available equality. Conclude with `⟨y₀, hy₀, hne⟩`. Establish `hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom` using `differentiableOn_of_mem_holSub' ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k`. Establish `hint` using `interior_closure_zeros ((U σ).X k) hdiff hex`. Establish `hcont : ContinuousOn (fun y => rdU (U σ) s k y - q k y) ((U σ).X k).dom` using `(GlobalTheory.T.continuousOn_reading_integerExponent_section E H Dw l Xo c r U x hL e' he s hs σ hσ k).sub (hq k)`.

Establish `hO` using `FourierCoefficientDomain.isOpen_dom ((U σ).X k)`. Establish `key : ∀ y ∈ ((U σ).X k).dom, rdU (U σ) s k y = q k y`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Establish `hev : ∀ᶠ w in 𝓝 y, rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom` using `((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hne)).and (hO.mem_nhds hy)`.

Establish `hsub : {w | rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom} ⊆ closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0}`. Introduce and unpack `w ⟨hw, hwd⟩`. Use `subset_closure ⟨hwd, ?_⟩` and prove the remaining obligations. Establish `h3` using `hrel ⟨k, w⟩ (by rw [hk]; exact ⟨rfl, hwd⟩)`. Rewrite `h3` using `[GlobalTheory.AllWt.rdU_mul (U σ)]`.

Establish `h2 : (rdU (U σ) s k w - q k w) * rdU (U σ) f k w = 0`. Rewrite using `[sub_mul, sub_eq_zero]`. Conclude with `h3`. Conclude with `(mul_eq_zero.1 h2).resolve_left hw`. Establish `hy' : y ∈ interior (closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0})` using `interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)`.

Rewrite `hy'` using `[hint]`. Conclude with `hy'`. Introduce and unpack `⟨k', y⟩ hz`. Rewrite `hz` using `[hk]`. Take `⟨h1, hy⟩` from `hz`.

Substitute `h1` using the available equality. Conclude with `key y hy`.
-/
theorem rdU_eq_of_rdU_mul' (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} (he : e' none = 0) {s : Rul Xo c} (hs : s ∈ secZ Xo c e')
    (q : FDSec (U σ).X) (hq : ∀ k, ContinuousOn (q k) ((U σ).X k).dom)
    (hrel : ∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) :
    ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2 := by
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0 := by
    obtain ⟨⟨k₀, y₀⟩, hz₀, hne⟩ := exists_framesOn_rdU_ne_zero' hL hσ hf hf0
    rw [hk] at hz₀
    obtain ⟨h1, hy₀⟩ := hz₀
    subst h1
    exact ⟨y₀, hy₀, hne⟩
  have hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom :=
    differentiableOn_of_mem_holSub' ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k
  have hint := interior_closure_zeros ((U σ).X k) hdiff hex
  have hcont : ContinuousOn (fun y => rdU (U σ) s k y - q k y) ((U σ).X k).dom :=
    (GlobalTheory.T.continuousOn_reading_integerExponent_section E H Dw l Xo c r U x hL e' he s hs σ hσ k).sub (hq k)
  have hO := FourierCoefficientDomain.isOpen_dom ((U σ).X k)
  have key : ∀ y ∈ ((U σ).X k).dom, rdU (U σ) s k y = q k y := by
    intro y hy
    by_contra hne
    have hev : ∀ᶠ w in 𝓝 y, rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom :=
      ((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hne)).and (hO.mem_nhds hy)
    have hsub : {w | rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom} ⊆
        closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0} := by
      rintro w ⟨hw, hwd⟩
      refine subset_closure ⟨hwd, ?_⟩
      have h3 := hrel ⟨k, w⟩ (by rw [hk]; exact ⟨rfl, hwd⟩)
      rw [GlobalTheory.AllWt.rdU_mul (U σ)] at h3
      have h2 : (rdU (U σ) s k w - q k w) * rdU (U σ) f k w = 0 := by
        rw [sub_mul, sub_eq_zero]
        exact h3
      exact (mul_eq_zero.1 h2).resolve_left hw
    have hy' : y ∈ interior (closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0}) :=
      interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)
    rw [hint] at hy'
    exact hy'
  rintro ⟨k', y⟩ hz
  rw [hk] at hz
  obtain ⟨h1, hy⟩ := hz
  subst h1
  exact key y hy

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL Z G e' f s hf hf0 hs`. Conclude with `⟨idem_mul_eq_zero_of_mul_eq_zero' hf hf0 hs, fun he σ hσ q hq hrel => rdU_eq_of_rdU_mul' hL hσ hf hf0 he hs q hq hrel⟩`.
-/
theorem cuspOn_cancel' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z G e' f s hf hf0 hs
  exact ⟨idem_mul_eq_zero_of_mul_eq_zero' hf hf0 hs,
    fun he σ hσ q hq hrel => rdU_eq_of_rdU_mul' hL hσ hf hf0 he hs q hq hrel⟩

end Cancel

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `Continuous.matrix_det (continuous_apply τ)`.
-/
theorem flatSec_continuous_det {r : ℕ} {Ψ : Finset (E →+* ℂ)} (τ : Ψ) :
    Continuous fun y : Frame Ψ r => (mat y τ).det :=
  Continuous.matrix_det (continuous_apply τ)

/- English proof (translation)
The claim follows from `(flatSec_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1`.
-/
theorem flatSec_continuousOn_horizGen {r : ℕ} (X : Data E r) (τ : X.Ψ) : ContinuousOn (horizGen τ) X.dom :=
  (flatSec_continuous_det τ).continuousOn.inv₀ fun _ hy => (hy τ).1

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

/- English proof (translation)
Use `((hU.2.1 k).2 _).2 ?_` and prove the remaining obligations. Establish `hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0` using `hσ`. Conclude with `(congrArg σ (Subtype.ext τ.2)).trans hσ0`.
-/
theorem flatSec_relab_mem {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (τ : Psi H) (k : U.Comp) :
    relab c σ τ.1 ∈ (U.X k).Ψ := by
  refine ((hU.2.1 k).2 _).2 ?_
  have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
  exact (congrArg σ (Subtype.ext τ.2)).trans hσ0

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x hL Z τ`. Take `⟨G, f, g, -, hf, hg, hf0, hq⟩` from `GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator E H Dw l Xo c r U x hL Z τ`. Establish `hfs : f ∈ secZ Xo c (exZ Dw G)` using `cuspW_le_secZ G hf.1`. Establish `hgs : g ∈ secZ Xo c (exZ Dw (G + wtOf Dw (flatWt Dw τ) 0))` using `cuspW_le_secZ _ hg.1`. Establish `hex : exZ Dw (G + wtOf Dw (flatWt Dw τ) 0) - exZ Dw G = exOf Dw (flatWt Dw τ) 0`.

Use function extensionality and compare the values at `i`. Rewrite using `[Pi.sub_apply, exZ_add, exOf, add_sub_cancel_left]`. Establish `hmem : ∀ σ (hσ : GoodEmb c σ) k, relab c σ τ.1 ∈ ((U σ).X k).Ψ` using `fun σ hσ k => flatSec_relab_mem (U σ) hσ (hL.unf σ hσ) τ k`. Establish `hgood : ∀ σ, GoodEmb c (goodOf c σ)` using `fun σ => goodEmb_goodOf c σ`. Establish `hσ₀` using `hgood c.F.val.toRingHom`.

Generalize the expression as in `goodOf c c.F.val.toRingHom = σ₀ at hσ₀`. Take `⟨a₀, ha₀, h₀⟩` from `hq σ₀ hσ₀`. Take `⟨sig, hsig, hsi, hsf⟩` from `GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ f g hfs hf.2 hgs hg.2 hf0 σ₀ hσ₀ (fun k y => a₀ * horizGen ⟨_, hmem σ₀ hσ₀ k⟩ y) (fun k => continuousOn_const.mul (flatSec_continuousOn_horizGen _ _)) (fun z hz => h₀ z.1 _ z.2 hz)`. Rewrite `hsig` using `[hex]`. Establish `hrd : ∀ σ (hσ : GoodEmb c σ), ∃ a : ℂ, a ≠ 0 ∧ ∀ z ∈ framesOn (U σ) Z, rdU (U σ) sig z.1 z.2 = a * horizGen ⟨_, hmem σ hσ z.1⟩ z.2` using `fun σ hσ => by`.

Take `⟨a, ha, h⟩` from `hq σ hσ`. Conclude with `⟨a, ha, (cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).2 rfl σ hσ (fun k y => a * horizGen ⟨_, hmem σ hσ k⟩ y) (fun k => continuousOn_const.mul (flatSec_continuousOn_horizGen _ _)) (fun z hz => hsf.symm ▸ h z.1 _ z.2 hz)⟩`. Establish `hnorm : ∀ σ (hσ : GoodEmb c σ), ∃ b : ℝ, 0 < b ∧ homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) sig '' framesOn (U σ) Z = {b}` using `fun σ hσ => by`. Take `⟨a, ha, h⟩` from `hrd σ hσ`. Take `⟨k, hk⟩` from `framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ`.

Take `⟨y, hy⟩` from `GlobalTheory.CompBij.frames_nonempty ((U σ).X k)`. Use `⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖), mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha) (Real.sqrt_pos.2 (norm_pos_iff.2 ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨⟨k, y⟩, ?_⟩, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `⟨rfl, hy⟩`. Introduce and unpack `⟨k', y'⟩ hz`.

Establish `h1` using `h _ hz`. Establish `hz'` using `hz`. Rewrite `hz'` using `[hk]`. Take `⟨rfl, hy'⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom` from `hz'`. Rewrite using `[← pnorm_horizGen ((U σ).X k') ⟨_, hmem σ hσ k'⟩ hy', homN, ptN, modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' (hmem σ hσ k')]`.

Simplify using `only at h1`. Simplify using `only [Data.pnorm, h1, norm_mul, mul_assoc]`. Establish `hg0 : g ≠ 0` using `fun h0 => by`. Establish `h1 : sig = 0` using `hsi.symm.trans ((cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).1 (hsf.trans h0))`. Take `⟨b, hb, h2⟩` from `hnorm σ₀ hσ₀`.

Take `⟨⟨z, hz⟩, h3⟩` from `image_eq_singleton_iff.1 h2`. Establish `h4` using `h3 z hz`. Rewrite `h4` using `[h1, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul]`. Conclude with `hb.ne h4`. Take `⟨inv, hinv, hii, hig⟩` from `GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ g f hgs hg.2 hfs hf.2 hg0 σ₀ hσ₀ (fun k y => a₀⁻¹ * (mat y ⟨_, hmem σ₀ hσ₀ k⟩).det) (fun k => (continuous_const.mul (flatSec_continuous_det _)).continuousOn) (fun z hz => by`.

Establish `hd` using `(hz.1 ⟨_, hmem σ₀ hσ₀ z.1⟩).1`. Rewrite using `[h₀ z.1 (hmem σ₀ hσ₀ z.1) z.2 hz, horizGen]`. Use the proof step `field_simp)`. Rewrite `hinv` using `[← neg_sub, hex]`. Establish `hif : idem Z * f = f` using `by rw [← hig, ← mul_assoc, hii]`.

Establish `hs0 : sig * inv - idem Z ∈ secZ Xo c 0`. Use `mul_mem_secZ hsig hinv` as an intermediate fact. Rewrite `this` using `[add_neg_cancel]`. Conclude with `Submodule.sub_mem _ this (idem_mem_secZ Z)`. Establish `hone : sig * inv = idem Z`.

Establish `h1` using `(cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f _ hf hf0 hs0).1 (by`. Rewrite using `[sub_mul, hif, mul_right_comm, hsf, mul_comm, hig, sub_self])`. Rewrite `h1` using `[mul_sub, ← mul_assoc, hsi, idem_mul_idem, sub_eq_zero]`. Then use the resulting hypothesis. Use `choose b hb hb' using fun σ => hnorm _ (hgood σ)`. Conclude with `⟨⟨sig, inv, hsig, hinv, hsi, hii, hone, b, hb, hb'⟩⟩`.
-/
theorem flatSec_always : Always fun U x => ArchEx U x := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ
  obtain ⟨G, f, g, -, hf, hg, hf0, hq⟩ := GlobalTheory.T.exists_cuspForm_pair_quotient_horizontal_generator E H Dw l Xo c r U x hL Z τ
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G hf.1
  have hgs : g ∈ secZ Xo c (exZ Dw (G + wtOf Dw (flatWt Dw τ) 0)) := cuspW_le_secZ _ hg.1
  have hex : exZ Dw (G + wtOf Dw (flatWt Dw τ) 0) - exZ Dw G = exOf Dw (flatWt Dw τ) 0 := by
    funext i; rw [Pi.sub_apply, exZ_add, exOf, add_sub_cancel_left]
  have hmem : ∀ σ (hσ : GoodEmb c σ) k, relab c σ τ.1 ∈ ((U σ).X k).Ψ := fun σ hσ k =>
    flatSec_relab_mem (U σ) hσ (hL.unf σ hσ) τ k
  have hgood : ∀ σ, GoodEmb c (goodOf c σ) := fun σ => goodEmb_goodOf c σ
  have hσ₀ := hgood c.F.val.toRingHom
  generalize goodOf c c.F.val.toRingHom = σ₀ at hσ₀
  obtain ⟨a₀, ha₀, h₀⟩ := hq σ₀ hσ₀
  obtain ⟨sig, hsig, hsi, hsf⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ f g hfs hf.2 hgs hg.2 hf0 σ₀ hσ₀
    (fun k y => a₀ * horizGen ⟨_, hmem σ₀ hσ₀ k⟩ y)
    (fun k => continuousOn_const.mul (flatSec_continuousOn_horizGen _ _)) (fun z hz => h₀ z.1 _ z.2 hz)
  rw [hex] at hsig
  have hrd : ∀ σ (hσ : GoodEmb c σ), ∃ a : ℂ, a ≠ 0 ∧ ∀ z ∈ framesOn (U σ) Z,
      rdU (U σ) sig z.1 z.2 = a * horizGen ⟨_, hmem σ hσ z.1⟩ z.2 := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hq σ hσ
    exact ⟨a, ha, (cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).2 rfl σ hσ
      (fun k y => a * horizGen ⟨_, hmem σ hσ k⟩ y)
      (fun k => continuousOn_const.mul (flatSec_continuousOn_horizGen _ _))
      (fun z hz => hsf.symm ▸ h z.1 _ z.2 hz)⟩
  have hnorm : ∀ σ (hσ : GoodEmb c σ), ∃ b : ℝ, 0 < b ∧
      homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) sig '' framesOn (U σ) Z = {b} := fun σ hσ => by
    obtain ⟨a, ha, h⟩ := hrd σ hσ
    obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
    obtain ⟨y, hy⟩ := GlobalTheory.CompBij.frames_nonempty ((U σ).X k)
    refine ⟨lieFacZ Dw x (wtOf Dw (flatWt Dw τ) 0) * (‖a‖ * Real.sqrt ‖relab c σ τ.1 ((U σ).X k).Gm.det‖),
      mul_pos (lieFacZ_pos _ _) (mul_pos (norm_pos_iff.2 ha) (Real.sqrt_pos.2 (norm_pos_iff.2
        ((map_ne_zero _).2 ((U σ).X k).Gm_det)))), image_eq_singleton_iff.2 ⟨⟨⟨k, y⟩, ?_⟩, ?_⟩⟩
    · rw [hk]; exact ⟨rfl, hy⟩
    · rintro ⟨k', y'⟩ hz
      have h1 := h _ hz
      have hz' := hz
      rw [hk] at hz'
      obtain ⟨rfl, hy'⟩ : k' = k ∧ y' ∈ ((U σ).X k').dom := hz'
      rw [← pnorm_horizGen ((U σ).X k') ⟨_, hmem σ hσ k'⟩ hy', homN, ptN,
        modelWt_flatWt (U σ) hσ (hL.unf σ hσ) τ k' (hmem σ hσ k')]
      simp only at h1
      simp only [Data.pnorm, h1, norm_mul, mul_assoc]
  have hg0 : g ≠ 0 := fun h0 => by
    have h1 : sig = 0 := hsi.symm.trans
      ((cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f sig hf hf0 hsig).1 (hsf.trans h0))
    obtain ⟨b, hb, h2⟩ := hnorm σ₀ hσ₀
    obtain ⟨⟨z, hz⟩, h3⟩ := image_eq_singleton_iff.1 h2
    have h4 := h3 z hz
    rw [h1, ← zero_smul c.F (0 : Rul Xo c), homN_smul, map_zero, norm_zero, zero_mul] at h4
    exact hb.ne h4
  obtain ⟨inv, hinv, hii, hig⟩ := GlobalTheory.T.exists_section_quotient_of_continuous_reading E H Dw l Xo c r U x hL Z _ _ g f hgs hg.2 hfs hf.2 hg0 σ₀ hσ₀
    (fun k y => a₀⁻¹ * (mat y ⟨_, hmem σ₀ hσ₀ k⟩).det)
    (fun k => (continuous_const.mul (flatSec_continuous_det _)).continuousOn) (fun z hz => by
      have hd := (hz.1 ⟨_, hmem σ₀ hσ₀ z.1⟩).1
      rw [h₀ z.1 (hmem σ₀ hσ₀ z.1) z.2 hz, horizGen]
      field_simp)
  rw [← neg_sub, hex] at hinv
  have hif : idem Z * f = f := by rw [← hig, ← mul_assoc, hii]
  have hs0 : sig * inv - idem Z ∈ secZ Xo c 0 := by
    have := mul_mem_secZ hsig hinv
    rw [add_neg_cancel] at this
    exact Submodule.sub_mem _ this (idem_mem_secZ Z)
  have hone : sig * inv = idem Z := by
    have h1 := (cuspOn_cancel' E H Dw l Xo c r U x hL Z G _ f _ hf hf0 hs0).1 (by
      rw [sub_mul, hif, mul_right_comm, hsf, mul_comm, hig, sub_self])
    rwa [mul_sub, ← mul_assoc, hsi, idem_mul_idem, sub_eq_zero] at h1
  choose b hb hb' using fun σ => hnorm _ (hgood σ)
  exact ⟨⟨sig, inv, hsig, hinv, hsi, hii, hone, b, hb, hb'⟩⟩

section General
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

/- English proof (translation)
Introduce `h0` and use `hf0 <| by have h1 : idem Z * f = f := idem_mul_eq (e := exZ _ G) ⟨cuspW_le_secZ _ hf.1, hf.2⟩ rw [← h1, ← h, mul_comm, ← mul_assoc, h0, zero_mul]`.
-/
theorem mul_ne_zero_of_inv {Z : Comp Xo c} {G : WTZ E} {f s t : Rul Xo c} (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0)
    (h : s * t = idem Z) : f * s ≠ 0 := fun h0 => hf0 <| by
  have h1 : idem Z * f = f := idem_mul_eq (e := exZ _ G) ⟨cuspW_le_secZ _ hf.1, hf.2⟩
  rw [← h1, ← h, mul_comm, ← mul_assoc, h0, zero_mul]

open GlobalTheory.ShFam GlobalTheory.KeyFourth GlobalTheory.LamT in

/- English proof (translation)
Take `⟨κ, k₁, k₂, -, k₄, k₅, k₆, -, -⟩` from `GlobalTheory.KeyFamClosing.keyFam_one`. Set `e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)` to `(Fintype.equivFin _).symm`. Take `⟨K, hKmem, hKval⟩` from `GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos`. Establish `hσ0` using `goodEmb_goodOf c c.F.val.toRingHom`. Take `⟨ρ, -⟩` from `GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos hKmem hKval`.

Use `⟨⟨ρ⟩, fun Z G hG ⟨f, hf, hf0⟩ => ⟨f * (idem Z * (K : Rul Xo c)), ?_, mul_ne_zero_of_inv (t := ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) hf hf0 (by rw [mul_assoc, Units.mul_inv, mul_one])⟩⟩` and prove the remaining obligations. Establish `hwt` using `GlobalTheory.KeyRootTw.wtOf_zero_fst E H Dw`. Establish `hex : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw`. Use function extensionality and compare the values at `i`. Break down `i with _ | ⟨τ, i⟩` into its components or cases.

Use `show (2 * (-4) : ℤ) = 4 * (-2)`. Evaluate the numerical expressions. Use `show (wtOf Dw 0 (-4)).1 (τ, (i : ℕ)) = 4 * 1`. Rewrite using `[hwt (-4) τ i i.2]`. Evaluate the numerical expressions.

Use `GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ _ ⟨ρ⟩ hL.unf hL.pos (even_wtOf _ _) (fun τ i j hij hj => by rw [hwt _ τ i (lt_of_le_of_lt hij hj), hwt _ τ j hj]) ?_ ?_ (fun σ hσ => ?_) G hG f hf` and prove the remaining obligations. Use `mul_mem_secZ (idem_mem_secZ Z) hKmem` as an intermediate fact. Rewrite `this` using `[zero_add, ← hex]`. Then use the resulting hypothesis. Rewrite using `[mul_comm]`. Conclude with `mul_mem_suppOn _ (idem_mem_suppOn Z)`.

Take `⟨C, hC, -, hCeq⟩` from `GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e σ r (U σ) x K hσ (hL.unf σ hσ) (hL.xi σ hσ) ⟨ρ⟩ hL.pos hKmem hKval`. Use `⟨C, fun z hz => ?_⟩` and prove the remaining obligations. Establish `h0 : homN (U σ) x (wtOf Dw 0 (-4)) (K : Rul Xo c) z = C` using `hCeq z.1 z.2 hz.1`. Establish `ht` using `tested_of_homN_ne (U σ) x hz.1 (h0.trans_ne hC.ne')`. Establish `h1` using `homN_mul (U σ) x (G := 0) (G' := wtOf Dw 0 (-4)) ⟨0, rfl⟩ (even_wtOf _ _) (idem Z) (K : Rul Xo c) z hz.1`.

Rewrite `h1` using `[zero_add, homN_idem (U σ) x hz.1 hz.2 ht, one_mul, h0]`. Conclude with `h1.le`.
-/
theorem exists_ne_zero_key (hL : Laws U x) : Nonempty (KeySec Xo c) ∧ ∀ (Z : Comp Xo c) (G : WTZ E), Even G.2 →
    (∃ f ∈ cuspOn U Z G, f ≠ 0) → ∃ f ∈ cuspOn U Z (G + wtOf Dw 0 (-4)), f ≠ 0 := by
  obtain ⟨κ, k₁, k₂, -, k₄, k₅, k₆, -, -⟩ := GlobalTheory.KeyFamClosing.keyFam_one
  let e : Fin (Fintype.card (Σ τ : E →+* ℂ, Fin (Dw.mult τ))) ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ) :=
    (Fintype.equivFin _).symm
  obtain ⟨K, hKmem, hKval⟩ := GlobalTheory.T.exists_unit_section_thetaKeyRule_weightFour κ k₁ k₂ k₆ E H Dw l Xo c _ e hL.pos
  have hσ0 := goodEmb_goodOf c c.F.val.toRingHom
  obtain ⟨ρ, -⟩ := GlobalTheory.T.exists_keySection_fourthRoot_perComponent κ k₁ k₂ k₆ k₄ E H Dw l Xo c _ e _ r (U _) K hσ0 (hL.unf _ hσ0) hL.geo hL.pos hKmem hKval
  refine ⟨⟨ρ⟩, fun Z G hG ⟨f, hf, hf0⟩ => ⟨f * (idem Z * (K : Rul Xo c)), ?_,
    mul_ne_zero_of_inv (t := ((K⁻¹ : (Rul Xo c)ˣ) : Rul Xo c)) hf hf0 (by rw [mul_assoc, Units.mul_inv, mul_one])⟩⟩
  have hwt := GlobalTheory.KeyRootTw.wtOf_zero_fst E H Dw
  have hex : exZ Dw (wtOf Dw 0 (-4)) = (4 : ℤ) • keyEx Dw := by
    funext i
    rcases i with _ | ⟨τ, i⟩
    · show (2 * (-4) : ℤ) = 4 * (-2)
      norm_num
    · show (wtOf Dw 0 (-4)).1 (τ, (i : ℕ)) = 4 * 1
      rw [hwt (-4) τ i i.2]; norm_num
  refine GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ _ ⟨ρ⟩ hL.unf hL.pos (even_wtOf _ _)
    (fun τ i j hij hj => by rw [hwt _ τ i (lt_of_le_of_lt hij hj), hwt _ τ j hj]) ?_ ?_ (fun σ hσ => ?_) G hG f hf
  · have := mul_mem_secZ (idem_mem_secZ Z) hKmem
    rwa [zero_add, ← hex] at this
  · rw [mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  · obtain ⟨C, hC, -, hCeq⟩ := GlobalTheory.T.thetaKeySection_norm_complexPoints_eq_two_pi_pow κ k₁ k₂ k₅ E H Dw l Xo c _ e σ r (U σ) x K hσ (hL.unf σ hσ) (hL.xi σ hσ)
      ⟨ρ⟩ hL.pos hKmem hKval
    refine ⟨C, fun z hz => ?_⟩
    have h0 : homN (U σ) x (wtOf Dw 0 (-4)) (K : Rul Xo c) z = C := hCeq z.1 z.2 hz.1
    have ht := tested_of_homN_ne (U σ) x hz.1 (h0.trans_ne hC.ne')
    have h1 := homN_mul (U σ) x (G := 0) (G' := wtOf Dw 0 (-4)) ⟨0, rfl⟩ (even_wtOf _ _) (idem Z) (K : Rul Xo c) z hz.1
    rw [zero_add, homN_idem (U σ) x hz.1 hz.2 ht, one_mul, h0] at h1
    exact h1.le

/- English proof (translation)
Take `⟨f, hf, hf0⟩` from `h`. Take `⟨s⟩` from `flatSec_always E H Dw l Xo c r U x hL Z τ`. Establish `hK` using `(exists_ne_zero_key hL).1`. Establish `hn : ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) s.sig z = s.cInf σ` using `fun σ hσ => by`. Establish `e : goodOf c σ = σ` using `if_pos hσ`.

Establish `h` using `(image_eq_singleton_iff.1 (s.norm_inf σ)).2`. Rewrite `h` using `[e]`. Conclude with `h`. Establish `hneg : wtOf Dw (-flatWt Dw τ) 0 = -wtOf Dw (flatWt Dw τ) 0` using `GlobalTheory.FlatTwisting.wtOf_parWt_neg _`. Use `⟨⟨f * s.sig, ?_, mul_ne_zero_of_inv hf hf0 s.mul_inv⟩, ⟨f * s.inv, ?_, mul_ne_zero_of_inv hf hf0 ((mul_comm _ _).trans s.mul_inv)⟩⟩` and prove the remaining obligations.

Use `GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hL.unf hL.pos (even_wtOf _ _) (GlobalTheory.FlatTwisting.wtOf_parWt_anti _) s.sig_mem ?_ (fun σ hσ => ⟨s.cInf σ, fun z hz => (hn σ hσ z hz).le⟩) G hG f hf` and prove the remaining obligations. Rewrite using `[← s.idem_sig, mul_comm]`. Conclude with `mul_mem_suppOn _ (idem_mem_suppOn Z)`. Use `GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw (-flatWt Dw τ) 0) s.inv hK hL.unf hL.pos (even_wtOf _ _) (GlobalTheory.FlatTwisting.wtOf_parWt_anti (-fun τ' => if τ' = τ then -1 else 0)) ?_ ?_ (fun σ hσ => ⟨(s.cInf σ)⁻¹, fun z hz => ?_⟩) G hG f hf` and prove the remaining obligations. Rewrite using `[hneg, GlobalTheory.FlatTw.exZ_neg_eq]`.

Conclude with `s.inv_mem`. Rewrite using `[← s.idem_inv, mul_comm]`. Conclude with `mul_mem_suppOn _ (idem_mem_suppOn Z)`. Establish `h1` using `homN_mul (U σ) x (even_wtOf (Dw := Dw) (flatWt Dw τ) 0) (even_wtOf (Dw := Dw) (-flatWt Dw τ) 0) s.sig s.inv z hz.1`. Establish `hp` using `s.cInf_pos σ`.

Establish `ht` using `tested_of_homN_ne (U σ) x hz.1 ((hn σ hσ z hz).trans_ne hp.ne')`. Rewrite `h1` using `[s.mul_inv, hn σ hσ z hz, ← wtOf_add', add_neg_cancel, wtOf_zero, homN_idem (U σ) x hz.1 hz.2 ht]`. Conclude with `(eq_inv_of_mul_eq_one_right h1.symm).le`.
-/
theorem exists_ne_zero_flat (hL : Laws U x) (Z : Comp Xo c) (τ : Psi H) (G : WTZ E) (hG : Even G.2)
    (h : ∃ f ∈ cuspOn U Z G, f ≠ 0) :
    (∃ f ∈ cuspOn U Z (G + wtOf Dw (flatWt Dw τ) 0), f ≠ 0) ∧ ∃ f ∈ cuspOn U Z (G + wtOf Dw (-flatWt Dw τ) 0), f ≠ 0 := by
  classical
  obtain ⟨f, hf, hf0⟩ := h
  obtain ⟨s⟩ := flatSec_always E H Dw l Xo c r U x hL Z τ
  have hK := (exists_ne_zero_key hL).1
  have hn : ∀ σ, GoodEmb c σ → ∀ z ∈ framesOn (U σ) Z, homN (U σ) x (wtOf Dw (flatWt Dw τ) 0) s.sig z = s.cInf σ :=
    fun σ hσ => by
      have e : goodOf c σ = σ := if_pos hσ
      have h := (image_eq_singleton_iff.1 (s.norm_inf σ)).2
      rw [e] at h
      exact h
  have hneg : wtOf Dw (-flatWt Dw τ) 0 = -wtOf Dw (flatWt Dw τ) 0 := GlobalTheory.FlatTwisting.wtOf_parWt_neg _
  refine ⟨⟨f * s.sig, ?_, mul_ne_zero_of_inv hf hf0 s.mul_inv⟩,
    ⟨f * s.inv, ?_, mul_ne_zero_of_inv hf hf0 ((mul_comm _ _).trans s.mul_inv)⟩⟩
  · refine GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z _ s.sig hK hL.unf hL.pos (even_wtOf _ _)
      (GlobalTheory.FlatTwisting.wtOf_parWt_anti _) s.sig_mem ?_ (fun σ hσ => ⟨s.cInf σ, fun z hz => (hn σ hσ z hz).le⟩) G hG f hf
    rw [← s.idem_sig, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
  · refine GlobalTheory.BddCusp.mul_mem_cuspOn_of_bdd E H Dw l Xo c r U x Z (wtOf Dw (-flatWt Dw τ) 0) s.inv hK hL.unf hL.pos (even_wtOf _ _)
      (GlobalTheory.FlatTwisting.wtOf_parWt_anti (-fun τ' => if τ' = τ then -1 else 0)) ?_ ?_
      (fun σ hσ => ⟨(s.cInf σ)⁻¹, fun z hz => ?_⟩) G hG f hf
    · rw [hneg, GlobalTheory.FlatTw.exZ_neg_eq]; exact s.inv_mem
    · rw [← s.idem_inv, mul_comm]; exact mul_mem_suppOn _ (idem_mem_suppOn Z)
    · have h1 := homN_mul (U σ) x (even_wtOf (Dw := Dw) (flatWt Dw τ) 0) (even_wtOf (Dw := Dw) (-flatWt Dw τ) 0)
        s.sig s.inv z hz.1
      have hp := s.cInf_pos σ
      have ht := tested_of_homN_ne (U σ) x hz.1 ((hn σ hσ z hz).trans_ne hp.ne')
      rw [s.mul_inv, hn σ hσ z hz, ← wtOf_add', add_neg_cancel, wtOf_zero, homN_idem (U σ) x hz.1 hz.2 ht] at h1
      exact (eq_inv_of_mul_eq_one_right h1.symm).le

/- English proof (translation)
Use `Finset.sum_induction _ P hadd h0 fun i _ => ?_` and prove the remaining obligations. Generalize the expression as in `n i = m`. Proceed by induction on `m using Int.induction_on with`. Consider the case `zero => rwa [zero_smul]`. Consider the case `succ m ih => rw [add_smul, one_smul]`.

Conclude with `hadd _ _ ih (h1 i)`. Consider the case `pred m ih => rw [sub_smul, one_smul, sub_eq_add_neg]`. Conclude with `hadd _ _ ih (h2 i)`.
-/
theorem sum_zsmul_induction {A ι : Type} [AddCommGroup A] (P : A → Prop) (h0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b))
    (s : Finset ι) (n : ι → ℤ) (a : ι → A) (h1 : ∀ i, P (a i)) (h2 : ∀ i, P (-a i)) : P (∑ i ∈ s, n i • a i) := by
  refine Finset.sum_induction _ P hadd h0 fun i _ => ?_
  generalize n i = m
  induction m using Int.induction_on with
  | zero => rwa [zero_smul]
  | succ m ih => rw [add_smul, one_smul]; exact hadd _ _ ih (h1 i)
  | pred m ih => rw [sub_smul, one_smul, sub_eq_add_neg]; exact hadd _ _ ih (h2 i)

/- English proof (translation)
Rewrite using `[parWt_eq_sum]`. Use `sum_zsmul_induction (fun la : AllWt.Weight Dw => ∀ G : WTZ E, Even G.2 → (∃ f ∈ cuspOn U Z G, f ≠ 0) → ∃ f ∈ cuspOn U Z (G + wtOf Dw la 0), f ≠ 0) ?_ ?_ _ _ _ (fun τ G hG h => (exists_ne_zero_flat hL Z τ G hG h).1) (fun τ G hG h => (exists_ne_zero_flat hL Z τ G hG h).2) G hG h` and prove the remaining obligations. Introduce `G _ h`. Rewrite using `[wtOf_zero, add_zero]` and apply the resulting hypothesis. Introduce `a b ha hb G hG h`.

Rewrite using `[wtOf_add', ← add_assoc]`. Conclude with `hb _ (hG.add (even_wtOf _ _)) (ha G hG h)`.
-/
theorem exists_ne_zero_par (hL : Laws U x) (Z : Comp Xo c) (w : Psi H → ℤ) (G : WTZ E) (hG : Even G.2)
    (h : ∃ f ∈ cuspOn U Z G, f ≠ 0) : ∃ f ∈ cuspOn U Z (G + wtOf Dw (parWt Dw w) 0), f ≠ 0 := by
  rw [parWt_eq_sum]
  refine sum_zsmul_induction (fun la : AllWt.Weight Dw => ∀ G : WTZ E, Even G.2 → (∃ f ∈ cuspOn U Z G, f ≠ 0) →
    ∃ f ∈ cuspOn U Z (G + wtOf Dw la 0), f ≠ 0) ?_ ?_ _ _ _ (fun τ G hG h => (exists_ne_zero_flat hL Z τ G hG h).1)
    (fun τ G hG h => (exists_ne_zero_flat hL Z τ G hG h).2) G hG h
  · intro G _ h
    rwa [wtOf_zero, add_zero]
  · intro a b ha hb G hG h
    rw [wtOf_add', ← add_assoc]
    exact hb _ (hG.add (even_wtOf _ _)) (ha G hG h)

/- English proof (translation)
Establish `h1` using `exists_ne_zero_par hL Z (-w) _ (even_wtOf _ _) h`. Establish `e : u + parWt Dw w + parWt Dw (-w) = u` using `by funext τ i; simp [parWt]`. Rewrite `h1` using `[← wtOf_add, e, add_zero]`. Use `clear h`. Proceed by induction on `m with`.

Consider the case `zero => simpa using h1`. Consider the case `succ m ih`. Establish `h2` using `(exists_ne_zero_key hL).2 Z _ (even_wtOf _ _) h1`. Rewrite `h2` using `[← wtOf_add, add_zero, show 4 * ((m + 1 : ℕ) : ℤ) + -4 = 4 * (m : ℤ) by push_cast; ring]`. Conclude with `ih h2`.
-/
theorem exists_ne_zero_back (hL : Laws U x) (Z : Comp Xo c) (u : AllWt.Weight Dw) (w : Psi H → ℤ) (m : ℕ)
    (h : ∃ f ∈ cuspOn U Z (wtOf Dw (u + parWt Dw w) (4 * (m : ℤ))), f ≠ 0) :
    ∃ f ∈ cuspOn U Z (wtOf Dw u 0), f ≠ 0 := by
  have h1 := exists_ne_zero_par hL Z (-w) _ (even_wtOf _ _) h
  have e : u + parWt Dw w + parWt Dw (-w) = u := by funext τ i; simp [parWt]
  rw [← wtOf_add, e, add_zero] at h1
  clear h
  induction m with
  | zero => simpa using h1
  | succ m ih =>
    have h2 := (exists_ne_zero_key hL).2 Z _ (even_wtOf _ _) h1
    rw [← wtOf_add, add_zero, show 4 * ((m + 1 : ℕ) : ℤ) + -4 = 4 * (m : ℤ) by push_cast; ring] at h2
    exact ih h2

/- English proof (translation)
Establish `hsurj : Function.Surjective (relab (E` using `E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)`. Take `⟨hp0, hΨ⟩` from `hV.2.1 k`. Establish `hr` using `hV.1`. Take `⟨τ', hτ'⟩` from `τ'`. Take `⟨ρ, rfl⟩` from `hsurj τ'`.

Establish `hρΨ : ρ (H.rt : E) = H.rt0`. Assume the negation of the conclusion as `hn`. Establish `h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0`. Establish `hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0` using `hσ`. Conclude with `(congrArg σ (Subtype.ext (conj_mem hn))).trans hσ0`.

Rewrite `h3` using `[relab_conj]`. Conclude with `conj_not_mem ⟨_, (hΨ _).1 hτ'⟩ h3`. Use `⟨⟨ρ, hρΨ⟩, fun j => ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `j`. Use `split_ifs with h`.

Conclude with `modelWt_wtOf_small V la m k hp0 ⟨ρ, hρΨ⟩ hτ' j h hj`. Take `⟨i, rfl⟩ : ∃ i, j = Dw.q + i` from `⟨j - Dw.q, by simp only at h; omega⟩`. Use `(modelWt_wtOf_big V la m k hp0 ⟨ρ, hρΨ⟩ hτ' i (by omega) hj).trans ?_` and prove the remaining obligations. Use `congr 2`. Simplify using the standard rewrite rules.
-/
theorem modelWt_entry {σ : c.F →+* ℂ} (V : Unf Xo c σ r) (hσ : GoodEmb c σ) (hV : IsUnf V) (la : AllWt.Weight Dw) (m : ℤ)
    (k : V.Comp) (τ' : (V.X k).Ψ) : ∃ τ : Psi H, ∀ j : Fin r, modelWt V (wtOf Dw la m) k τ' j =
      if h : (j : ℕ) < Dw.q then la τ ⟨Dw.p + j, by omega⟩ else la τ ⟨j - Dw.q, by have := hV.1; have := j.2; omega⟩ := by
  have hsurj : Function.Surjective (relab (E := E) c σ) := Finite.injective_iff_surjective.1 (relab_injective σ)
  obtain ⟨hp0, hΨ⟩ := hV.2.1 k
  have hr := hV.1
  obtain ⟨τ', hτ'⟩ := τ'
  obtain ⟨ρ, rfl⟩ := hsurj τ'
  have hρΨ : ρ (H.rt : E) = H.rt0 := by
    by_contra hn
    have h3 : relab c σ (conjEmb ρ) (H.rt : E) = H.rt0 := by
      have hσ0 : σ ⟨H.rt0, c.le (baseKA l).ρ.2⟩ = H.rt0 := hσ
      exact (congrArg σ (Subtype.ext (conj_mem hn))).trans hσ0
    rw [relab_conj] at h3
    exact conj_not_mem ⟨_, (hΨ _).1 hτ'⟩ h3
  refine ⟨⟨ρ, hρΨ⟩, fun j => ?_⟩
  obtain ⟨j, hj⟩ := j
  split_ifs with h
  · exact modelWt_wtOf_small V la m k hp0 ⟨ρ, hρΨ⟩ hτ' j h hj
  · obtain ⟨i, rfl⟩ : ∃ i, j = Dw.q + i := ⟨j - Dw.q, by simp only at h; omega⟩
    refine (modelWt_wtOf_big V la m k hp0 ⟨ρ, hρΨ⟩ hτ' i (by omega) hj).trans ?_
    congr 2
    simp

/- English proof (translation)
The claim follows from `| 0, i, j, e => by rw [show j = i from Fin.ext e] | d + 1, i, j, e => (h ⟨i + d, by have := j.2; omega⟩ j (by simp only; omega)).trans (anti_of_gaps h d i _ rfl)`.
-/
theorem anti_of_gaps {N : ℕ} {a : Fin N → ℤ} (h : ∀ i j : Fin N, (j : ℕ) = i + 1 → a j ≤ a i) :
    ∀ (d : ℕ) (i j : Fin N), (j : ℕ) = i + d → a j ≤ a i
  | 0, i, j, e => by rw [show j = i from Fin.ext e]
  | d + 1, i, j, e => (h ⟨i + d, by have := j.2; omega⟩ j (by simp only; omega)).trans (anti_of_gaps h d i _ rfl)

/- English proof (translation)
Establish `h1 : 4 * (q * p) ≤ (p + q) ^ 2` using `by nlinarith [sq_nonneg ((p : ℤ) - q)]`. Generalize the expression as in `p + q = r at *`. Establish `h2 : 2 * (r * (r - 1) / 2) = r * (r - 1)` using `Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd`. Establish `h3 : r * 5 ≤ r * (r - 1)` using `Nat.mul_le_mul_left _ (by omega)`. Generalize the expression as in `r * (r - 1) / 2 = t at *`.

Establish `h4 : 5 * r ≤ 2 * t` using `by omega`. Establish `h5 : 5 * (f * r) ≤ 2 * (f * t)` using `by nlinarith`. Establish `h6 : f * r ^ 2 ≤ (f * r) ^ 2` using `by nlinarith [Nat.mul_le_mul_right (f * r ^ 2) hf]`. Establish `h7 : 4 * (f * (q * p)) ≤ f * r ^ 2` using `by nlinarith [Nat.mul_le_mul_left f h1]`. Establish `h8 : (5 * (f * r)) ^ 2 ≤ (2 * (f * t)) ^ 2` using `Nat.pow_le_pow_left h5 2`.

Establish `h9 : 6 ≤ f * r` using `by nlinarith`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem numbers {f p q : ℕ} (hf : 1 ≤ f) (hr : 6 ≤ p + q) :
    4 * f * (p + q) ^ 2 + 4 * (f * (q * p)) ≤ (f * ((p + q) * (p + q - 1) / 2) + 3) ^ 2 ∧
      8 * (f * (p + q) + 1) + 2 ≤ (f * ((p + q) * (p + q - 1) / 2) + 3) ^ 2 := by
  have h1 : 4 * (q * p) ≤ (p + q) ^ 2 := by nlinarith [sq_nonneg ((p : ℤ) - q)]
  generalize p + q = r at *
  have h2 : 2 * (r * (r - 1) / 2) = r * (r - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self r).two_dvd
  have h3 : r * 5 ≤ r * (r - 1) := Nat.mul_le_mul_left _ (by omega)
  generalize r * (r - 1) / 2 = t at *
  have h4 : 5 * r ≤ 2 * t := by omega
  have h5 : 5 * (f * r) ≤ 2 * (f * t) := by nlinarith
  have h6 : f * r ^ 2 ≤ (f * r) ^ 2 := by nlinarith [Nat.mul_le_mul_right (f * r ^ 2) hf]
  have h7 : 4 * (f * (q * p)) ≤ f * r ^ 2 := by nlinarith [Nat.mul_le_mul_left f h1]
  have h8 : (5 * (f * r)) ^ 2 ≤ (2 * (f * t)) ^ 2 := Nat.pow_le_pow_left h5 2
  have h9 : 6 ≤ f * r := by nlinarith
  constructor <;> nlinarith

/- English proof (translation)
Establish `hσ : GoodEmb c c.F.val.toRingHom` using `rfl`. Generalize the expression as in `c.F.val.toRingHom = σ at hσ`. Establish `hV` using `hL.unf σ hσ`. Establish `hrr : r = Dw.p + Dw.q` using `hV.1`. Take `⟨k, hk⟩` from `framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ`.

Take `⟨hp0, hΨ⟩` from `hV.2.1 k`. Take `⟨x0, hx0, hFB⟩` from `hB σ hσ k`. Use `set f : ℕ := ((U σ).X k).Ψ.card with hf`. Establish `hcard : Fintype.card (Psi H) = f` using `Fintype.card_of_subtype _ hΨ`. Establish `h2f : 2 * f = finrank ℚ E` using `by rw [← RealPlaceEmbeddings.two_card_Psi ((U σ).X k), Fintype.card_coe]`.

Establish `hf1 : 1 ≤ f` using `by have : 0 < finrank ℚ E := finrank_pos; omega`. Establish `hD : dimFlag Dw = f * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2)` using `by rw [← hcard]; rfl`. Take `⟨n1, n2⟩` from `numbers (p := Dw.p) (q := Dw.q) hf1 (by omega)`. Rewrite `n1`, `n2` using `[← hD]`. Establish `hanti : ∀ τ (d : ℕ) (i j : Fin (Dw.p + Dw.q)), (j : ℕ) = i + d → u τ j ≤ u τ i` using `fun τ => anti_of_gaps fun i j e => by have := hu τ i j e; omega`.

Use `set m : ℕ := f * (Dw.p + Dw.q) + 1 with hm`. Use `set w : Psi H → ℤ := fun τ => 4 * (m : ℤ) + 1 - u τ ⟨Dw.p - 1, by omega⟩ with hw`. Use `exists_ne_zero_back hL Z u w m ?_` and prove the remaining obligations. Use `set G := wtOf Dw (u + parWt Dw w) (4 * (m : ℤ)) with hG`. Establish `hbar : ∀ τ, 8 * (m : ℤ) + 2 ≤ u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p, by omega⟩` using `fun τ => by`.

Use `hu τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp only; omega)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hstep : ∀ ρ i j, i ≤ j → j < Dw.mult ρ → 1 ≤ G.1 (ρ, j) ∧ G.1 (ρ, j) ≤ G.1 (ρ, i)` using `fun ρ i j hij hj => by`. Distinguish the cases in `h : ρ (H.rt : E) = H.rt0`. Establish `hj' : j < Dw.p` using `by simpa [Datum.mult, h] using hj`.

Establish `e1` using `wtOf_big (u + parWt Dw w) (4 * (m : ℤ)) ⟨ρ, h⟩ j hj'`. Establish `e2` using `wtOf_big (u + parWt Dw w) (4 * (m : ℤ)) ⟨ρ, h⟩ i (by omega)`. Establish `a1` using `hanti ⟨ρ, h⟩ (Dw.p - 1 - j) ⟨j, by omega⟩ ⟨Dw.p - 1, by omega⟩ (by simp only; omega)`. Establish `a2` using `hanti ⟨ρ, h⟩ (j - i) ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only; omega)`. Simplify using `only [Pi.add_apply, parWt, hw] at e1 e2`.

Rewrite using `[hG, e1, e2]`. Use linear arithmetic over natural numbers and integers. Establish `hj' : j < Dw.q` using `by simpa [Datum.mult, h] using hj`. Establish `e1` using `wtOf_small (u + parWt Dw w) (4 * (m : ℤ)) ⟨conjEmb ρ, conj_mem h⟩ j hj'`. Establish `e2` using `wtOf_small (u + parWt Dw w) (4 * (m : ℤ)) ⟨conjEmb ρ, conj_mem h⟩ i (by omega)`.

Establish `a1` using `hanti ⟨conjEmb ρ, conj_mem h⟩ (Dw.q - 1 - j) ⟨Dw.p, by omega⟩ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ rfl`. Establish `a2` using `hanti ⟨conjEmb ρ, conj_mem h⟩ (j - i) ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (by simp only; omega)`. Establish `a3` using `hbar ⟨conjEmb ρ, conj_mem h⟩`. Simplify using `only [Pi.add_apply, parWt, hw, conjEmb_conjEmb] at e1 e2`. Rewrite using `[hG, e1, e2]`.

Use linear arithmetic over natural numbers and integers. Establish `hoff : ∀ ρ j, ¬ j < Dw.mult ρ → G.1 (ρ, j) = 0` using `fun ρ j hj => by`. Distinguish the cases in `h : ρ (H.rt : E) = H.rt0`. Establish `hj' : ¬ j < Dw.p` using `by simpa [Datum.mult, h] using hj`. Simplify using `only [hG, wtOf, dif_pos h, dif_neg hj']`.

Establish `hj' : ¬ j < Dw.q` using `by simpa [Datum.mult, h] using hj`. Simplify using `only [hG, wtOf, dif_neg h, dif_neg hj', dite_eq_ite, ite_self]`. Establish `hnn : ∀ y, 0 ≤ G.1 y` using `fun ⟨ρ, j⟩ => by`. Distinguish the cases in `hj : j < Dw.mult ρ`. Use `(hstep ρ j j le_rfl hj).1` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `(hoff ρ j hj).ge`. Set `a : (E →+* ℂ) × ℕ → ℕ` to `fun y => (G.1 y).toNat`. Establish `hGa : wtZ a (8 * m) = G`. Use `Prod.ext (funext fun y => Int.toNat_of_nonneg (hnn y)) ?_` and prove the remaining obligations.

Rewrite using `[hG, wtOf_snd]`. Use `show ((8 * m : ℕ) : ℤ) = _`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hDom : Dom a (8 * m)`.

Use `⟨fun ρ i j hij => ?_, ⟨4 * m, by ring⟩⟩` and prove the remaining obligations. Distinguish the cases in `hj : j < Dw.mult ρ`. Conclude with `Int.toNat_le_toNat (hstep ρ i j hij hj).2`. Simplify using `only [a, hoff ρ j hj]`. Conclude with `Nat.zero_le _`.

Take `⟨P, hP, hP0⟩` from `exists_cusp_centre ((U σ).X k) (by omega) (by omega) hx0 hFB (modelWt (U σ) G k) (fun τ' i j hj hjp => by`. Apply the tactic sequence `obtain ⟨τ, hτ⟩ := modelWt_entry (U σ) hσ hV (u + parWt Dw w) (4 * (m : ℤ)) k τ'`. Rewrite using `[hG, hτ, hτ]`. Use `j.2` as an intermediate fact. Use `split_ifs with h1 h2 h2`.

Conclude with `add_le_add_left (hanti τ 1 _ _ (by simp only; omega)) _`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Conclude with `add_le_add_left (hanti τ 1 _ _ (by simp only; omega)) _)`. Use the proof step `(fun τ' i0 i1 h0 h1 => by`.

Apply the tactic sequence `obtain ⟨τ, hτ⟩ := modelWt_entry (U σ) hσ hV (u + parWt Dw w) (4 * (m : ℤ)) k τ'`. Rewrite using `[hG, hτ, hτ, dif_neg (by omega), dif_pos (by omega)]`. Use `hu τ ⟨i1 - Dw.q, by omega⟩ ⟨Dw.p + i0, by omega⟩ (by simp only; omega)` as an intermediate fact. Establish `hdx : GlobalTheory.Up.dimX ((U σ).X k) = f * (Dw.q * Dw.p)`. Unfold `GlobalTheory.Up.dimX`.

Rewrite using `[hp0, show r - Dw.q = Dw.p by omega]`. Establish `n3 : 4 * f * r ^ 2 + 4 * GlobalTheory.Up.dimX ((U σ).X k) + 2 * r ≤ (dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q)`. Rewrite `*` using `[hdx, ← hrr]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [Pi.add_apply, parWt]`.

Conclude with `(Int.ofNat_le.2 n3).trans (this.trans (le_of_eq (by ring))))`. Establish `hx0d` using `ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom _ x0 hx0`. Set `P' : FDSec (U σ).X` to `Pi.single (M := fun k => Frame ((U σ).X k).Ψ r → ℂ) k (((U σ).X k).dom.indicator P)`. Establish `hspan` using `(cuspOn_fd_and_span_rdU E H Dw l Xo c r U x hL Z σ hσ a (8 * m) hDom (fun ρ i hi => by have := (hstep ρ i i le_rfl hi).1; simp only [a]; omega) (by rw [← h2f, hm, hrr]; nlinarith)).2 P' (holCusp_mem_holSub _ _ fun k' => by`. Distinguish the cases in `e : k' = k`.

Substitute `e` using the available equality. Simplify using `only [P', Pi.single_eq_same, hGa]`. Conclude with `(GlobalTheory.UpTie.indicator_mem_SS_and_domSpan E r _ _ 0).1 P hP`. Simplify using `only [P', Pi.single_eq_of_ne e]`. Conclude with `GlobalTheory.FlatCore.MulSpan.zero_mem_SS' _ _)`.

Use the proof step `(fun k' y hy => by`. Distinguish the cases in `e : k' = k`. Substitute `e` using the available equality. Simplify using `only [P', Pi.single_eq_same]`. Use `Set.indicator_of_notMem (fun hd => hy ?_) _` and prove the remaining obligations.

Rewrite using `[hk]`. Conclude with `⟨rfl, hd⟩`. Simplify using `only [P', Pi.single_eq_of_ne e, Pi.zero_apply])`. Rewrite `hspan` using `[hGa]`. Assume the negation of the conclusion as `hcon`.

Use `push Not at hcon`. Establish `hle : Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))) ≤ ⊥`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨g, hg, rfl⟩`. Rewrite using `[hcon g hg, map_zero]`.

Conclude with `Submodule.zero_mem _`. Establish `h0 : P' = 0` using `hle hspan`. Establish `h1` using `congrFun (congrFun h0 k) x0`. Simplify using `only [P', Pi.single_eq_same, Pi.zero_apply, Set.indicator_of_mem hx0d] at h1`. Conclude with `hP0 h1`.
-/
theorem exists_cuspOn_ne_zero_of_ball (hL : Laws U x) (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (hr : 6 ≤ r)
    (hB : ∀ σ, GoodEmb c σ → ∀ k, ∃ x0, ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((U σ).X k) x0 ∧
      GlobalTheory.Up.FreeBall ((U σ).X k) ((U σ).X k).Γ x0 (1 / 4))
    (u : AllWt.Weight Dw) (hu : ∀ τ (a b : Fin (Dw.p + Dw.q)), (b : ℕ) = a + 1 →
      (((dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) : ℕ) : ℤ) ≤ u τ a - u τ b) (Z : Comp Xo c) :
    ∃ f ∈ cuspOn U Z (wtOf Dw u 0), f ≠ 0 := by
  classical
  have hσ : GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  have hV := hL.unf σ hσ
  have hrr : r = Dw.p + Dw.q := hV.1
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  obtain ⟨hp0, hΨ⟩ := hV.2.1 k
  obtain ⟨x0, hx0, hFB⟩ := hB σ hσ k
  set f : ℕ := ((U σ).X k).Ψ.card with hf
  have hcard : Fintype.card (Psi H) = f := Fintype.card_of_subtype _ hΨ
  have h2f : 2 * f = finrank ℚ E := by rw [← RealPlaceEmbeddings.two_card_Psi ((U σ).X k), Fintype.card_coe]
  have hf1 : 1 ≤ f := by have : 0 < finrank ℚ E := finrank_pos; omega
  have hD : dimFlag Dw = f * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by rw [← hcard]; rfl
  obtain ⟨n1, n2⟩ := numbers (p := Dw.p) (q := Dw.q) hf1 (by omega)
  rw [← hD] at n1 n2
  have hanti : ∀ τ (d : ℕ) (i j : Fin (Dw.p + Dw.q)), (j : ℕ) = i + d → u τ j ≤ u τ i := fun τ =>
    anti_of_gaps fun i j e => by have := hu τ i j e; omega
  set m : ℕ := f * (Dw.p + Dw.q) + 1 with hm
  set w : Psi H → ℤ := fun τ => 4 * (m : ℤ) + 1 - u τ ⟨Dw.p - 1, by omega⟩ with hw
  refine exists_ne_zero_back hL Z u w m ?_
  set G := wtOf Dw (u + parWt Dw w) (4 * (m : ℤ)) with hG
  have hbar : ∀ τ, 8 * (m : ℤ) + 2 ≤ u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p, by omega⟩ := fun τ => by
    have := hu τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp only; omega)
    omega
  have hstep : ∀ ρ i j, i ≤ j → j < Dw.mult ρ → 1 ≤ G.1 (ρ, j) ∧ G.1 (ρ, j) ≤ G.1 (ρ, i) := fun ρ i j hij hj => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hj' : j < Dw.p := by simpa [Datum.mult, h] using hj
      have e1 := wtOf_big (u + parWt Dw w) (4 * (m : ℤ)) ⟨ρ, h⟩ j hj'
      have e2 := wtOf_big (u + parWt Dw w) (4 * (m : ℤ)) ⟨ρ, h⟩ i (by omega)
      have a1 := hanti ⟨ρ, h⟩ (Dw.p - 1 - j) ⟨j, by omega⟩ ⟨Dw.p - 1, by omega⟩ (by simp only; omega)
      have a2 := hanti ⟨ρ, h⟩ (j - i) ⟨i, by omega⟩ ⟨j, by omega⟩ (by simp only; omega)
      simp only [Pi.add_apply, parWt, hw] at e1 e2
      rw [hG, e1, e2]
      omega
    · have hj' : j < Dw.q := by simpa [Datum.mult, h] using hj
      have e1 := wtOf_small (u + parWt Dw w) (4 * (m : ℤ)) ⟨conjEmb ρ, conj_mem h⟩ j hj'
      have e2 := wtOf_small (u + parWt Dw w) (4 * (m : ℤ)) ⟨conjEmb ρ, conj_mem h⟩ i (by omega)
      have a1 := hanti ⟨conjEmb ρ, conj_mem h⟩ (Dw.q - 1 - j) ⟨Dw.p, by omega⟩ ⟨Dw.p + (Dw.q - 1 - j), by omega⟩ rfl
      have a2 := hanti ⟨conjEmb ρ, conj_mem h⟩ (j - i) ⟨Dw.p + (Dw.q - 1 - j), by omega⟩
        ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ (by simp only; omega)
      have a3 := hbar ⟨conjEmb ρ, conj_mem h⟩
      simp only [Pi.add_apply, parWt, hw, conjEmb_conjEmb] at e1 e2
      rw [hG, e1, e2]
      omega
  have hoff : ∀ ρ j, ¬ j < Dw.mult ρ → G.1 (ρ, j) = 0 := fun ρ j hj => by
    by_cases h : ρ (H.rt : E) = H.rt0
    · have hj' : ¬ j < Dw.p := by simpa [Datum.mult, h] using hj
      simp only [hG, wtOf, dif_pos h, dif_neg hj']
    · have hj' : ¬ j < Dw.q := by simpa [Datum.mult, h] using hj
      simp only [hG, wtOf, dif_neg h, dif_neg hj', dite_eq_ite, ite_self]
  have hnn : ∀ y, 0 ≤ G.1 y := fun ⟨ρ, j⟩ => by
    by_cases hj : j < Dw.mult ρ
    · have := (hstep ρ j j le_rfl hj).1; omega
    · exact (hoff ρ j hj).ge
  let a : (E →+* ℂ) × ℕ → ℕ := fun y => (G.1 y).toNat
  have hGa : wtZ a (8 * m) = G := by
    refine Prod.ext (funext fun y => Int.toNat_of_nonneg (hnn y)) ?_
    rw [hG, wtOf_snd]
    show ((8 * m : ℕ) : ℤ) = _
    push_cast; ring
  have hDom : Dom a (8 * m) := by
    refine ⟨fun ρ i j hij => ?_, ⟨4 * m, by ring⟩⟩
    by_cases hj : j < Dw.mult ρ
    · exact Int.toNat_le_toNat (hstep ρ i j hij hj).2
    · simp only [a, hoff ρ j hj]; exact Nat.zero_le _
  obtain ⟨P, hP, hP0⟩ := exists_cusp_centre ((U σ).X k) (by omega) (by omega) hx0 hFB (modelWt (U σ) G k)
    (fun τ' i j hj hjp => by
      obtain ⟨τ, hτ⟩ := modelWt_entry (U σ) hσ hV (u + parWt Dw w) (4 * (m : ℤ)) k τ'
      rw [hG, hτ, hτ]
      have := j.2
      split_ifs with h1 h2 h2
      · exact add_le_add_left (hanti τ 1 _ _ (by simp only; omega)) _
      · omega
      · omega
      · exact add_le_add_left (hanti τ 1 _ _ (by simp only; omega)) _)
    (fun τ' i0 i1 h0 h1 => by
      obtain ⟨τ, hτ⟩ := modelWt_entry (U σ) hσ hV (u + parWt Dw w) (4 * (m : ℤ)) k τ'
      rw [hG, hτ, hτ, dif_neg (by omega), dif_pos (by omega)]
      have := hu τ ⟨i1 - Dw.q, by omega⟩ ⟨Dw.p + i0, by omega⟩ (by simp only; omega)
      have hdx : GlobalTheory.Up.dimX ((U σ).X k) = f * (Dw.q * Dw.p) := by
        unfold GlobalTheory.Up.dimX
        rw [hp0, show r - Dw.q = Dw.p by omega]
      have n3 : 4 * f * r ^ 2 + 4 * GlobalTheory.Up.dimX ((U σ).X k) + 2 * r ≤ (dimFlag Dw + 3) ^ 2 + 2 * (Dw.p + Dw.q) := by
        rw [hdx, ← hrr] at *; omega
      simp only [Pi.add_apply, parWt]
      exact (Int.ofNat_le.2 n3).trans (this.trans (le_of_eq (by ring))))
  have hx0d := ReciprocityTheory.ChartRestriction.G.AR.Up.IW.orth_mem_dom _ x0 hx0
  let P' : FDSec (U σ).X := Pi.single (M := fun k => Frame ((U σ).X k).Ψ r → ℂ) k (((U σ).X k).dom.indicator P)
  have hspan := (cuspOn_fd_and_span_rdU E H Dw l Xo c r U x hL Z σ hσ a (8 * m) hDom
    (fun ρ i hi => by have := (hstep ρ i i le_rfl hi).1; simp only [a]; omega)
    (by rw [← h2f, hm, hrr]; nlinarith)).2 P'
    (holCusp_mem_holSub _ _ fun k' => by
      by_cases e : k' = k
      · subst e
        simp only [P', Pi.single_eq_same, hGa]
        exact (GlobalTheory.UpTie.indicator_mem_SS_and_domSpan E r _ _ 0).1 P hP
      · simp only [P', Pi.single_eq_of_ne e]
        exact GlobalTheory.FlatCore.MulSpan.zero_mem_SS' _ _)
    (fun k' y hy => by
      by_cases e : k' = k
      · subst e
        simp only [P', Pi.single_eq_same]
        refine Set.indicator_of_notMem (fun hd => hy ?_) _
        rw [hk]; exact ⟨rfl, hd⟩
      · simp only [P', Pi.single_eq_of_ne e, Pi.zero_apply])
  rw [hGa] at hspan
  by_contra hcon
  push Not at hcon
  have hle : Submodule.span ℂ (rdU (U σ) '' (cuspOn U Z G : Set (Rul Xo c))) ≤ ⊥ := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    rw [hcon g hg, map_zero]
    exact Submodule.zero_mem _
  have h0 : P' = 0 := hle hspan
  have h1 := congrFun (congrFun h0 k) x0
  simp only [P', Pi.single_eq_same, Pi.zero_apply, Set.indicator_of_mem hx0d] at h1
  exact hP0 h1

end General

section Cover

open GlobalTheory.CovTop GlobalTheory.PrincCore Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {T : CoreJ D} {j : ℕ} {Y : Deep T.toCore j} {e : ℕ} {o : ℝ}

/- English proof (translation)
Rewrite using `[hG.lev.1.2.1, hT.pins.2.1.1]`.
-/
theorem level_eq (hT : LawsJ T) (hG : Y.Good e o) : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by
  rw [hG.lev.1.2.1, hT.pins.2.1.1]

/- English proof (translation)
Use `D.R.two_le_m` as an intermediate fact. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.r`. Use linear arithmetic over natural numbers and integers.
-/
theorem six_le_rank (D : D7) : 6 ≤ D.R.r := by
  have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega

/- English proof (translation)
Establish `hr : 0 < D.R.r` using `by have := six_le_rank D; omega`. Take `⟨γ', hγ', u, n, hn, hu, he⟩` from `GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) (hG.unf σ hσ) hG.lev.2 hr k γ hγ hc`. Take `⟨th, hrk, hth, hD⟩` from `hG.dictU σ hσ`. Establish `hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ))` using `⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩`. Establish `h1` using `root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD hmu _ Y.d.l₂.three_le (level_eq hT hG ▸ hG.levelK) k γ γ' hγ' hc u n hn hu he`.

Rewrite `he` using `[h1, one_smul]`. Conclude with `Units.ext he ▸ hγ'`.
-/
theorem mem_of_cong (hT : LawsJ T) (hG : Y.Good e o) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) (k : (Y.U σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E) (hγ : IsUStab ((Y.U σ).X k).Gm ((Y.U σ).X k).Λ γ)
    (hc : ∀ x ∈ ((Y.U σ).X k).Λ, ∃ y ∈ ((Y.U σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (Y.d.l₂.M : D.host.E) • y) :
    γ ∈ ((Y.U σ).X k).Γ := by
  have hr : 0 < D.R.r := by have := six_le_rank D; omega
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) (hG.unf σ hσ) hG.lev.2 hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩
  have h1 := root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD
    hmu _ Y.d.l₂.three_le (level_eq hT hG ▸ hG.levelK) k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Establish `hr : 1 ≤ D.R.r` using `by have := six_le_rank D; omega`. Establish `hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p` using `goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne`. Use `⟨?_, hG.lev.2, GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0, hG.unf, hG.geo, hG.xiAbs, hG.chiTriv, fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_, GlobalTheory.RankOneDatum.exists_datum_of_rt D _ hT.pins.1.2.1 hT.pins.1.2.2.1⟩` and prove the remaining obligations. Establish `e : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q` using `(hG.unf Y.d.c₂.F.val.toRingHom rfl).1`. Use linear arithmetic over natural numbers and integers.

Take `⟨th, hrk, hth, hD⟩` from `hG.dictU σ hσ`. Conclude with `GlobalTheory.LevLaws.det_eq_one _ hrk hr (Y.U σ).X (Y.dict σ) Y.Kf th hth hD (hG.unit σ hσ) _ Y.d.l₂.three_le (level_eq hT hG ▸ hG.levelK) k γ hγ`. Take `⟨hrk, hM⟩` from `hG.modelW σ hσ`. Establish `key` using `GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E _ _ _ Y.d.Xo₂ Y.d.c₂ D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (Y.U s)) hr hG.lev.2 (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf s hs)) σ hσ (fun k k' => ⟨(hM k).1.trans ( …`. Take `⟨y, hy, e⟩` from `hc0 x hx`.

Conclude with `⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩)`. Use `a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => hG.chiTriv σ hσ a n ha k)`. Introduce `P hP`. Conclude with `key ⟨hP.1, hP.2⟩`.
-/
theorem laws_good (hT : LawsJ T) (hG : Y.Good e o) : Laws Y.U (xiR D) := by
  have hr : 1 ≤ D.R.r := by have := six_le_rank D; omega
  have hg0 : ∀ p : ℕ, p.Prime → T.Q.l.GoodAt p :=
    goodAt_of_two_primes hT.pins.2.1.1 (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne
  refine ⟨?_, hG.lev.2, GlobalTheory.LawsDeep.goodAt_of_mul _ _ _ hG.lev.1.2.1 hg0, hG.unf, hG.geo, hG.xiAbs, hG.chiTriv,
    fun σ hσ k γ hγ => ?_, fun σ hσ a n ha hp hn => ?_,
    GlobalTheory.RankOneDatum.exists_datum_of_rt D _ hT.pins.1.2.1 hT.pins.1.2.2.1⟩
  · have e : D.R.r = (T.Q.Dw j).p + (T.Q.Dw j).q := (hG.unf Y.d.c₂.F.val.toRingHom rfl).1
    omega
  · obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
    exact GlobalTheory.LevLaws.det_eq_one _ hrk hr (Y.U σ).X (Y.dict σ) Y.Kf th hth hD (hG.unit σ hσ) _ Y.d.l₂.three_le
      (level_eq hT hG ▸ hG.levelK) k γ hγ
  · obtain ⟨hrk, hM⟩ := hG.modelW σ hσ
    have key := GlobalTheory.Dict.holSub0_le_span_cusp GlobalTheory.chartIndependence_unconditional D.host.E _ _ _
      Y.d.Xo₂ Y.d.c₂ D.R.r (fun s => Formalism.L2.PjFree.Unf.ofPj (Y.U s)) hr hG.lev.2
      (fun s hs => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf s hs)) σ hσ
      (fun k k' => ⟨(hM k).1.trans (hM k').1.symm, (hM k).2.trans (hM k').2.symm⟩)
      (fun k γ hγ hc0 => mem_of_cong hT hG hσ k γ hγ fun x hx => by
        obtain ⟨y, hy, e⟩ := hc0 x hx
        exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩)
      a n ha (fun τ _ h0 => hp τ _ (by omega)) hn (fun k => hG.chiTriv σ hσ a n ha k)
    intro P hP
    exact key ⟨hP.1, hP.2⟩

/- English proof (translation)
Rewrite using `[ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_rmul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul η γ, ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_inv]`.
-/
theorem lact_inv_rmul {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (η γ : GL (Fin r) E) (x b : Frame Ψ r) : lact (η * γ)⁻¹ (rmul (lact η (lact γ x)) b) = rmul x b := by
  rw [ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_rmul, ← ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_mul η γ,
    ReciprocityTheory.ChartRestriction.G.AR.Up.FundSetPf.lact_inv]

/- English proof (translation)
Establish `hr : 1 ≤ D.R.r` using `by have := six_le_rank D; omega`. Take `⟨x0, hx0⟩` from `GlobalTheory.CompBij.frames_nonempty ((Y.U σ).X k)`. Take `⟨η, hηU, hηc, b, hb, hx⟩` from `GlobalTheory.CongrOrbit.exists_congr_back _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ x0 hx0`. Establish `hηΓ : η ∈ ((Y.U σ).X k).Γ` using `mem_of_cong hT hG hσ k η hηU hηc`. Establish `hmem : (η * γ)⁻¹ ∈ ((Y.U σ).X k).Γ` using `inv_mem (mul_mem hηΓ hγ)`.

Establish `hfix : lact (η * γ)⁻¹ x0 = rmul x0 b`. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `((Y.U σ).X k).Γ_free _ hmem x0 hx0 b hb hfix`. Establish `hγη : γ = η⁻¹`. Rewrite `h1` using `[inv_eq_one]`.

Conclude with `eq_inv_of_mul_eq_one_right h1`. Establish `hγU` using `((Y.U σ).X k).Γ_stab γ hγ`. Introduce `u hu`. Take `⟨y, hy, he⟩` from `hηc (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) ((hγU.2 u).1 hu)`. Establish `hηγ : Matrix.mulVec (η : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) = u`.

Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul, hγη, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]`. Use `⟨-y, ((Y.U σ).X k).Λ.neg_mem hy, ?_⟩` and prove the remaining obligations. Rewrite `he` using `[hηγ]`. Rewrite using `[smul_neg, ← he]`. Normalize the expressions using the abelian group laws.
-/
theorem cong_of_mem (hT : LawsJ T) (hG : Y.Good e o) {σ : Y.d.c₂.F →+* ℂ} (hσ : GoodEmb Y.d.c₂ σ) (k : (Y.U σ).Comp)
    (γ : GL (Fin D.R.r) D.host.E) (hγ : γ ∈ ((Y.U σ).X k).Γ) : ∀ u ∈ ((Y.U σ).X k).Λ, ∃ y ∈ ((Y.U σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u - u = (Y.d.l₂.M : D.host.E) • y := by
  have hr : 1 ≤ D.R.r := by have := six_le_rank D; omega
  obtain ⟨x0, hx0⟩ := GlobalTheory.CompBij.frames_nonempty ((Y.U σ).X k)
  obtain ⟨η, hηU, hηc, b, hb, hx⟩ := GlobalTheory.CongrOrbit.exists_congr_back _ _ _ _ _ _ _ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) hσ
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ x0 hx0
  have hηΓ : η ∈ ((Y.U σ).X k).Γ := mem_of_cong hT hG hσ k η hηU hηc
  have hmem : (η * γ)⁻¹ ∈ ((Y.U σ).X k).Γ := inv_mem (mul_mem hηΓ hγ)
  have hfix : lact (η * γ)⁻¹ x0 = rmul x0 b := by
    calc lact (η * γ)⁻¹ x0 = lact (η * γ)⁻¹ (rmul (lact η (lact γ x0)) b) := congrArg _ hx
      _ = rmul x0 b := lact_inv_rmul η γ x0 b
  have h1 := ((Y.U σ).X k).Γ_free _ hmem x0 hx0 b hb hfix
  have hγη : γ = η⁻¹ := by
    rw [inv_eq_one] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hγU := ((Y.U σ).X k).Γ_stab γ hγ
  intro u hu
  obtain ⟨y, hy, he⟩ := hηc (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) ((hγU.2 u).1 hu)
  have hηγ : Matrix.mulVec (η : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)
      (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) u) = u := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, hγη, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  refine ⟨-y, ((Y.U σ).X k).Λ.neg_mem hy, ?_⟩
  rw [hηγ] at he
  rw [smul_neg, ← he]
  abel

/- English proof (translation)
Establish `h1 : ∀ b ∈ 𝔄⁻¹, ∀ v ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ L, v = a • u}, b • v ∈ L`. Introduce `b hb v hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem v hv`. Take `⟨a, ha, u, hu, rfl⟩` from `hv`.

Establish `h2` using `FractionalIdeal.mul_mem_mul hb ha`. Rewrite `h2` using `[inv_mul_cancel₀ h, FractionalIdeal.mem_one_iff]`. Take `⟨t, ht⟩` from `h2`. Rewrite using `[smul_smul, ← ht, algebraMap_smul]`. Conclude with `L.smul_mem t hu`.

Consider the case `zero => rw [smul_zero]`. Conclude with `L.zero_mem`. Consider the case `add v w _ _ hv hw => rw [smul_add]`. Conclude with `L.add_mem hv hw`. Consider the case `smul t v _ hv => rw [smul_comm]`.

Conclude with `L.smul_mem t hv`. Establish `h3 : (1 : E) ∈ 𝔄⁻¹ * 𝔄` using `by rw [inv_mul_cancel₀ h]; exact FractionalIdeal.one_mem_one _`. Establish `h4 : (1 : E) • z ∈ L` using `FractionalIdeal.mul_induction_on (C := fun t => t • z ∈ L) h3 (fun b hb a ha => by rw [← smul_smul]; exact h1 b hb _ (hz a ha)) (fun s t hs ht => by rw [add_smul]; exact L.add_mem hs ht)`. Rewrite `h4` using `[one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_of_ideal_smul {E : Type} [Field E] [NumberField E] {r : ℕ} (L : Submodule (𝓞 E) (Fin r → E))
    (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (h : 𝔄 ≠ 0) (z : Fin r → E)
    (hz : ∀ a ∈ 𝔄, a • z ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ L, v = a • u}) : z ∈ L := by
  have h1 : ∀ b ∈ 𝔄⁻¹, ∀ v ∈ Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ u ∈ L, v = a • u}, b • v ∈ L := by
    intro b hb v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, u, hu, rfl⟩ := hv
      have h2 := FractionalIdeal.mul_mem_mul hb ha
      rw [inv_mul_cancel₀ h, FractionalIdeal.mem_one_iff] at h2
      obtain ⟨t, ht⟩ := h2
      rw [smul_smul, ← ht, algebraMap_smul]
      exact L.smul_mem t hu
    | zero => rw [smul_zero]; exact L.zero_mem
    | add v w _ _ hv hw => rw [smul_add]; exact L.add_mem hv hw
    | smul t v _ hv => rw [smul_comm]; exact L.smul_mem t hv
  have h3 : (1 : E) ∈ 𝔄⁻¹ * 𝔄 := by rw [inv_mul_cancel₀ h]; exact FractionalIdeal.one_mem_one _
  have h4 : (1 : E) • z ∈ L := FractionalIdeal.mul_induction_on (C := fun t => t • z ∈ L) h3
    (fun b hb a ha => by rw [← smul_smul]; exact h1 b hb _ (hz a ha))
    (fun s t hs ht => by rw [add_smul]; exact L.add_mem hs ht)
  rwa [one_smul] at h4

/- English proof (translation)
Take `⟨Xx, 𝔄, hX, h𝔄, hΛ⟩` from `GlobalTheory.CovData.exists_dataX_good D T.toCore j Y e o hG σ hσ k`. Establish `hM : 5 ≤ Y.d.l₂.M`. Rewrite using `[level_eq hT hG]`. Establish `h0` using `(D.host.g_prime 0).two_le`. Establish `h1` using `(D.host.g_prime 1).two_le`.

Establish `h2 : D.host.g 0 ≠ D.host.g 1` using `D.host.g_ne`. Establish `hp : 1 ≤ Y.d.pd` using `by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)`. Establish `: 6 ≤ D.host.g 0 * D.host.g 1`. Apply the tactic sequence `rcases lt_or_gt_of_ne h2 with h | h <;> nlinarith`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hc` using `cong_of_mem hT hG hσ k`. Rewrite `hc`, the goal using `[← hX]`. Use `exists_freeBall Xx hM fun γ hγ w hw => ?_` and prove the remaining obligations. Establish `hM0 : (Y.d.l₂.M : D.host.E) ≠ 0` using `by exact_mod_cast (show Y.d.l₂.M ≠ 0 by omega)`. Use `⟨(Y.d.l₂.M : D.host.E)⁻¹ • (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w), mem_of_ideal_smul _ 𝔄 h𝔄 _ fun a ha => ?_, by rw [smul_smul, mul_inv_cancel₀ hM0, one_smul]⟩` and prove the remaining obligations.

Take `⟨y, hy, he⟩` from `hc γ hγ (a • w) (hΛ ▸ Submodule.subset_span ⟨a, ha, w, hw, rfl⟩)`. Rewrite using `[smul_comm, smul_sub, ← Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hM0, one_smul, ← hΛ]`. Conclude with `hy`.
-/
theorem exists_freeBall_good (hT : LawsJ T) (hG : Y.Good e o) (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ)
    (k : (Y.U σ).Comp) : ∃ x0, ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth ((Y.U σ).X k) x0 ∧
      GlobalTheory.Up.FreeBall ((Y.U σ).X k) ((Y.U σ).X k).Γ x0 (1 / 4) := by
  obtain ⟨Xx, 𝔄, hX, h𝔄, hΛ⟩ := GlobalTheory.CovData.exists_dataX_good D T.toCore j Y e o hG σ hσ k
  have hM : 5 ≤ Y.d.l₂.M := by
    rw [level_eq hT hG]
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have h2 : D.host.g 0 ≠ D.host.g 1 := D.host.g_ne
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 6 ≤ D.host.g 0 * D.host.g 1 := by
      rcases lt_or_gt_of_ne h2 with h | h <;> nlinarith
    nlinarith
  have hc := cong_of_mem hT hG hσ k
  rw [← hX] at hc ⊢
  refine exists_freeBall Xx hM fun γ hγ w hw => ?_
  have hM0 : (Y.d.l₂.M : D.host.E) ≠ 0 := by exact_mod_cast (show Y.d.l₂.M ≠ 0 by omega)
  refine ⟨(Y.d.l₂.M : D.host.E)⁻¹ • (Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) w - w),
    mem_of_ideal_smul _ 𝔄 h𝔄 _ fun a ha => ?_, by rw [smul_smul, mul_inv_cancel₀ hM0, one_smul]⟩
  obtain ⟨y, hy, he⟩ := hc γ hγ (a • w) (hΛ ▸ Submodule.subset_span ⟨a, ha, w, hw, rfl⟩)
  rw [smul_comm, smul_sub, ← Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hM0, one_smul, ← hΛ]
  exact hy

end Cover

end GlobalTheory.CentreCusp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.CentreCusp

/- English proof (translation)
Take `⟨f, hf, hf0⟩` from `exists_cuspOn_ne_zero_of_ball (laws_good hT hY) hp hq (six_le_rank D) (exists_freeBall_good hT hY) u hu Z`. Conclude with `⟨f, hf, genVal_ne_zero_of_mem_cuspOn' hf hf0⟩`.
-/
theorem exists_cusp_genVal_ne_zero' (D : D7) (T : CoreJ D) (hT : LawsJ T) (j : ℕ) (hp : 1 ≤ (T.Q.Dw j).p)
    (hq : 1 ≤ (T.Q.Dw j).q) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ) (hY : Y.Good e o) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j))
    (hu : ∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 →
      (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) : ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 := by
  obtain ⟨f, hf, hf0⟩ := exists_cuspOn_ne_zero_of_ball (laws_good hT hY) hp hq (six_le_rank D)
    (exists_freeBall_good hT hY) u hu Z
  exact ⟨f, hf, genVal_ne_zero_of_mem_cuspOn' hf hf0⟩

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ D T hT j hp hq Y e o hY u hu Z` and use `exists_cusp_genVal_ne_zero' D T hT j hp hq Y e o hY u hu Z`.
-/
theorem exists_cusp_genVal_ne_zero : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → Hypotheses₂ → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0), genVal Z f ≠ 0 :=
  fun _ _ _ _ _ _ _ D T hT j hp hq Y e o hY u hu Z => exists_cusp_genVal_ne_zero' D T hT j hp hq Y e o hY u hu Z

end GlobalTheory.CentreCusp

end
