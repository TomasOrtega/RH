import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypePlaceResidueCharactersValuesMemSmallFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CurveOverOfRayIn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FixBaseSmall

/- English proof (translation)
Set `e : D.host.E →+* ↥D.LL0` to `D.embE.codRestrict D.LL0 fun y => D.hostField_le_fixedField y`. Establish `hsp` using `Normal.splits hgal.to_normal (e x)`. Establish `hmin : minpoly ℚ (e x) = minpoly ℚ x` using `minpoly.algHom_eq e.toRatAlgHom e.injective x`. Rewrite `hsp` using `[hmin]`. Establish `himg` using `Polynomial.Splits.image_rootSet hsp (embLL0 D).toRatAlgHom`.

Establish `hx : φ x ∈ (minpoly ℚ x).rootSet ℂ`. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x), ?_⟩` and prove the remaining obligations. Use `Polynomial.aeval_algHom_apply φ.toRatAlgHom x (minpoly ℚ x)` as an intermediate fact. Rewrite `this` using `[minpoly.aeval, map_zero]`.

Conclude with `this`. Rewrite `hx` using `[← himg]`. Take `⟨y, -, hy⟩` from `hx`. Conclude with `⟨y, hy⟩`.
-/
theorem host_mem (D : D7) (hgal : IsGalois ℚ D.LL0) (φ : D.host.E →+* ℂ) (x : D.host.E) :
    φ x ∈ (embLL0 D).fieldRange := by
  let e : D.host.E →+* ↥D.LL0 := D.embE.codRestrict D.LL0 fun y => D.hostField_le_fixedField y
  have hsp := Normal.splits hgal.to_normal (e x)
  have hmin : minpoly ℚ (e x) = minpoly ℚ x := minpoly.algHom_eq e.toRatAlgHom e.injective x
  rw [hmin] at hsp
  have himg := Polynomial.Splits.image_rootSet hsp (embLL0 D).toRatAlgHom
  have hx : φ x ∈ (minpoly ℚ x).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral x), ?_⟩
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom x (minpoly ℚ x)
    rw [minpoly.aeval, map_zero] at this
    exact this
  rw [← himg] at hx
  obtain ⟨y, -, hy⟩ := hx
  exact ⟨y, hy⟩

/- English proof (translation)
Use `⟨S.kKs ((YS.fi j).eK.symm a), ?_⟩` and prove the remaining obligations. Establish `h1 : res T D.what₂.embLL = T.σ₀` using `res_embLL T ha hLaws.pins.2.2.1`. Express the relevant statement in the definitionally equal form `D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm a) : ↥D.LL0) : D.what₂.LL) = (a : ℂ)`. Rewrite using `[S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]`. Conclude with `RingHom.congr_fun h1 a`.
-/
theorem core_mem {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (Rl : RealDat3 D A3 ↥T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S)
    (hLaws : LawsJ T) (ha : AlgTie T) (j : Fin D.R.m) (a : T.Q.c.F) : (a : ℂ) ∈ (embLL0 D).fieldRange := by
  refine ⟨S.kKs ((YS.fi j).eK.symm a), ?_⟩
  have h1 : res T D.what₂.embLL = T.σ₀ := res_embLL T ha hLaws.pins.2.2.1
  change D.what₂.embLL ((S.kKs ((YS.fi j).eK.symm a) : ↥D.LL0) : D.what₂.LL) = (a : ℂ)
  rw [S.kKs_spec, ← (YS.fi j).eK_LL, RingEquiv.apply_symm_apply]
  exact RingHom.congr_fun h1 a

/- English proof (translation)
Establish `h0` using `(D.host.g_prime 0).two_le`. Establish `h1` using `(D.host.g_prime 1).two_le`. Establish `h2` using `D.host.pde_prime.two_le`. Establish `h3` using `D.host.pde'_prime.two_le`. Use `Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem three_le_mod (D : D7) : 3 ≤ D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' := by
  have h0 := (D.host.g_prime 0).two_le
  have h1 := (D.host.g_prime 1).two_le
  have h2 := D.host.pde_prime.two_le
  have h3 := D.host.pde'_prime.two_le
  have := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h0 h1) h2) h3
  omega

/- English proof (translation)
Take `⟨C, ι, hpb, hact⟩` from `h`. Use `⟨C, ι, hpb, fun a => ?_⟩` and prove the remaining obligations. Establish `hN0 : (N : ℂ) ≠ 0` using `by exact_mod_cast hN`. Establish `key` using `hact ((N : ℤ) * a.1, (N : ℤ) * a.2)`. Establish `e1 : GlobalTheory.CompRat.wC H ((N : ℤ) * a.1, (N : ℤ) * a.2) = (N : ℂ) * GlobalTheory.CompRat.wC H a`.

Simplify using `only [GlobalTheory.CompRat.wC]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `key` using `[e1]`. Establish `e2 : GlobalTheory.CompRat.wC H (1, 0) * ((N : ℂ) * GlobalTheory.CompRat.wC H a) / (N : ℂ) = GlobalTheory.CompRat.wC H (1, 0) * GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ)`.

Rewrite using `[Nat.cast_one, div_one]`. Clear the denominators using the available nonvanishing facts. Establish `e3 : (N : ℂ) * GlobalTheory.CompRat.wC H a / (N : ℂ) = GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ)`. Rewrite using `[Nat.cast_one, div_one]`. Clear the denominators using the available nonvanishing facts.

Rewrite `key` using `[e2, e3]`. Conclude with `key`.
-/
theorem fixesCurve_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (τ : ℂ ≃+* ℂ)
    (N : ℕ) (hN : N ≠ 0) (h : GlobalTheory.CompRat.FixesCurve H τ N) : GlobalTheory.CompRat.FixesCurve H τ 1 := by
  obtain ⟨C, ι, hpb, hact⟩ := h
  refine ⟨C, ι, hpb, fun a => ?_⟩
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  have key := hact ((N : ℤ) * a.1, (N : ℤ) * a.2)
  have e1 : GlobalTheory.CompRat.wC H ((N : ℤ) * a.1, (N : ℤ) * a.2) = (N : ℂ) * GlobalTheory.CompRat.wC H a := by
    simp only [GlobalTheory.CompRat.wC]; push_cast; ring
  rw [e1] at key
  have e2 : GlobalTheory.CompRat.wC H (1, 0) * ((N : ℂ) * GlobalTheory.CompRat.wC H a) / (N : ℂ) =
      GlobalTheory.CompRat.wC H (1, 0) * GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  have e3 : (N : ℂ) * GlobalTheory.CompRat.wC H a / (N : ℂ) = GlobalTheory.CompRat.wC H a / ((1 : ℕ) : ℂ) := by
    rw [Nat.cast_one, div_one]; field_simp
  rw [e2, e3] at key
  exact key

/- English proof (translation)
Use `set N := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' with hNdef`. Establish `hN` using `three_le_mod D`. Set `Fc : IntermediateField ℚ ℂ` to `(embLL0 D).toRatAlgHom.fieldRange`. Set `σ : Fc →+* ℂ` to `Fc.val.toRingHom`. Establish `hRay' : RayIn D N σ.fieldRange`.

Take `⟨L, i1, i2, i3, i4, h1, jj, h2, h3⟩` from `hRay`. Use `⟨L, i1, i2, i3, i4, h1, jj, h2, fun x => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `h3 x`. Conclude with `⟨⟨jj x, ⟨y, hy⟩⟩, rfl⟩`. Establish `hC` using `GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hLaws.pins.1 N hN Fc σ hRay'`.

Establish `hfix` using `hC τ fun z hz => by`. Take `⟨y, hy⟩` from `hz`. Conclude with `hτ z ⟨y, hy⟩`. Conclude with `fixesCurve_one T.Q.H τ N (by omega) hfix`.
-/
theorem curve_fix (hRF : GlobalTheory.NT.RayField) (D : D7) (T : CoreJ D) (hLaws : LawsJ T)
    (hRay : RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange)
    (τ : ℂ ≃+* ℂ) (hτ : ∀ z ∈ (embLL0 D).fieldRange, τ z = z) : GlobalTheory.CompRat.FixesCurve T.Q.H τ 1 := by
  set N := D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde' with hNdef
  have hN := three_le_mod D
  let Fc : IntermediateField ℚ ℂ := (embLL0 D).toRatAlgHom.fieldRange
  let σ : Fc →+* ℂ := Fc.val.toRingHom
  have hRay' : RayIn D N σ.fieldRange := by
    obtain ⟨L, i1, i2, i3, i4, h1, jj, h2, h3⟩ := hRay
    refine ⟨L, i1, i2, i3, i4, h1, jj, h2, fun x => ?_⟩
    obtain ⟨y, hy⟩ := h3 x
    exact ⟨⟨jj x, ⟨y, hy⟩⟩, rfl⟩
  have hC := GlobalTheory.TwistRat.Field.curveOver_of_rayIn hRF D T.Q hLaws.pins.1 N hN Fc σ hRay'
  have hfix := hC τ fun z hz => by
    obtain ⟨y, hy⟩ := hz
    exact hτ z ⟨y, hy⟩
  exact fixesCurve_one T.Q.H τ N (by omega) hfix

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

/- English proof (translation)
Establish `hu : (C.mu0 i).UnrAt P` using `(C.isMu0 i).unr P fun k hk => hP (by`. Simplify using `only [Formalism.L2.Host.OverP] at hk`. Use `fin_cases k`. Use `push_cast`. Conclude with `Ideal.mul_mem_right _ _ hk`.

Use `push_cast`. Conclude with `Ideal.mul_mem_left _ _ hk)`. Establish `he : C.eta.UnrAt P` using `C.isEta.unr P`. Take `⟨y1, hy1⟩` from `hV.mu0 i P hu`. Take `⟨y2, hy2⟩` from `hV.eta P he`.

Use `⟨y1 * y2⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_inv₀, hy1, hy2]`. Establish `hN : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0`. Conclude with `(Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot)` after adjusting the coercions. Establish `hNn : (0 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ)` using `Nat.cast_nonneg _`.

Establish `hs : Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ≠ 0`. Rewrite using `[Real.sqrt_ne_zero hNn]`. Conclude with `hN`. Establish `hc : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((1 / 2 : ℝ) : ℂ)) = ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)⁻¹`. Rewrite using `[← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hNn, Real.sqrt_eq_rpow, Real.rpow_neg hNn, Complex.ofReal_inv]`.

Establish `hval : (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) = (((C.mu0 i).val P : ℂˣ) : ℂ) * (((C.eta).val P : ℂˣ) : ℂ)⁻¹` using `by show ((((C.mu0 i).val P * (C.eta.val P)⁻¹ : ℂˣ)) : ℂ) = _`. Rewrite using `[Units.val_mul, Units.val_inv_eq_inv_val]`. Rewrite using `[hval]`. Simplify using `only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one, hc]`. Establish `hne : (((C.eta).val P : ℂˣ) : ℂ) ≠ 0` using `Units.ne_zero _`.

Establish `hs' : ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hs`. Clear the denominators using the available nonvanishing facts.
-/
theorem split_mem (D : D7) (C : Formalism.L2.Host.CharFrame D) (hV : Formalism.L2.Host.ValLL0 D C) (i : Fin D.R.m)
    (P : Formalism.L2.DIV.Pl D.host.E) (hP : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ∈ (embLL0 D).fieldRange := by
  have hu : (C.mu0 i).UnrAt P := (C.isMu0 i).unr P fun k hk => hP (by
    simp only [Formalism.L2.Host.OverP] at hk
    fin_cases k
    · push_cast; exact Ideal.mul_mem_right _ _ hk
    · push_cast; exact Ideal.mul_mem_left _ _ hk)
  have he : C.eta.UnrAt P := C.isEta.unr P
  obtain ⟨y1, hy1⟩ := hV.mu0 i P hu
  obtain ⟨y2, hy2⟩ := hV.eta P he
  refine ⟨y1 * y2⁻¹, ?_⟩
  rw [map_mul, map_inv₀, hy1, hy2]
  have hN : (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.2 P.ne_bot)
  have hNn : (0 : ℝ) ≤ (Ideal.absNorm P.asIdeal : ℝ) := Nat.cast_nonneg _
  have hs : Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero hNn]; exact hN
  have hc : ((Ideal.absNorm P.asIdeal : ℕ) : ℂ) ^ (-((1 / 2 : ℝ) : ℂ)) =
      ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hNn, Real.sqrt_eq_rpow,
      Real.rpow_neg hNn, Complex.ofReal_inv]
  have hval : (((C.mu0 i * C.eta⁻¹).val P : ℂˣ) : ℂ) = (((C.mu0 i).val P : ℂˣ) : ℂ) * (((C.eta).val P : ℂˣ) : ℂ)⁻¹ := by
    show ((((C.mu0 i).val P * (C.eta.val P)⁻¹ : ℂˣ)) : ℂ) = _
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hval]
  simp only [Formalism.L2.Host.HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one, hc]
  have hne : (((C.eta).val P : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hs' : ((Real.sqrt (Ideal.absNorm P.asIdeal : ℝ) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs
  field_simp

end GlobalTheory.FixBaseSmall

namespace GlobalTheory.FixBaseSmall

/- English proof (translation)
Introduce `D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ hLaws hCore hFW hTie hgal hVal hRay hroots j τ hτ`. Use `⟨fun a => hτ _ (core_mem T Rl cG S YS hLaws hTie.alg j a), fun φ x => hτ _ (host_mem D hgal φ x), curve_fix hRF D T hLaws hRay τ hτ, fun P hP => hτ _ (split_mem D Rl.C hVal j P hP), fun PP hPP x => hτ _ (GlobalTheory.T.typePlace_residueCharacters_values_mem_smallField D Γ Pl0 I0 …` and prove the remaining obligations.
-/
theorem fixBase_of_fixes : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (τ : ℂ ≃+* ℂ), (∀ z ∈ (embLL0 D).fieldRange, τ z = z) → FixBase T Rl.toRealDat j τ := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ hLaws hCore hFW hTie hgal hVal hRay hroots j τ hτ
  refine ⟨fun a => hτ _ (core_mem T Rl cG S YS hLaws hTie.alg j a), fun φ x => hτ _ (host_mem D hgal φ x),
    curve_fix hRF D T hLaws hRay τ hτ, fun P hP => hτ _ (split_mem D Rl.C hVal j P hP),
    fun PP hPP x => hτ _ (GlobalTheory.T.typePlace_residueCharacters_values_mem_smallField D Γ Pl0 I0 T0 A3 T Rl cG S YS F hLaws hCore hgal hVal hroots j PP hPP x)⟩

end GlobalTheory.FixBaseSmall
