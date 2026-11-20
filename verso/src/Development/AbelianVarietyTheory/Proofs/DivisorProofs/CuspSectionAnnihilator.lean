import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecZEqZeroOfGenVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesOnEqModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingSectionsFiniteType
import Formalism.LocalToGlobal.ProjectiveLattices.TieGenDense

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore Filter Topology

namespace GlobalTheory.FlatCore

/- English proof (translation)
Use `haveI hJ : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)`. Establish `hrad : b ∉ (⊥ : Ideal R).jacobson`. Rewrite using `[← Ideal.radical_eq_jacobson]`. Introduce `h`. Take `⟨n, hn⟩` from `Ideal.mem_radical_iff.1 h`.

Conclude with `hb ⟨n, by simpa using hn⟩`. Rewrite `hrad` using `[Ideal.jacobson, Submodule.mem_sInf]`. Use `push_neg at hrad`. Take `⟨m, ⟨-, hm⟩, hbm⟩` from `hrad`. Use `letI : Field (R ⧸ m) := Ideal.Quotient.field m`.

Use `haveI : Algebra.FiniteType K (R ⧸ m) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective _ _)`. Use `haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)`. Use `haveI : Algebra.IsAlgebraic K (R ⧸ m) := Algebra.IsAlgebraic.of_finite K (R ⧸ m)`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Set `ψ : (R ⧸ m) →ₐ[K] ℂ` to `IsAlgClosed.lift`.

Use `⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a show ψ (Ideal.Quotient.mkₐ K m (algebraMap K R a)) = σ a`. Rewrite using `[AlgHom.commutes, AlgHom.commutes]`. Both sides reduce to the same expression. Use `show ψ (Ideal.Quotient.mk m b) ≠ 0`.

Rewrite using `[map_ne_zero_iff ψ ψ.toRingHom.injective]`. Conclude with `fun h => hbm (Ideal.Quotient.eq_zero_iff_mem.1 h)`.
-/
theorem exists_ringHom_ne_zero_of_not_isNilpotent {K R : Type} [Field K] [CommRing R] [Algebra K R]
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
theorem differentiableOn_of_mem_holSub {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {C : Type}
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
theorem genVal_ne_zero_of_mem_cuspOn (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) : genVal Z f ≠ 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  intro h0
  refine hf0 (secZ_eq_zero_of_genVal (cuspW_le_secZ G (Submodule.mem_inf.1 hf).1) fun Z' => ?_)
  by_cases hZ : Z' = Z
  · rw [hZ]; exact h0
  · rw [genVal_apply hG]; exact evC_eq_zero hG hZ (Submodule.mem_inf.1 hf).2

/- English proof (translation)
Establish `hG : GenFrEx Xo c` using `(GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1`. Establish `h1 : genVal Z s = 0`. Establish `h2` using `congrArg (genVal Z) hsf`. Rewrite `h2` using `[map_mul, map_zero]`. Conclude with `(mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn hf hf0)`.

Use `secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hZ : Z' = Z`. Rewrite using `[hZ, h1, mul_zero]`. Rewrite using `[genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]`.
-/
theorem idem_mul_eq_zero_of_mul_eq_zero (hf : f ∈ cuspOn U Z G) (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} {s : Rul Xo c}
    (hs : s ∈ secZ Xo c e') (hsf : s * f = 0) : idem Z * s = 0 := by
  have hG : GenFrEx Xo c := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  have h1 : genVal Z s = 0 := by
    have h2 := congrArg (genVal Z) hsf
    rw [map_mul, map_zero] at h2
    exact (mul_eq_zero.1 h2).resolve_right (genVal_ne_zero_of_mem_cuspOn hf hf0)
  refine secZ_eq_zero_of_genVal (mul_mem_secZ (idem_mem_secZ Z) hs) fun Z' => ?_
  rw [map_mul]
  by_cases hZ : Z' = Z
  · rw [hZ, h1, mul_zero]
  · rw [genVal_apply hG Z' (idem Z), evC_eq_zero hG hZ (idem_mem_suppOn Z), zero_mul]

/- English proof (translation)
Establish `hfs : f ∈ secZ Xo c (exZ Dw G)` using `cuspW_le_secZ G (Submodule.mem_inf.1 hf).1`. Take `⟨R, hR, t, hmem, hφ⟩` from `GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z`. Set `b : R` to `⟨_, hmem _ f hfs⟩`. Establish `hb : ¬ IsNilpotent b` using `fun h => by`. Establish `h2 : ((b : Om Z)) = 0` using `by rw [h.eq_zero]; rfl`.

Conclude with `genVal_ne_zero_of_mem_cuspOn hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))`. Take `⟨φ, hφσ, hφb⟩` from `exists_ringHom_ne_zero_of_not_isNilpotent σ hb`. Take `⟨z, hz, s, hread⟩` from `hφ φ hφσ`. Use `⟨z, hz, fun h0 => hφb ?_⟩` and prove the remaining obligations. Rewrite using `[hread _ f hfs b rfl, h0, mul_zero]`.
-/
theorem exists_framesOn_rdU_ne_zero (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) : ∃ z ∈ framesOn (U σ) Z, rdU (U σ) f z.1 z.2 ≠ 0 := by
  have hfs : f ∈ secZ Xo c (exZ Dw G) := cuspW_le_secZ G (Submodule.mem_inf.1 hf).1
  obtain ⟨R, hR, t, hmem, hφ⟩ :=
    GlobalTheory.DegCmp.exists_chart_read_at_frames E H Dw l Xo c r σ (U σ) (hL.unf σ hσ) Z
  let b : R := ⟨_, hmem _ f hfs⟩
  have hb : ¬ IsNilpotent b := fun h => by
    have h2 : ((b : Om Z)) = 0 := by rw [h.eq_zero]; rfl
    exact genVal_ne_zero_of_mem_cuspOn hf hf0 ((mul_eq_zero.1 h2).resolve_left (Units.ne_zero _))
  obtain ⟨φ, hφσ, hφb⟩ := exists_ringHom_ne_zero_of_not_isNilpotent σ hb
  obtain ⟨z, hz, s, hread⟩ := hφ φ hφσ
  refine ⟨z, hz, fun h0 => hφb ?_⟩
  rw [hread _ f hfs b rfl, h0, mul_zero]

/- English proof (translation)
Take `⟨k, hk⟩` from `framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ`. Establish `hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0`. Take `⟨⟨k₀, y₀⟩, hz₀, hne⟩` from `exists_framesOn_rdU_ne_zero hL hσ hf hf0`. Rewrite `hz₀` using `[hk]`. Take `⟨h1, hy₀⟩` from `hz₀`.

Substitute `h1` using the available equality. Conclude with `⟨y₀, hy₀, hne⟩`. Establish `hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom` using `differentiableOn_of_mem_holSub ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k`. Establish `hint` using `interior_closure_zero ((U σ).X k) hdiff hex`. Establish `hcont : ContinuousOn (fun y => rdU (U σ) s k y - q k y) ((U σ).X k).dom` using `(GlobalTheory.T.continuousOn_reading_integerExponent_section E H Dw l Xo c r U x hL e' he s hs σ hσ k).sub (hq k)`.

Establish `hO` using `FourierCoefficientDomain.isOpen_dom ((U σ).X k)`. Establish `key : ∀ y ∈ ((U σ).X k).dom, rdU (U σ) s k y = q k y`. Introduce `y hy`. Assume the negation of the conclusion as `hne`. Establish `hev : ∀ᶠ w in 𝓝 y, rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom` using `((hcont.continuousAt (hO.mem_nhds hy)).eventually_ne (sub_ne_zero.2 hne)).and (hO.mem_nhds hy)`.

Establish `hsub : {w | rdU (U σ) s k w - q k w ≠ 0 ∧ w ∈ ((U σ).X k).dom} ⊆ closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0}`. Introduce and unpack `w ⟨hw, hwd⟩`. Use `subset_closure ⟨hwd, ?_⟩` and prove the remaining obligations. Establish `h3` using `hrel ⟨k, w⟩ (by rw [hk]; exact ⟨rfl, hwd⟩)`. Rewrite `h3` using `[GlobalTheory.AllWt.rdU_mul (U σ)]`.

Establish `h2 : (rdU (U σ) s k w - q k w) * rdU (U σ) f k w = 0`. Rewrite using `[sub_mul, sub_eq_zero]`. Conclude with `h3`. Conclude with `(mul_eq_zero.1 h2).resolve_left hw`. Establish `hy' : y ∈ interior (closure {w | w ∈ ((U σ).X k).dom ∧ rdU (U σ) f k w = 0})` using `interior_mono hsub (mem_interior_iff_mem_nhds.2 hev)`.

Rewrite `hy'` using `[hint]`. Conclude with `hy'`. Introduce and unpack `⟨k', y⟩ hz`. Rewrite `hz` using `[hk]`. Take `⟨h1, hy⟩` from `hz`.

Substitute `h1` using the available equality. Conclude with `key y hy`.
-/
theorem rdU_eq_of_rdU_mul (hL : Laws U x) {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) (hf : f ∈ cuspOn U Z G)
    (hf0 : f ≠ 0) {e' : Ix Dw → ℤ} (he : e' none = 0) {s : Rul Xo c} (hs : s ∈ secZ Xo c e')
    (q : FDSec (U σ).X) (hq : ∀ k, ContinuousOn (q k) ((U σ).X k).dom)
    (hrel : ∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) :
    ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2 := by
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ hσ
  have hex : ∃ y ∈ ((U σ).X k).dom, rdU (U σ) f k y ≠ 0 := by
    obtain ⟨⟨k₀, y₀⟩, hz₀, hne⟩ := exists_framesOn_rdU_ne_zero hL hσ hf hf0
    rw [hk] at hz₀
    obtain ⟨h1, hy₀⟩ := hz₀
    subst h1
    exact ⟨y₀, hy₀, hne⟩
  have hdiff : DifferentiableOn ℂ (rdU (U σ) f k) ((U σ).X k).dom :=
    differentiableOn_of_mem_holSub ((mem_cuspW.1 (Submodule.mem_inf.1 hf).1).2 σ hσ) k
  have hint := interior_closure_zero ((U σ).X k) hdiff hex
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
Introduce `E _ _ _ H Dw l Xo c r U x hL Z G e' f s hf hf0 hs`. Conclude with `⟨idem_mul_eq_zero_of_mul_eq_zero hf hf0 hs, fun he σ hσ q hq hrel => rdU_eq_of_rdU_mul hL hσ hf hf0 he hs q hq hrel⟩`.
-/
theorem cuspOn_cancel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (G : WTZ E) (e' : Ix Dw → ℤ) (f s : Rul Xo c), f ∈ cuspOn U Z G → f ≠ 0 → s ∈ secZ Xo c e' → (s * f = 0 → idem Z * s = 0) ∧ (e' none = 0 → ∀ σ, GoodEmb c σ → ∀ (q : FDSec (U σ).X), (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) (s * f) z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∀ z ∈ framesOn (U σ) Z, rdU (U σ) s z.1 z.2 = q z.1 z.2) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z G e' f s hf hf0 hs
  exact ⟨idem_mul_eq_zero_of_mul_eq_zero hf hf0 hs,
    fun he σ hσ q hq hrel => rdU_eq_of_rdU_mul hL hσ hf hf0 he hs q hq hrel⟩

end GlobalTheory.FlatCore

end
