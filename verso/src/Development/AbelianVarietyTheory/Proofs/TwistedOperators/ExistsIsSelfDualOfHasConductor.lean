import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AddCharConductorAndHaarIntegersExist

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.SplitWeil

variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {ψ : AddChar k Circle} {c : kˣ}

/- English proof (translation)
Use `t2Space k` as an intermediate fact. Establish `hcl : IsClosed (𝒪[k] : Set k)` using `(isCompact_int k).isClosed`. Establish `hclo : IsClopen (𝒪[k] : Set k)` using `⟨hcl, isOpen_int k⟩`. Use `set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf`. Establish `hfSB : f ∈ SB k`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hlc` using `(LocallyConstant.charFn ℂ hclo).isLocallyConstant`. Conclude with `hlc`. Conclude with `HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]`. Establish `hf0 : f 0 = 1` using `by simp [f]`.

Establish `hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal` using `measureReal_def ν _`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨-, hsd⟩`. Establish `e` using `(fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)`. Rewrite `e` using `[hf0, mul_one]`.

Rewrite using `[← hvol]`. Conclude with `e` after adjusting the coercions. Introduce `hC`. Use `⟨inferInstance, fun g hg => ?_⟩` and prove the remaining obligations. Rewrite using `[fourier_inversion ν h hg, hvol, hC]`.

Simplify using the standard rewrite rules.
-/
theorem isSelfDual_iff_vol (h : HasConductor ψ c) (ν : Measure k) [ν.IsAddHaarMeasure] :
    IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1 := by
  have := t2Space k
  have hcl : IsClosed (𝒪[k] : Set k) := (isCompact_int k).isClosed
  have hclo : IsClopen (𝒪[k] : Set k) := ⟨hcl, isOpen_int k⟩
  set f : k → ℂ := (𝒪[k] : Set k).indicator 1 with hf
  have hfSB : f ∈ SB k := by
    refine ⟨?_, ?_⟩
    · have hlc := (LocallyConstant.charFn ℂ hclo).isLocallyConstant
      exact hlc
    · exact HasCompactSupport.intro' (isCompact_int k) hcl fun x hx => by simp [f, hx]
  have hf0 : f 0 = 1 := by simp [f]
  have hvol : ν.real (𝒪[k] : Set k) = (ν (𝒪[k] : Set k)).toReal := measureReal_def ν _
  constructor
  · rintro ⟨-, hsd⟩
    have e := (fourier_inversion ν h hfSB).symm.trans (hsd f hfSB)
    rw [hf0, mul_one] at e
    rw [← hvol]
    exact_mod_cast e
  · intro hC
    refine ⟨inferInstance, fun g hg => ?_⟩
    rw [fourier_inversion ν h hg, hvol, hC]
    simp

/- English proof (translation)
Take `⟨ν₀, hH, h1⟩` from `exists_isUnitVol k`. Establish `hn : 0 < nabs k c` using `nabs_pos k c`. Use `set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha`. Establish `ha0 : a ≠ 0`. Introduce `h0`.

Establish `: (Real.sqrt (nabs k c))⁻¹ = 0` using `congrArg Subtype.val h0`. Establish `hs : 0 < Real.sqrt (nabs k c)` using `Real.sqrt_pos.2 hn`. Conclude with `(inv_pos.2 hs).ne' this`. Establish `: (a • ν₀).IsAddHaarMeasure` using `.nnreal_smul ν₀ ha0`. Use `⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩` and prove the remaining obligations.

Establish `hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹`. Rewrite using `[Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]`. Both sides reduce to the same expression. Rewrite using `[hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']`.
-/
theorem exists_isSelfDual_of_hasConductor (h : HasConductor ψ c) : ∃ ν : Measure k, IsSelfDual ψ ν := by
  obtain ⟨ν₀, hH, h1⟩ := exists_isUnitVol k
  have hn : 0 < nabs k c := nabs_pos k c
  set a : ℝ≥0 := ⟨(Real.sqrt (nabs k c))⁻¹, by positivity⟩ with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have : (Real.sqrt (nabs k c))⁻¹ = 0 := congrArg Subtype.val h0
    have hs : 0 < Real.sqrt (nabs k c) := Real.sqrt_pos.2 hn
    exact (inv_pos.2 hs).ne' this
  have : (a • ν₀).IsAddHaarMeasure := .nnreal_smul ν₀ ha0
  refine ⟨a • ν₀, (isSelfDual_iff_vol h _).2 ?_⟩
  have hval : ((a • ν₀) (𝒪[k] : Set k)).toReal = (Real.sqrt (nabs k c))⁻¹ := by
    rw [Measure.smul_apply, h1, ENNReal.smul_def, smul_eq_mul, mul_one, ENNReal.coe_toReal]
    rfl
  rw [hval, inv_pow, Real.sq_sqrt hn.le, inv_mul_cancel₀ hn.ne']

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Conclude with `isSelfDual_of_isUnitVol ν h`. Introduce `hsd`. Use `hsd.1` as an intermediate fact. Establish `e` using `(isSelfDual_iff_vol h ν).1 hsd`.

Rewrite `e` using `[nabs_one, mul_one]`. Establish `hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal` using `ENNReal.toReal_nonneg`. Establish `e1 : (ν (𝒪[k] : Set k)).toReal = 1` using `by nlinarith`. Conclude with `⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩`.
-/
theorem isUnitVol_iff_isSelfDual (h : HasConductor ψ 1) (ν : Measure k) : IsUnitVol ν ↔ IsSelfDual ψ ν := by
  constructor
  · exact isSelfDual_of_isUnitVol ν h
  · intro hsd
    have := hsd.1
    have e := (isSelfDual_iff_vol h ν).1 hsd
    rw [nabs_one, mul_one] at e
    have hnn : 0 ≤ (ν (𝒪[k] : Set k)).toReal := ENNReal.toReal_nonneg
    have e1 : (ν (𝒪[k] : Set k)).toReal = 1 := by nlinarith
    exact ⟨hsd.1, (ENNReal.toReal_eq_one_iff _).1 e1⟩

/- English proof (translation)
Introduce `k _ _ _ _ _ _ ψ hψ h1`. Use `⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `exists_hasConductor_of_continuous ψ hψ h1`. Conclude with `exists_isSelfDual_of_hasConductor hc`. Conclude with `isSelfDual_iff_vol hc ν`.
-/
theorem selfDual_measure : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : ψ ≠ 1), (∃ ν : Measure k, IsSelfDual ψ ν) ∧ (HasConductor ψ 1 → ∀ ν : Measure k, IsUnitVol ν ↔ IsSelfDual ψ ν) ∧ ∀ (c : kˣ) (ν : Measure k), HasConductor ψ c → ν.IsAddHaarMeasure → (IsSelfDual ψ ν ↔ (ν (𝒪[k] : Set k)).toReal ^ 2 * nabs k c = 1) := by
  intro k _ _ _ _ _ _ ψ hψ h1
  refine ⟨?_, fun h ν => isUnitVol_iff_isSelfDual h ν, fun c ν hc hν => ?_⟩
  · obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ h1
    exact exists_isSelfDual_of_hasConductor hc
  · exact isSelfDual_iff_vol hc ν

end GlobalTheory.SplitWeil
