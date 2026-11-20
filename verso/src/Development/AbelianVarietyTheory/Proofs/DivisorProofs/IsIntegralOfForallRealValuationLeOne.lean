import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

namespace GlobalTheory.DegVal

open IsDedekindDomain IsLocalRing

/- English proof (translation)
Establish `hne : maximalIdeal V ≠ ⊥` using `IsDiscreteValuationRing.not_a_field V`. Set `v : HeightOneSpectrum V` to `⟨maximalIdeal V, inferInstance, hne⟩`. Set `hmono` to `(WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))`. Use `⟨(v.valuation Ω).map (WithZeroMulInt.toNNReal (e := 2) (by norm_num)) hmono.monotone, fun x => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h` using `v.valuation_le_one (K := Ω) x`.

Use `hmono.monotone h` as an intermediate fact. Simplify using `using this`. Establish `h` using `(v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx`. Use `hmono h` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_realValuation_of_discreteValuationSubring {Ω : Type} [Field Ω]
    (V : ValuationSubring Ω) [IsDiscreteValuationRing V] :
    ∃ ν : Valuation Ω ℝ≥0, (∀ x : V, ν (x : Ω) ≤ 1) ∧ ∀ x ∈ maximalIdeal V, ν (x : Ω) < 1 := by
  have hne : maximalIdeal V ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  let v : HeightOneSpectrum V := ⟨maximalIdeal V, inferInstance, hne⟩
  let hmono := (WithZeroMulInt.toNNReal_strictMono (e := 2) (by norm_num))
  refine ⟨(v.valuation Ω).map (WithZeroMulInt.toNNReal (e := 2) (by norm_num)) hmono.monotone,
    fun x => ?_, fun x hx => ?_⟩
  · have h := v.valuation_le_one (K := Ω) x
    have := hmono.monotone h
    simpa using this
  · have h := (v.valuation_lt_one_iff_mem (K := Ω) x).mpr hx
    have := hmono h
    simpa using this

/- English proof (translation)
Introduce `K Ω _ _ _ _ hfg A hA t ht`. Assume the negation of the conclusion as `hn`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Conclude with `hn isIntegral_zero`.

Establish `: Algebra.EssFiniteType K Ω` using `IntermediateField.fg_top_iff.mp hfg`. Establish `: Algebra.EssFiniteType A Ω` using `.of_comp K A Ω`. Establish `: Algebra.FiniteType K A` using `(Subalgebra.fg_iff_finiteType A).mp hA`. Establish `: IsNoetherianRing A` using `Algebra.FiniteType.isNoetherianRing K A`. Establish `hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω` using `inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)`.

Take `⟨W, hW, htW⟩` from `Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn (R := (integralClosure A Ω).toSubring) (x := t) hn`. Establish `hinv : t⁻¹ ∈ W.nonunits` using `W.inv_mem_nonunits_iff.mpr (Or.inr htW)`. Take `⟨V, h1, h2, -, h3⟩` from `GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W (fun r => hW ((integralClosure A Ω).algebraMap_mem r)) Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv) ⟨_, rfl, inv_ne_zero ht0⟩`. Take `⟨ν, hν1, hνm⟩` from `exists_realValuation_of_discreteValuationSubring V`. Establish `hle : ν t ≤ 1` using `ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩`.

Establish `hn3 : t⁻¹ ∈ V.nonunits` using `h3 _ rfl`. Establish `htV : t⁻¹ ∈ V` using `(V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))`. Establish `hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V` using `(ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3`. Establish `hlt : ν t⁻¹ < 1` using `hνm _ hm`. Establish `h1' : ν (t * t⁻¹) = 1` using `by rw [mul_inv_cancel₀ ht0, map_one]`.

Rewrite `h1'` using `[map_mul]`. Establish `: ν t * ν t⁻¹ < 1` using `lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt`. Conclude with `absurd h1' this.ne`.
-/
theorem isIntegral_of_forall_realValuation_le_one : ∀ (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω], (⊤ : IntermediateField K Ω).FG → ∀ (A : Subalgebra K Ω), A.FG → ∀ t : Ω, (∀ ν : Valuation Ω ℝ≥0, (∀ a ∈ A, ν a ≤ 1) → ν t ≤ 1) → IsIntegral A t := by
  intro K Ω _ _ _ _ hfg A hA t ht
  by_contra hn
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact hn isIntegral_zero
  have : Algebra.EssFiniteType K Ω := IntermediateField.fg_top_iff.mp hfg
  have : Algebra.EssFiniteType A Ω := .of_comp K A Ω
  have : Algebra.FiniteType K A := (Subalgebra.fg_iff_finiteType A).mp hA
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  have hic : IsIntegrallyClosedIn (integralClosure A Ω).toSubring Ω :=
    inferInstanceAs (IsIntegrallyClosedIn (integralClosure A Ω) Ω)
  obtain ⟨W, hW, htW⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn
    (R := (integralClosure A Ω).toSubring) (x := t) hn
  have hinv : t⁻¹ ∈ W.nonunits := W.inv_mem_nonunits_iff.mpr (Or.inr htW)
  obtain ⟨V, h1, h2, -, h3⟩ := GlobalTheory.exists_discreteValuationSubring_of_valuationSubring (R := A) W
    (fun r => hW ((integralClosure A Ω).algebraMap_mem r))
    Set.finite_empty (Set.finite_singleton t⁻¹) (by simp) (by simpa using hinv)
    ⟨_, rfl, inv_ne_zero ht0⟩
  obtain ⟨ν, hν1, hνm⟩ := exists_realValuation_of_discreteValuationSubring V
  have hle : ν t ≤ 1 := ht ν fun a ha => hν1 ⟨a, h2 ⟨a, ha⟩⟩
  have hn3 : t⁻¹ ∈ V.nonunits := h3 _ rfl
  have htV : t⁻¹ ∈ V :=
    (V.valuation_le_one_iff _).mp (le_of_lt ((V.mem_nonunits_iff).mp hn3))
  have hm : (⟨t⁻¹, htV⟩ : V) ∈ maximalIdeal V :=
    (ValuationSubring.coe_mem_nonunits_iff (a := ⟨t⁻¹, htV⟩)).mp hn3
  have hlt : ν t⁻¹ < 1 := hνm _ hm
  have h1' : ν (t * t⁻¹) = 1 := by rw [mul_inv_cancel₀ ht0, map_one]
  rw [map_mul] at h1'
  have : ν t * ν t⁻¹ < 1 := lt_of_le_of_lt (mul_le_of_le_one_left zero_le hle) hlt
  exact absurd h1' this.ne

end GlobalTheory.DegVal
