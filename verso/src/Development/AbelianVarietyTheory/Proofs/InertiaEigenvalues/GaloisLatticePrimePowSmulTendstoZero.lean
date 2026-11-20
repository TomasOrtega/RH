import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section
namespace GlobalTheory.TContNbhd

/- English proof (translation)
Set `f : R →+* (NormedField.valuation (K` to `C)).integer := (algebraMap R C).codRestrict _ (fun r => by`. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]`. Conclude with `hR r)`. Establish `h1 : IsIntegral (NormedField.valuation (K` using `C)).integer x := hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)`. Establish `h2` using `(Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1`.

Rewrite `h2` using `[Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]`. Conclude with `h2`.
-/
theorem norm_le_one_of_isIntegral' {R C : Type} [CommRing R] [NormedField C] [IsUltrametricDist C]
    [Algebra R C] (hR : ∀ r : R, ‖algebraMap R C r‖ ≤ 1) {x : C} (hx : IsIntegral R x) : ‖x‖ ≤ 1 := by
  let f : R →+* (NormedField.valuation (K := C)).integer :=
    (algebraMap R C).codRestrict _ (fun r => by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      exact hR r)
  have h1 : IsIntegral (NormedField.valuation (K := C)).integer x :=
    hx.map_of_comp_eq f (RingHom.id C) (by ext r; rfl)
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral h1
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe] at h2
  exact h2

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l)‖ ≤ 1`. Establish `: ((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l])` using `rfl`. Rewrite using `[this, norm_algebraMap']`. Conclude with `PadicInt.norm_le_one r`.
-/
theorem norm_algebraMap_le (LL : FinExt l) (r : ℤ_[l]) : ‖algebraMap ℤ_[l] ↥LL.1 r‖ ≤ 1 := by
  change ‖((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l)‖ ≤ 1
  have : ((algebraMap ℤ_[l] ↥LL.1 r : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (r : ℚ_[l]) := rfl
  rw [this, norm_algebraMap']
  exact PadicInt.norm_le_one r

/- English proof (translation)
The claim follows from `norm_le_one_of_isIntegral' (R := ℤ_[l]) (norm_algebraMap_le LL) c.2`.
-/
theorem norm_le_one_of_mem (LL : FinExt l) (c : ↥(OL LL)) : ‖(c : ↥LL.1)‖ ≤ 1 :=
  norm_le_one_of_isIntegral' (R := ℤ_[l]) (norm_algebraMap_le LL) c.2

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖((l : ↥LL.1) : PadicAlgCl l)‖ < 1`. Establish `: ((l : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l])` using `by simp`. Rewrite using `[this, norm_algebraMap']`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_natCast_lt_one (LL : FinExt l) : ‖(l : ↥LL.1)‖ < 1 := by
  change ‖((l : ↥LL.1) : PadicAlgCl l)‖ < 1
  have : ((l : ↥LL.1) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  rw [this, norm_algebraMap']
  exact Padic.norm_p_lt_one

/- English proof (translation)
Introduce `l _ LL T U hU`. Take `⟨s, hs⟩` from `T.L.fg`. Set `f : (↥s → ↥LL.1) → T.V` to `fun a => ∑ t : ↥s, a t • (t : T.V)`. Establish `hf : Continuous f` using `continuous_finset_sum _ fun t _ => (continuous_apply t).smul continuous_const`. Establish `h0 : f 0 = 0` using `by simp [f]`.

Establish `hpre : f ⁻¹' U ∈ nhds (0 : ↥s → ↥LL.1)` using `hf.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)`. Take `⟨ε, hε, hball⟩` from `Metric.mem_nhds_iff.1 hpre`. Take `⟨m, hm⟩` from `exists_pow_lt_of_lt_one hε (norm_natCast_lt_one LL)`. Use `⟨m, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite `hx` using `[← hs]`.

Take `⟨c, -, hc⟩` from `Submodule.mem_span_finset.1 hx`. Set `a : ↥s → ↥LL.1` to `fun t => (l : ↥LL.1) ^ m * ((c t : ↥(OL LL)) : ↥LL.1)`. Establish `ha : ‖a‖ < ε`. Use `(pi_norm_lt_iff hε).2 fun t => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hfa : f a = ((l : ↥LL.1) ^ m) • x`. Rewrite using `[← hc, Finset.smul_sum]`. Simplify using `only [f, a]`. Rewrite using `[← Finset.sum_coe_sort s]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations.

Rewrite using `[mul_smul]`. Use `congr 1`. Conclude with `algebraMap_smul (↥LL.1) (c t) (t : T.V)`. Establish `: a ∈ f ⁻¹' U` using `hball (mem_ball_zero_iff.2 ha)`. Rewrite `this` using `[Set.mem_preimage, hfa]`.

Conclude with `this`.
-/
theorem main : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (T : QLat LL) (U : Set T.V), U ∈ nhds (0 : T.V) → ∃ m : ℕ, ∀ x ∈ T.L.T, ((l : ↥LL.1) ^ m) • x ∈ U := by
  intro l _ LL T U hU
  classical
  obtain ⟨s, hs⟩ := T.L.fg
  let f : (↥s → ↥LL.1) → T.V := fun a => ∑ t : ↥s, a t • (t : T.V)
  have hf : Continuous f := continuous_finset_sum _ fun t _ => (continuous_apply t).smul continuous_const
  have h0 : f 0 = 0 := by simp [f]
  have hpre : f ⁻¹' U ∈ nhds (0 : ↥s → ↥LL.1) := hf.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hpre
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε (norm_natCast_lt_one LL)
  refine ⟨m, fun x hx => ?_⟩
  rw [← hs] at hx
  obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 hx
  let a : ↥s → ↥LL.1 := fun t => (l : ↥LL.1) ^ m * ((c t : ↥(OL LL)) : ↥LL.1)
  have ha : ‖a‖ < ε := by
    refine (pi_norm_lt_iff hε).2 fun t => ?_
    calc ‖a t‖ = ‖(l : ↥LL.1)‖ ^ m * ‖((c t : ↥(OL LL)) : ↥LL.1)‖ := by simp [a, norm_pow]
      _ ≤ ‖(l : ↥LL.1)‖ ^ m * 1 := by gcongr; exact norm_le_one_of_mem LL (c t)
      _ < ε := by rw [mul_one]; exact hm
  have hfa : f a = ((l : ↥LL.1) ^ m) • x := by
    rw [← hc, Finset.smul_sum]
    simp only [f, a]
    rw [← Finset.sum_coe_sort s]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_smul]
    congr 1
    exact algebraMap_smul (↥LL.1) (c t) (t : T.V)
  have : a ∈ f ⁻¹' U := hball (mem_ball_zero_iff.2 ha)
  rw [Set.mem_preimage, hfa] at this
  exact this
end GlobalTheory.TContNbhd
