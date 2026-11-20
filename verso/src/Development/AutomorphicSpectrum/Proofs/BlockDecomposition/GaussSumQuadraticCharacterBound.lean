import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaPartD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundUnitary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermInf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermOf
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopologyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatTuple
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SchwartzBruhatEqSumPure
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterArchimedeanFormStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StandardAdelicCharacterStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolumeStatement
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField
open GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl GlobalTheory.CompanionTheory.SW.Core

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl

/- English proof (translation)
Rewrite using `[← integral_indicator hA, ← integral_indicator hD, ← integral_add_left_eq_self (μ := m) (Set.indicator A f) g]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Distinguish the cases in `hy : y ∈ D`. Simplify using `[Set.indicator, hy, (h y).2 hy]`. Establish `: g + y ∉ A` using `fun hh => hy ((h y).1 hh)`.

Simplify using `[Set.indicator, hy, this]`.
-/
theorem setIntegral_translate_of_iff {X : Type} [AddCommGroup X] [TopologicalSpace X]
    [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (m : Measure X)
    [m.IsAddHaarMeasure] {A D : Set X} (hA : MeasurableSet A) (hD : MeasurableSet D) (g : X)
    (h : ∀ y, g + y ∈ A ↔ y ∈ D) (f : X → ℂ) :
    ∫ x in A, f x ∂m = ∫ y in D, f (g + y) ∂m := by
  rw [← integral_indicator hA, ← integral_indicator hD,
    ← integral_add_left_eq_self (μ := m) (Set.indicator A f) g]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  by_cases hy : y ∈ D
  · simp [Set.indicator, hy, (h y).2 hy]
  · have : g + y ∉ A := fun hh => hy ((h y).1 hh)
    simp [Set.indicator, hy, this]

/- English proof (translation)
Introduce `X _ _ _ _ _ _ _ m _ L hLc hLo q B hq hq1 hqB hB1 hB2 x₀`. Use `set C : Set X := {y | y - x₀ ∈ L} with hCdef`. Establish `hLm : MeasurableSet (L : Set X)` using `hLo.measurableSet`. Establish `hCo : IsOpen C` using `hLo.preimage (continuous_id.sub continuous_const)`. Establish `hCm : MeasurableSet C` using `hCo.measurableSet`.

Establish `hLfin : m (L : Set X) < ⊤` using `hLc.measure_lt_top`. Establish `hmC : m C = m (L : Set X)`. Establish `: C = (fun h => -x₀ + h) ⁻¹' (L : Set X)`. Use extensionality with `y`. Simplify using `[hCdef, sub_eq_neg_add]`.

Rewrite using `[this, measure_preimage_add]`. Establish `hCfin : m C < ⊤` using `hmC ▸ hLfin`. Use `haveI : IsFiniteMeasure (m.restrict C) := ⟨by simpa using hCfin⟩`. Use `haveI : IsFiniteMeasure (m.restrict (L : Set X)) := ⟨by simpa using hLfin⟩`. Establish `hq0 : ∀ x, q x ≠ 0` using `fun x h => by simpa [h] using hq1 x`.

Establish `hBnorm : ∀ x y, ‖B x y‖ = 1` using `fun x y => by`. Use `congrArg norm (hqB x y)` as an intermediate fact. Simplify `this.symm` using `[hq1]`. Establish `hBform : ∀ x y, B x y = q (x + y) / (q x * q y)` using `fun x y => by`. Rewrite using `[hqB x y]`.

Clear denominators, using `[hq0 x, hq0 y]` for the nonvanishing conditions. Establish `hBc : Continuous (Function.uncurry B)`. Establish `: Function.uncurry B = fun p : X × X => q (p.1 + p.2) / (q p.1 * q p.2)`. Use function extensionality and compare the values at `p`. Conclude with `hBform p.1 p.2`.

Rewrite using `[this]`. Conclude with `(hq.comp (continuous_fst.add continuous_snd)).div ((hq.comp continuous_fst).mul (hq.comp continuous_snd)) fun p => mul_ne_zero (hq0 _) (hq0 _)`. Establish `hconj : ∀ x, (starRingEnd ℂ) (q x) * q x = 1` using `fun x => by`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq1]`. Simplify using the standard rewrite rules.

Use `set I : ℂ := ∫ x in C, q x ∂m with hI`. Use `set J : X → ℂ := fun y => ∫ x in C, B x y ∂m with hJ`. Establish `hstep : I * (starRingEnd ℂ) I = ∫ y in (L : Set X), q y * J y ∂m`. Establish `h1 : I * (starRingEnd ℂ) I = ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m`. Rewrite using `[integral_mul_const, integral_conj, mul_comm]`.

Establish `h2 : ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m = ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m`. Use `setIntegral_congr_fun hCm fun x' hx' => ?_` and prove the remaining obligations. Establish `hx'' : x' - x₀ ∈ L` using `hx'`. Establish `ht : I = ∫ y in (L : Set X), q (x' + y) ∂m`. Use `setIntegral_translate_of_iff m hCm hLm x' (fun y => ?_) q` and prove the remaining obligations.

Establish `e : x' + y - x₀ = (x' - x₀) + y` using `by abel`. Simplify using `only [hCdef, Set.mem_setOf_eq, e, SetLike.mem_coe]`. Conclude with `L.add_mem_cancel_left hx''`. Rewrite using `[ht, ← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Use `beta_reduce`. Rewrite using `[hqB x' y]`. Combine the equalities or inequalities in the displayed calculation. Establish `h3 : ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m = ∫ y in (L : Set X), ∫ x' in C, q y * B x' y ∂m ∂m`. Use `integral_integral_swap ?_` and prove the remaining obligations.

Establish `hc : Continuous (Function.uncurry fun x' y => q y * B x' y)` using `(hq.comp continuous_snd).mul hBc`. Use `Integrable.of_bound hc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Simplify using `[Function.uncurry, hq1, hBnorm]`. Rewrite using `[h1, h2, h3]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations.

Simplify using `only [hJ]`. Rewrite using `[integral_const_mul]`. Establish `hJle : ∀ y, ‖J y‖ ≤ (m (L : Set X)).toReal` using `fun y => by`. Use `norm_setIntegral_le_of_norm_le_const (μ := m) (s := C) (f := fun x => B x y) (C := 1) hCfin (fun x _ => (hBnorm x y).le)` as an intermediate fact. Simplify `this` using `[Measure.real, hmC]`.

Establish `hJ0 : ∀ y l, l ∈ L → B l y ≠ 1 → J y = 0` using `fun y l hl hne => by`. Establish `ht : J y = ∫ x in C, B (l + x) y ∂m`. Use `setIntegral_translate_of_iff m hCm hCm l (fun x => ?_) (fun x => B x y)` and prove the remaining obligations. Establish `e : l + x - x₀ = l + (x - x₀)` using `by abel`. Simplify using `only [hCdef, Set.mem_setOf_eq, e]`.

Conclude with `L.add_mem_cancel_left hl`. Establish `h2 : J y = B l y * J y` using `by conv_lhs => rw [ht]`. Simplify using `only [hJ, hB1, integral_const_mul]`. Establish `h3 : (1 - B l y) * J y = 0` using `by rw [sub_mul, one_mul, ← h2, sub_self]`. Break down `mul_eq_zero.1 h3 with h | h` into its components or cases.

Conclude with `absurd (sub_eq_zero.1 h).symm hne`. Conclude with `h`. Use `set S : Set X := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS`. Establish `hSL : S ⊆ (L : Set X)` using `fun y hy => hy.1`. Establish `hSfin : m S < ⊤` using `(measure_mono hSL).trans_lt hLfin`.

Establish `hcut : ∫ y in (L : Set X), q y * J y ∂m = ∫ y in S, q y * J y ∂m`. Use `setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSL fun y hy => ?_` and prove the remaining obligations. Establish `: ¬ ∀ l ∈ L, B l y = 1` using `fun h => hy.2 ⟨hy.1, h⟩`. Use `push_neg at this`. Take `⟨l, hl, hne⟩` from `this`.

Simplify using `[hJ0 y l hl hne]`. Establish `hbound : ‖∫ y in S, q y * J y ∂m‖ ≤ (m (L : Set X)).toReal * (m S).toReal`. Use `norm_setIntegral_le_of_norm_le_const (μ := m) (s := S) (f := fun y => q y * J y) (C := (m (L : Set X)).toReal) hSfin (fun y _ => by simpa [hq1] using hJle y)` as an intermediate fact. Simplify `this` using `[Measure.real]`. Establish `hsq : ‖I‖ ^ 2 = ‖I * (starRingEnd ℂ) I‖`.

Rewrite using `[norm_mul, RCLike.norm_conj, sq]`. Rewrite using `[hsq, hstep, hcut]`. Conclude with `hbound`.
-/
theorem weyl_sq_compact_open : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (m : Measure X) [m.IsAddHaarMeasure]
    (L : AddSubgroup X), IsCompact (L : Set X) → IsOpen (L : Set X) →
    ∀ (q : X → ℂ) (B : X → X → ℂ), Continuous q → (∀ x, ‖q x‖ = 1) →
    (∀ x y, q (x + y) = q x * q y * B x y) →
    (∀ x x' y, B (x + x') y = B x y * B x' y) → (∀ x y y', B x (y + y') = B x y * B x y') →
    ∀ x₀ : X, ‖∫ x in {y | y - x₀ ∈ L}, q x ∂m‖ ^ 2 ≤
      (m (L : Set X)).toReal * (m {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1}).toReal := by
  intro X _ _ _ _ _ _ _ m _ L hLc hLo q B hq hq1 hqB hB1 hB2 x₀
  set C : Set X := {y | y - x₀ ∈ L} with hCdef
  have hLm : MeasurableSet (L : Set X) := hLo.measurableSet
  have hCo : IsOpen C := hLo.preimage (continuous_id.sub continuous_const)
  have hCm : MeasurableSet C := hCo.measurableSet
  have hLfin : m (L : Set X) < ⊤ := hLc.measure_lt_top
  have hmC : m C = m (L : Set X) := by
    have : C = (fun h => -x₀ + h) ⁻¹' (L : Set X) := by
      ext y; simp [hCdef, sub_eq_neg_add]
    rw [this, measure_preimage_add]
  have hCfin : m C < ⊤ := hmC ▸ hLfin
  haveI : IsFiniteMeasure (m.restrict C) := ⟨by simpa using hCfin⟩
  haveI : IsFiniteMeasure (m.restrict (L : Set X)) := ⟨by simpa using hLfin⟩
  have hq0 : ∀ x, q x ≠ 0 := fun x h => by simpa [h] using hq1 x
  have hBnorm : ∀ x y, ‖B x y‖ = 1 := fun x y => by
    have := congrArg norm (hqB x y)
    simpa [hq1] using this.symm
  have hBform : ∀ x y, B x y = q (x + y) / (q x * q y) := fun x y => by
    rw [hqB x y]; field_simp [hq0 x, hq0 y]
  have hBc : Continuous (Function.uncurry B) := by
    have : Function.uncurry B = fun p : X × X => q (p.1 + p.2) / (q p.1 * q p.2) := by
      funext p; exact hBform p.1 p.2
    rw [this]
    exact (hq.comp (continuous_fst.add continuous_snd)).div
      ((hq.comp continuous_fst).mul (hq.comp continuous_snd)) fun p => mul_ne_zero (hq0 _) (hq0 _)
  have hconj : ∀ x, (starRingEnd ℂ) (q x) * q x = 1 := fun x => by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hq1]; simp
  set I : ℂ := ∫ x in C, q x ∂m with hI
  set J : X → ℂ := fun y => ∫ x in C, B x y ∂m with hJ

  have hstep : I * (starRingEnd ℂ) I = ∫ y in (L : Set X), q y * J y ∂m := by
    have h1 : I * (starRingEnd ℂ) I = ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m := by
      rw [integral_mul_const, integral_conj, mul_comm]
    have h2 : ∫ x' in C, (starRingEnd ℂ) (q x') * I ∂m
        = ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m := by
      refine setIntegral_congr_fun hCm fun x' hx' => ?_
      have hx'' : x' - x₀ ∈ L := hx'
      have ht : I = ∫ y in (L : Set X), q (x' + y) ∂m := by
        refine setIntegral_translate_of_iff m hCm hLm x' (fun y => ?_) q
        have e : x' + y - x₀ = (x' - x₀) + y := by abel
        simp only [hCdef, Set.mem_setOf_eq, e, SetLike.mem_coe]
        exact L.add_mem_cancel_left hx''
      rw [ht, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      beta_reduce
      rw [hqB x' y]
      calc _ = ((starRingEnd ℂ) (q x') * q x') * (q y * B x' y) := by ring
        _ = _ := by rw [hconj, one_mul]
    have h3 : ∫ x' in C, ∫ y in (L : Set X), q y * B x' y ∂m ∂m
        = ∫ y in (L : Set X), ∫ x' in C, q y * B x' y ∂m ∂m := by
      refine integral_integral_swap ?_
      have hc : Continuous (Function.uncurry fun x' y => q y * B x' y) :=
        (hq.comp continuous_snd).mul hBc
      refine Integrable.of_bound hc.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun p => ?_)
      simp [Function.uncurry, hq1, hBnorm]
    rw [h1, h2, h3]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hJ]
    rw [integral_const_mul]
  have hJle : ∀ y, ‖J y‖ ≤ (m (L : Set X)).toReal := fun y => by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := C) (f := fun x => B x y) (C := 1)
      hCfin (fun x _ => (hBnorm x y).le)
    simpa [Measure.real, hmC] using this
  have hJ0 : ∀ y l, l ∈ L → B l y ≠ 1 → J y = 0 := fun y l hl hne => by
    have ht : J y = ∫ x in C, B (l + x) y ∂m := by
      refine setIntegral_translate_of_iff m hCm hCm l (fun x => ?_) (fun x => B x y)
      have e : l + x - x₀ = l + (x - x₀) := by abel
      simp only [hCdef, Set.mem_setOf_eq, e]
      exact L.add_mem_cancel_left hl
    have h2 : J y = B l y * J y := by
      conv_lhs => rw [ht]
      simp only [hJ, hB1, integral_const_mul]
    have h3 : (1 - B l y) * J y = 0 := by rw [sub_mul, one_mul, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h | h
    · exact absurd (sub_eq_zero.1 h).symm hne
    · exact h
  set S : Set X := {y | y ∈ L ∧ ∀ l ∈ L, B l y = 1} with hS
  have hSL : S ⊆ (L : Set X) := fun y hy => hy.1
  have hSfin : m S < ⊤ := (measure_mono hSL).trans_lt hLfin
  have hcut : ∫ y in (L : Set X), q y * J y ∂m = ∫ y in S, q y * J y ∂m := by
    refine setIntegral_eq_of_subset_of_forall_diff_eq_zero hLm hSL fun y hy => ?_
    have : ¬ ∀ l ∈ L, B l y = 1 := fun h => hy.2 ⟨hy.1, h⟩
    push_neg at this
    obtain ⟨l, hl, hne⟩ := this
    simp [hJ0 y l hl hne]
  have hbound : ‖∫ y in S, q y * J y ∂m‖ ≤ (m (L : Set X)).toReal * (m S).toReal := by
    have := norm_setIntegral_le_of_norm_le_const (μ := m) (s := S) (f := fun y => q y * J y)
      (C := (m (L : Set X)).toReal) hSfin (fun y _ => by simpa [hq1] using hJle y)
    simpa [Measure.real] using this
  have hsq : ‖I‖ ^ 2 = ‖I * (starRingEnd ℂ) I‖ := by
    rw [norm_mul, RCLike.norm_conj, sq]
  rw [hsq, hstep, hcut]
  exact hbound

end GlobalTheory.CompanionTheory.SiegelND.Integ.Weyl
