import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAuxiliaryVectorWittDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralBasisCompletion
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceHermitianFrameProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLatti
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialIffGIntOfSuppAtSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PlaceIdempotentActsOnSupportedAndOffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationEqUniformizerAndUnitAtPrime
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open ValuativeRel

noncomputable section

namespace GlobalTheory.SplitPtLev

/- English proof (translation)
Introduce `D k _ _ _ _ p w he d m hm z hz`. Set `f : 𝓞 D.host.E → k` to `fun x => p.pr (incA D (x : D.host.E))`. Establish `fmul : ∀ x y, f (x * y) = f x * f y`. Introduce `x y`. Simplify using `only [f, map_mul]`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht, ht2⟩ : ∃ t ∈ w.asIdeal, t ∉ w.asIdeal ^ 2 := by`. Take `⟨t, ht, ht2⟩` from `Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1`. Conclude with `⟨t, by simpa using ht, ht2⟩`. Establish `h1w : (1 : 𝓞 D.host.E) ∉ w.asIdeal` using `fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)`. Take `⟨q, hq⟩` from `(GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t 1 ht ht2 h1w).1`.

Establish `hunit : ∀ x, x ∉ w.asIdeal → valuation k (f x) = 1` using `fun x hx => (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t x ht ht2 hx).2`. Choose the witnesses or unpack the hypotheses as in `⟨s, hs, hsw⟩ : ∃ s, s ∉ w.asIdeal ∧ ∀ x ∈ w.asIdeal, ∃ y, s * x = y * t := by`. Take `⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {t}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ht)`. Establish `hJw : ¬ J ≤ w.asIdeal`. Introduce `h`.

Apply `ht2` to reduce the goal to its premises. Establish `: Ideal.span {t} ≤ w.asIdeal ^ 2`. Rewrite using `[hJ, pow_two]`. Conclude with `Ideal.mul_mono_right h`. Conclude with `this (Ideal.mem_span_singleton_self t)`.

Take `⟨s, hsJ, hsw⟩` from `Set.not_subset.1 hJw`. Use `⟨s, hsw, fun x hx => ?_⟩` and prove the remaining obligations. Establish `: s * x ∈ Ideal.span {t}`. Rewrite using `[hJ, mul_comm s x]`. Conclude with `Ideal.mul_mem_mul hx hsJ`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨y, hy.symm⟩`. Establish `hq1 : valuation k ((q.1 : 𝒪[k]) : k) ≤ 1` using `(GlobalTheory.FinPl.SplitPt.val_unif_lt_one q).le`. Establish `key : ∀ n (x : 𝓞 D.host.E), x ∉ w.asIdeal ^ (n + 1) → valuation k ((q.1 : 𝒪[k]) : k) ^ n ≤ valuation k (f x)`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `x hx`. Rewrite using `[pow_zero, hunit x (by simpa using hx)]`. Consider the case `succ n ih`.

Introduce `x hx`. Distinguish the cases in `hxw : x ∈ w.asIdeal`. Take `⟨y, hy⟩` from `hsw x hxw`. Establish `hy' : y ∉ w.asIdeal ^ (n + 1)`. Introduce `hy1`.

Establish `hsx : s * x ∈ w.asIdeal ^ (n + 1 + 1)`. Rewrite using `[hy, pow_succ]`. Conclude with `Ideal.mul_mem_mul hy1 ht`. Break down `Ideal.IsPrime.mul_mem_pow w.asIdeal hsx with h | h` into its components or cases. Conclude with `hs h`.

Conclude with `hx h`. Establish `h1` using `congrArg (fun u => valuation k (f u)) hy`. Simplify using `only [fmul, Valuation.map_mul, hunit s hs, one_mul] at h1`. Rewrite using `[h1, ← hq, pow_succ]`. Rewrite using `[hq]`.

Conclude with `mul_le_mul_of_nonneg_right (ih y hy') zero_le'`. Rewrite using `[hunit x hxw]`. Conclude with `pow_le_one₀ zero_le' hq1`. Establish `hzle : ∀ n, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n, valuation k (z : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `z _`. Rewrite using `[pow_zero]`. Conclude with `z.2`.

Consider the case `succ n ih`. Introduce `z hz`. Rewrite `hz` using `[pow_succ]`. Use `Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)` and prove the remaining obligations. Establish `hy1 : valuation k (y : k) < 1`.

Establish `: y ∈ nonunits 𝒪[k]` using `(IsLocalRing.mem_maximalIdeal y).1 hy`. Conclude with `Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 this`. Rewrite using `[MulMemClass.coe_mul, Valuation.map_mul, pow_succ]`. Conclude with `mul_le_mul' (ih x hx) (GlobalTheory.FinPl.SplitPt.val_le_unif q hy1)`. Rewrite using `[AddMemClass.coe_add]`.

Conclude with `(Valuation.map_add _ _ _).trans (max_le hx hy)`. Establish `hmv` using `key d m hm`. Establish `hpos : 0 < valuation k (f m)` using `lt_of_lt_of_le (pow_pos (GlobalTheory.FinPl.SplitPt.val_unif_pos q) d) hmv`. Establish `hf0 : f m ≠ 0` using `fun h => by simp [h] at hpos`. Use `⟨(z : k) / f m, ?_, ?_⟩` and prove the remaining obligations.

Use `show valuation k ((z : k) / f m) ≤ 1`. Rewrite using `[map_div₀]`. Conclude with `div_le_one_of_le₀ ((hzle d z hz).trans hmv) zero_le'`. Conclude with `(div_mul_cancel₀ _ hf0).symm`.
-/
theorem dvd_of_mem_maxIdeal_pow : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : GlobalTheory.FinPl.SplitPt D k) (w : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt p.e w → ∀ (d : ℕ) (m : 𝓞 D.host.E),
  m ∉ w.asIdeal ^ (d + 1) → ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ d, ∃ c ∈ 𝒪[k], (z : k) = c * p.pr (incA D ((m : 𝓞 D.host.E) : D.host.E)) := by
  intro D k _ _ _ _ p w he d m hm z hz
  let f : 𝓞 D.host.E → k := fun x => p.pr (incA D (x : D.host.E))
  have fmul : ∀ x y, f (x * y) = f x * f y := by
    intro x y
    simp only [f, map_mul]
  obtain ⟨t, ht, ht2⟩ : ∃ t ∈ w.asIdeal, t ∉ w.asIdeal ^ 2 := by
    obtain ⟨t, ht, ht2⟩ := Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top 1
    exact ⟨t, by simpa using ht, ht2⟩
  have h1w : (1 : 𝓞 D.host.E) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  obtain ⟨q, hq⟩ := (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t 1 ht ht2 h1w).1
  have hunit : ∀ x, x ∉ w.asIdeal → valuation k (f x) = 1 := fun x hx =>
    (GlobalTheory.FinPl.SplitPt.val_eq_unif_and_unit D k p w he t x ht ht2 hx).2
  obtain ⟨s, hs, hsw⟩ : ∃ s, s ∉ w.asIdeal ∧ ∀ x ∈ w.asIdeal, ∃ y, s * x = y * t := by
    obtain ⟨J, hJ⟩ : w.asIdeal ∣ Ideal.span {t} :=
      Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 ht)
    have hJw : ¬ J ≤ w.asIdeal := by
      intro h
      apply ht2
      have : Ideal.span {t} ≤ w.asIdeal ^ 2 := by
        rw [hJ, pow_two]
        exact Ideal.mul_mono_right h
      exact this (Ideal.mem_span_singleton_self t)
    obtain ⟨s, hsJ, hsw⟩ := Set.not_subset.1 hJw
    refine ⟨s, hsw, fun x hx => ?_⟩
    have : s * x ∈ Ideal.span {t} := by
      rw [hJ, mul_comm s x]
      exact Ideal.mul_mem_mul hx hsJ
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨y, hy.symm⟩
  have hq1 : valuation k ((q.1 : 𝒪[k]) : k) ≤ 1 := (GlobalTheory.FinPl.SplitPt.val_unif_lt_one q).le
  have key : ∀ n (x : 𝓞 D.host.E), x ∉ w.asIdeal ^ (n + 1) →
      valuation k ((q.1 : 𝒪[k]) : k) ^ n ≤ valuation k (f x) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      rw [pow_zero, hunit x (by simpa using hx)]
    | succ n ih =>
      intro x hx
      by_cases hxw : x ∈ w.asIdeal
      · obtain ⟨y, hy⟩ := hsw x hxw
        have hy' : y ∉ w.asIdeal ^ (n + 1) := by
          intro hy1
          have hsx : s * x ∈ w.asIdeal ^ (n + 1 + 1) := by
            rw [hy, pow_succ]
            exact Ideal.mul_mem_mul hy1 ht
          rcases Ideal.IsPrime.mul_mem_pow w.asIdeal hsx with h | h
          · exact hs h
          · exact hx h
        have h1 := congrArg (fun u => valuation k (f u)) hy
        simp only [fmul, Valuation.map_mul, hunit s hs, one_mul] at h1
        rw [h1, ← hq, pow_succ]
        rw [hq]
        exact mul_le_mul_of_nonneg_right (ih y hy') zero_le'
      · rw [hunit x hxw]
        exact pow_le_one₀ zero_le' hq1
  have hzle : ∀ n, ∀ z ∈ IsLocalRing.maximalIdeal 𝒪[k] ^ n,
      valuation k (z : k) ≤ valuation k ((q.1 : 𝒪[k]) : k) ^ n := by
    intro n
    induction n with
    | zero =>
      intro z _
      rw [pow_zero]
      exact z.2
    | succ n ih =>
      intro z hz
      rw [pow_succ] at hz
      refine Submodule.mul_induction_on hz (fun x hx y hy => ?_) (fun x y hx hy => ?_)
      · have hy1 : valuation k (y : k) < 1 := by
          have : y ∈ nonunits 𝒪[k] := (IsLocalRing.mem_maximalIdeal y).1 hy
          exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.1 this
        rw [MulMemClass.coe_mul, Valuation.map_mul, pow_succ]
        exact mul_le_mul' (ih x hx) (GlobalTheory.FinPl.SplitPt.val_le_unif q hy1)
      · rw [AddMemClass.coe_add]
        exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  have hmv := key d m hm
  have hpos : 0 < valuation k (f m) :=
    lt_of_lt_of_le (pow_pos (GlobalTheory.FinPl.SplitPt.val_unif_pos q) d) hmv
  have hf0 : f m ≠ 0 := fun h => by simp [h] at hpos
  refine ⟨(z : k) / f m, ?_, ?_⟩
  · show valuation k ((z : k) / f m) ≤ 1
    rw [map_div₀]
    exact div_le_one_of_le₀ ((hzle d z hz).trans hmv) zero_le'
  · exact (div_mul_cancel₀ _ hf0).symm

end GlobalTheory.SplitPtLev
