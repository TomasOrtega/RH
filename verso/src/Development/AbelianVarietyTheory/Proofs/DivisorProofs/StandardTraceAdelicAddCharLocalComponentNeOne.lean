import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAddCharSymplecticLocalLatticeEqOne
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.PsiNontriv

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels WithZero
open scoped nonZeroDivisors

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC`. Use `set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN`. Establish `hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0` using `by simpa using v.ne_bot`. Use `set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI`. Establish `hI0 : I ≠ 0` using `inv_ne_zero (pow_ne_zero _ hP)`.

Establish `hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0`. Introduce `w`. Rewrite using `[hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]`. Use `split_ifs with hw`. Substitute `hw` using the available equality.

Rewrite using `[FractionalIdeal.count_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1`.

Introduce `z hz w hw`. Use `(GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w` as an intermediate fact. Rewrite `this` using `[hcount w, if_neg hw, neg_zero, exp_zero]`. Then use the resulting hypothesis. Assume the negation of the conclusion as `H`. Use `push_neg at H`.

Establish `hle : I ≤ C`. Introduce `x hx`. Rewrite using `[hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]`. Introduce `a ha`. Take `⟨a, rfl⟩` from `(FractionalIdeal.mem_one_iff _).1 ha`.

Rewrite using `[Algebra.traceForm_apply]`. Establish `hxa : x * algebraMap (𝓞 F) F a ∈ I`. Rewrite using `[mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ a hx`. Conclude with `H _ (hint _ hxa)`.

Use `FractionalIdeal.count_mono F v hI0 hle` as an intermediate fact. Rewrite `this` using `[hcount v, if_pos rfl]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_trace_not_int (v : HeightOneSpectrum (𝓞 F)) :
    ∃ z : F, (∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1) ∧
      Algebra.trace ℚ F z ∉ (algebraMap ℤ ℚ).range := by
  classical
  set C : FractionalIdeal (𝓞 F)⁰ F := FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hC
  set N : ℕ := (-(FractionalIdeal.count F v C)).toNat + 1 with hN
  have hP : ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F)) ≠ 0 := by simpa using v.ne_bot
  set I : FractionalIdeal (𝓞 F)⁰ F := ((v.asIdeal : FractionalIdeal (𝓞 F)⁰ F) ^ N)⁻¹ with hI
  have hI0 : I ≠ 0 := inv_ne_zero (pow_ne_zero _ hP)
  have hcount : ∀ w, FractionalIdeal.count F w I = if w = v then -(N : ℤ) else 0 := by
    intro w
    rw [hI, FractionalIdeal.count_inv, FractionalIdeal.count_pow]
    split_ifs with hw
    · subst hw; rw [FractionalIdeal.count_self]; ring
    · rw [FractionalIdeal.count_maximal_coprime F w (Ne.symm hw)]; ring
  have hint : ∀ z ∈ I, ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v → w.valuation F z ≤ 1 := by
    intro z hz w hw
    have := (GlobalTheory.Idele.mem_iff_valuation_le hI0 z).1 hz w
    rwa [hcount w, if_neg hw, neg_zero, exp_zero] at this
  by_contra H
  push_neg at H
  have hle : I ≤ C := by
    intro x hx
    rw [hC, FractionalIdeal.mem_dual (one_ne_zero (α := FractionalIdeal (𝓞 F)⁰ F))]
    intro a ha
    obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
    rw [Algebra.traceForm_apply]
    have hxa : x * algebraMap (𝓞 F) F a ∈ I := by
      rw [mul_comm, ← Algebra.smul_def]
      exact Submodule.smul_mem _ a hx
    exact H _ (hint _ hxa)
  have := FractionalIdeal.count_mono F v hI0 hle
  rw [hcount v, if_pos rfl] at this
  omega

/- English proof (translation)
Introduce `F _ _ ψ hψ v h1`. Take `⟨z, hz, hzt⟩` from `exists_trace_not_int (F := F) v`. Establish `hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1` using `fun t => by`. Rewrite using `[← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]`. Use `set zv : Fv F v := algebraMap F (Fv F v) z with hzv`.

Use `set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα`. Establish `hαint : α ∈ intAf F`. Introduce `w`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality.

Rewrite using `[hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]`. Establish `: Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv` using `rfl`. Rewrite using `[this, sub_self]`. Conclude with `zero_mem _`. Rewrite using `[hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]`.

Establish `: Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z` using `rfl`. Rewrite using `[this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]`. Conclude with `hz w hw`. Establish `htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k`. Introduce `a`.

Establish `hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1))`. Rewrite using `[mul_one]`. Conclude with `Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Conclude with `⟨k, by rw [← hk]; simp⟩`.

Establish `h0` using `GlobalTheory.LatVacArith.psi_int hψ 1 htr α hαint`. Rewrite `h0` using `[map_one, mul_one]`. Establish `hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv`. Use `Prod.ext (add_zero (0 : Ainf F)).symm ?_` and prove the remaining obligations. Use `show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv`.

Rewrite using `[hα, sub_add_cancel]`. Establish `hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1`. Rewrite using `[hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]`. Rewrite `hval` using `[GlobalTheory.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff]`. Take `⟨n, hn⟩` from `hval`.

Apply `hzt` to reduce the goal to its premises. Use `⟨n, ?_⟩` and prove the remaining obligations. Establish `hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ)`. Establish `h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0` using `Complex.two_pi_I_ne_zero`. Apply `mul_left_cancel₀ h2` to reduce the goal to its premises.

Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[eq_intCast]`. Conclude with `hc.symm` after adjusting the coercions.
-/
theorem psiV_ne_one : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, GlobalTheory.VacAny.psiV ψ v ≠ 1 := by
  intro F _ _ ψ hψ v h1
  obtain ⟨z, hz, hzt⟩ := exists_trace_not_int (F := F) v
  have hloc : ∀ t : Fv F v, ψ (GlobalTheory.EmbChart.atPlace v t) = 1 := fun t => by
    rw [← GlobalTheory.VacAny.psiV_apply, h1, AddChar.one_apply]
  set zv : Fv F v := algebraMap F (Fv F v) z with hzv
  set α : Af F := algebraMap F (Af F) z - GlobalTheory.AdelicU.singleFin v zv with hα
  have hαint : α ∈ intAf F := by
    intro w
    by_cases hw : w = v
    · subst hw
      rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_self]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = zv := rfl
      rw [this, sub_self]
      exact zero_mem _
    · rw [hα, map_sub, GlobalTheory.AdelicU.evalV_singleFin_ne hw, sub_zero]
      have : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F w (algebraMap F (Af F) z) = algebraMap F (Fv F w) z := rfl
      rw [this, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.Idele.valued_algebraMap]
      exact hz w hw
  have htr : ∀ a : 𝓞 F, ∃ k : ℤ, Algebra.trace ℚ F ((a : F) * 1) = k := by
    intro a
    have hi : IsIntegral ℤ (Algebra.trace ℚ F ((a : F) * 1)) := by
      rw [mul_one]
      exact Algebra.isIntegral_trace (NumberField.RingOfIntegers.isIntegral_coe a)
    obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact ⟨k, by rw [← hk]; simp⟩
  have h0 := GlobalTheory.LatVacArith.psi_int hψ 1 htr α hαint
  rw [map_one, mul_one] at h0
  have hsplit : pairA F 0 (algebraMap F (Af F) z) = pairA F 0 α + GlobalTheory.EmbChart.atPlace v zv := by
    refine Prod.ext (add_zero (0 : Ainf F)).symm ?_
    show algebraMap F (Af F) z = α + GlobalTheory.AdelicU.singleFin v zv
    rw [hα, sub_add_cancel]
  have hval : ψ (pairA F 0 (algebraMap F (Af F) z)) = 1 := by
    rw [hsplit, AddChar.map_add_eq_mul, h0, hloc, one_mul]
  rw [GlobalTheory.LatVacArith.psi_fin_rat hψ, Complex.exp_eq_one_iff] at hval
  obtain ⟨n, hn⟩ := hval
  apply hzt
  refine ⟨n, ?_⟩
  have hc : ((Algebra.trace ℚ F z : ℚ) : ℂ) = (n : ℂ) := by
    have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    apply mul_left_cancel₀ h2
    rw [hn]; ring
  rw [eq_intCast]
  exact_mod_cast hc.symm

end GlobalTheory.PsiNontriv
