import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.LatticeAndConstantUnique

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair ValuativeRel NumberField Filter
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FinPl.AlmostAll

/- English proof (translation)
Use `⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]`. Conclude with `hc`. Take `⟨c', hc'⟩` from `Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))`. Conclude with `⟨c', by rw [← hc', mul_comm]⟩`.
-/
theorem exists_nat_eq_mul {E : Type} [Field E] [NumberField E] {c : 𝓞 E} (hc : c ≠ 0) :
    ∃ n : ℕ, n ≠ 0 ∧ ∃ c' : 𝓞 E, (n : 𝓞 E) = c * c' := by
  refine ⟨Ideal.absNorm (Ideal.span {c}), ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc
  · obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {c}))
    exact ⟨c', by rw [← hc', mul_comm]⟩

/- English proof (translation)
Take `⟨d, hd, hint⟩` from `I.isFractional`. Take `⟨N, hN, d', hdd'⟩` from `exists_nat_eq_mul (nonZeroDivisors.ne_zero hd)`. Establish `hsub : (I : Submodule (𝓞 E) E) ≠ ⊥` using `FractionalIdeal.coeToSubmodule_ne_bot.2 hI`. Take `⟨x, hxI, hx0⟩` from `(Submodule.ne_bot_iff _).1 hsub`. Take `⟨⟨r, s⟩, hrs⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 E)) x`.

Simplify using `only at hrs`. Establish `hs0 : algebraMap (𝓞 E) E (s : 𝓞 E) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero s.2)`. Establish `hr0 : r ≠ 0`. Introduce and unpack `rfl`. Rewrite `hrs` using `[map_zero, mul_eq_zero]`.

Conclude with `hrs.elim hx0 hs0`. Establish `hrI : algebraMap (𝓞 E) E r ∈ (I : Submodule (𝓞 E) E)`. Rewrite using `[← hrs, mul_comm, ← Algebra.smul_def]`. Conclude with `Submodule.smul_mem _ _ hxI`. Take `⟨M, hM, r', hrr'⟩` from `exists_nat_eq_mul hr0`.

Use `⟨N, M, hN, hM, fun a ha => ?_, ?_⟩` and prove the remaining obligations. Take `⟨b, hb⟩` from `hint a (FractionalIdeal.mem_coe.2 ha)`. Use `⟨d' * b, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_comm d' d, ← hdd', map_natCast]`. Establish `: (M : E) = r' • algebraMap (𝓞 E) E r`.

Rewrite using `[Algebra.smul_def, ← map_mul, mul_comm r' r, ← hrr', map_natCast]`. Rewrite using `[← FractionalIdeal.mem_coe, this]`. Conclude with `Submodule.smul_mem _ _ hrI`.
-/
theorem exists_nat_bounds {E : Type} [Field E] [NumberField E]
    {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E} (hI : I ≠ 0) :
    ∃ N M : ℕ, N ≠ 0 ∧ M ≠ 0 ∧ (∀ a ∈ I, ∃ b : 𝓞 E, (N : E) * a = algebraMap (𝓞 E) E b) ∧ (M : E) ∈ I := by
  obtain ⟨d, hd, hint⟩ := I.isFractional
  obtain ⟨N, hN, d', hdd'⟩ := exists_nat_eq_mul (nonZeroDivisors.ne_zero hd)
  have hsub : (I : Submodule (𝓞 E) E) ≠ ⊥ := FractionalIdeal.coeToSubmodule_ne_bot.2 hI
  obtain ⟨x, hxI, hx0⟩ := (Submodule.ne_bot_iff _).1 hsub
  obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) x
  simp only at hrs
  have hs0 : algebraMap (𝓞 E) E (s : 𝓞 E) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).2 (nonZeroDivisors.ne_zero s.2)
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, mul_eq_zero] at hrs
    exact hrs.elim hx0 hs0
  have hrI : algebraMap (𝓞 E) E r ∈ (I : Submodule (𝓞 E) E) := by
    rw [← hrs, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ hxI
  obtain ⟨M, hM, r', hrr'⟩ := exists_nat_eq_mul hr0
  refine ⟨N, M, hN, hM, fun a ha => ?_, ?_⟩
  · obtain ⟨b, hb⟩ := hint a (FractionalIdeal.mem_coe.2 ha)
    refine ⟨d' * b, ?_⟩
    rw [map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, mul_comm d' d, ← hdd', map_natCast]
  · have : (M : E) = r' • algebraMap (𝓞 E) E r := by
      rw [Algebra.smul_def, ← map_mul, mul_comm r' r, ← hrr', map_natCast]
    rw [← FractionalIdeal.mem_coe, this]
    exact Submodule.smul_mem _ _ hrI

/- English proof (translation)
Establish `h0 : (N : 𝓞 F) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `hI : Ideal.span {(N : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]` and apply the resulting hypothesis. Use `Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset ?_)` and prove the remaining obligations. Introduce `v hv`.

Simplify using `only [Set.mem_setOf_eq, not_not] at hv ⊢`. Rewrite using `[Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hv`.
-/
theorem eventually_notMem {F : Type} [Field F] [NumberField F] {N : ℕ} (hN : N ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (N : 𝓞 F) ∉ v.asIdeal := by
  have h0 : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hI : Ideal.span {(N : 𝓞 F)} ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors hI).subset ?_)
  intro v hv
  simp only [Set.mem_setOf_eq, not_not] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

/- English proof (translation)
Establish `h1 : v.valuation F (N : F) = 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `HeightOneSpectrum.intValuation_eq_one_iff.2 hv`. Establish `h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1`. Rewrite using `[← h1]`.

Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]`.
-/
theorem inv_mem_integers {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) : algebraMap F (Fv F v) (N : F)⁻¹ ∈ v.adicCompletionIntegers F := by
  have h1 : v.valuation F (N : F) = 1 := by
    rw [← map_natCast (algebraMap (𝓞 F) F), HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv
  have h2 : Valued.v (algebraMap F (Fv F v) (N : F)) = 1 := by
    rw [← h1]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (N : F)
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, map_inv₀, h2, inv_one]

/- English proof (translation)
Establish `key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α`. Introduce `w`. Rewrite using `[map_smul, Algebra.smul_def]`. Establish `hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F` using `hα`. Use `⟨fun w => ?_, fun w hw => ?_⟩` and prove the remaining obligations.

Rewrite using `[key]`. Distinguish the cases in `hw : w = v`. Substitute `hw` using the available equality. Conclude with `mul_mem (inv_mem_integers hv) (hα' w)`. Rewrite using `[h0 w hw, mul_zero]`.

Conclude with `zero_mem _`. Rewrite using `[key, h0 w hw, mul_zero]`.
-/
theorem smul_inv_mem {F : Type} [Field F] [NumberField F] {N : ℕ} {v : HeightOneSpectrum (𝓞 F)}
    (hv : (N : 𝓞 F) ∉ v.asIdeal) {α : Af F} (hα : α ∈ intAf F) (h0 : ∀ w, ¬ w = v → evalV F w α = 0) :
    (N : F)⁻¹ • α ∈ intAf F ∧ ∀ w, ¬ w = v → evalV F w ((N : F)⁻¹ • α) = 0 := by
  have key : ∀ w, evalV F w ((N : F)⁻¹ • α) = algebraMap F (Fv F w) (N : F)⁻¹ * evalV F w α := by
    intro w
    rw [map_smul, Algebra.smul_def]
  have hα' : ∀ w, evalV F w α ∈ w.adicCompletionIntegers F := hα
  refine ⟨fun w => ?_, fun w hw => ?_⟩
  · rw [key]
    by_cases hw : w = v
    · subst hw
      exact mul_mem (inv_mem_integers hv) (hα' w)
    · rw [h0 w hw, mul_zero]
      exact zero_mem _
  · rw [key, h0 w hw, mul_zero]

/- English proof (translation)
Use `show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)`. Rewrite using `[Prod.smul_mk, smul_zero]`.
-/
theorem pairA_smul {F : Type} [Field F] [NumberField F] (c : F) (α : Af F) :
    pairA F 0 (c • α) = c • pairA F 0 α := by
  show ((0 : Ainf F), c • α) = c • ((0 : Ainf F), α)
  rw [Prod.smul_mk, smul_zero]

/- English proof (translation)
Establish `hN' : (N : F) ≠ 0` using `Nat.cast_ne_zero.2 hN`. Establish `hz : (N : E) * z = (N : F) • z`. Rewrite using `[Algebra.smul_def, map_natCast]`. Rewrite using `[hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul, mul_inv_cancel₀ hN', one_smul]`.
-/
theorem tmul_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {N : ℕ} (hN : N ≠ 0) (α : Af F) (z : E) :
    pairA F 0 α ⊗ₜ[F] z = pairA F 0 ((N : F)⁻¹ • α) ⊗ₜ[F] ((N : E) * z) := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hz : (N : E) * z = (N : F) • z := by
    rw [Algebra.smul_def, map_natCast]
  rw [hz, TensorProduct.tmul_smul, TensorProduct.smul_tmul', ← pairA_smul, smul_smul,
    mul_inv_cancel₀ hN', one_smul]

/- English proof (translation)
Take `⟨N, M, hN, hM, hNI, hMI⟩` from `exists_nat_bounds (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)`. Use `filter_upwards [eventually_notMem (F := D.host.F) hN, eventually_notMem (F := D.host.F) hM] with v hvN hvM`. Introduce `S L`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[latA, latMul, AddSubgroup.closure_le]`.

Introduce and unpack `y ⟨α, hα, h0, a, ha, x, hx, rfl⟩`. Take `⟨b, hb⟩` from `hNI a ha`. Take `⟨hα', h0'⟩` from `smul_inv_mem hvN hα h0`. Rewrite using `[latV, latMul]`. Use `AddSubgroup.subset_closure ⟨(N : D.host.F)⁻¹ • α, hα', h0', 1, rfl, b • x, L.smul_mem b hx, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Establish `e : (N : D.host.E) * (a * x i) = 1 * (b • x) i`. Rewrite using `[one_mul, Pi.smul_apply, Algebra.smul_def, ← hb, mul_assoc]`. Rewrite using `[tmul_eq hN α (a * x i), e]`. Rewrite using `[latV, latMul, AddSubgroup.closure_le]`.

Introduce and unpack `y ⟨α, hα, h0, a, ha, x, hx, rfl⟩`. Rewrite `ha` using `[Set.mem_singleton_iff]`. Substitute `ha` using the available equality. Take `⟨hα', h0'⟩` from `smul_inv_mem hvM hα h0`. Rewrite using `[latA, latMul]`.

Use `AddSubgroup.subset_closure ⟨(M : D.host.F)⁻¹ • α, hα', h0', (M : D.host.E), hMI, x, hx, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Rewrite using `[one_mul, tmul_eq hM α (x i)]`.
-/
theorem latA_eq_latV (D : D7) :
    ∀ᶠ v : Pl D in cofinite, ∀ (S : HSp D) (L : Lat S), latA S L (· = v) = latV S L (· = v) := by
  obtain ⟨N, M, hN, hM, hNI, hMI⟩ := exists_nat_bounds (GlobalTheory.ModelLatticeCheck.AA_ne_zero D)
  filter_upwards [eventually_notMem (F := D.host.F) hN, eventually_notMem (F := D.host.F) hM]
    with v hvN hvM
  intro S L
  apply le_antisymm
  · rw [latA, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    obtain ⟨b, hb⟩ := hNI a ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvN hα h0
    rw [latV, latMul]
    refine AddSubgroup.subset_closure ⟨(N : D.host.F)⁻¹ • α, hα', h0', 1, rfl, b • x, L.smul_mem b hx, ?_⟩
    funext i
    have e : (N : D.host.E) * (a * x i) = 1 * (b • x) i := by
      rw [one_mul, Pi.smul_apply, Algebra.smul_def, ← hb, mul_assoc]
    rw [tmul_eq hN α (a * x i), e]
  · rw [latV, latMul, AddSubgroup.closure_le]
    rintro y ⟨α, hα, h0, a, ha, x, hx, rfl⟩
    rw [Set.mem_singleton_iff] at ha
    subst ha
    obtain ⟨hα', h0'⟩ := smul_inv_mem hvM hα h0
    rw [latA, latMul]
    refine AddSubgroup.subset_closure ⟨(M : D.host.F)⁻¹ • α, hα', h0', (M : D.host.E), hMI, x, hx, ?_⟩
    funext i
    rw [one_mul, tmul_eq hM α (x i)]

end GlobalTheory.FinPl.AlmostAll
end
