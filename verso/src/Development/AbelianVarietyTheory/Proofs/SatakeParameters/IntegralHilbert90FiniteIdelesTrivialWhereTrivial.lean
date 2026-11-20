import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TrueColumnChoicesHeckeCharReferenceEqOne
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfCongSet
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.H90RangeEqNormOneOfIsQuad
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteAdeleFieldIdentificationEqBaseChangeRingEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegralHilbert90DetHostField
open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwU.IntegralHilbert90Unramified
open GlobalTheory.AdeleBaseChange GlobalTheory.TwU.IntegralHilbert90

/- English proof (translation)
Establish `hD0 : Ideal.span {((D : ℕ) : 𝓞 F)} ≠ 0`. Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hD.ne'` after adjusting the coercions. Establish `hfin` using `Ideal.finite_factors hD0`. Use `⟨⟨fun v => algebraMap F (v.adicCompletion F) (r v), Filter.eventually_cofinite.2 (hfin.subset fun v hv => ?_)⟩, fun v => rfl⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_setOf_eq] at hv ⊢`. Rewrite using `[Ideal.dvd_span_singleton]`. Assume the negation of the conclusion as `hDv`. Apply `hv` to reduce the goal to its premises. Rewrite using `[SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `hv1 : v.valuation F (algebraMap (𝓞 F) F (D : 𝓞 F)) = 1` using `le_antisymm (v.valuation_le_one _) (not_lt.1 fun hlt => hDv ((v.valuation_lt_one_iff_mem _).1 hlt))`. Establish `h1` using `h v`. Rewrite `h1`, the goal using `[Formalism.UG.P.levelaf_valued_algebraMap]`. Rewrite `hv1` using `[map_natCast]`. Rewrite `h1` using `[map_mul, hv1, one_mul]`.

Conclude with `h1`.
-/
theorem exists_finiteAdele_of_denom {F : Type} [Field F] [NumberField F] (r : HeightOneSpectrum (𝓞 F) → F) (D : ℕ)
    (hD : 0 < D) (h : ∀ v, Valued.v (algebraMap F (v.adicCompletion F) ((D : F) * r v)) ≤ 1) :
    ∃ c : FiniteAdeleRing (𝓞 F) F, ∀ v, c v = algebraMap F (v.adicCompletion F) (r v) := by
  have hD0 : Ideal.span {((D : ℕ) : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hD.ne'
  have hfin := Ideal.finite_factors hD0
  refine ⟨⟨fun v => algebraMap F (v.adicCompletion F) (r v), Filter.eventually_cofinite.2
    (hfin.subset fun v hv => ?_)⟩, fun v => rfl⟩
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_span_singleton]
  by_contra hDv
  apply hv
  rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  have hv1 : v.valuation F (algebraMap (𝓞 F) F (D : 𝓞 F)) = 1 :=
    le_antisymm (v.valuation_le_one _) (not_lt.1 fun hlt => hDv ((v.valuation_lt_one_iff_mem _).1 hlt))
  have h1 := h v
  rw [Formalism.UG.P.levelaf_valued_algebraMap] at h1 ⊢
  rw [map_natCast] at hv1
  rw [map_mul, hv1, one_mul] at h1
  exact h1

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_le'`. Rewrite `hx`, the goal using `[← WithZero.exp_log h0]`. Rewrite `hx` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (hx : x < 1) : x ≤ WithZero.exp (-1) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le'
  · rw [← WithZero.exp_log h0] at hx ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at hx
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Establish `hle : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b ≤ 1 → Valued.v (locMap F P b) ≤ 1` using `fun b hb => by`. Simplify `hb)` using `using locMap_valued P 0 b (by simpa`. Establish `hlt : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b < 1 → Valued.v (locMap F P b) < 1` using `fun b hb => by`. Use `locMap_valued P 1 b (by simpa using le_exp_neg_one_of_lt_one hb)` as an intermediate fact. Use `lt_of_le_of_lt this ?_` and prove the remaining obligations.

Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Use linear arithmetic over natural numbers and integers. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`.

Break down `lt_or_gt_of_ne hne with hl | hg` into its components or cases. Conclude with `absurd h (ne_of_lt (hlt a hl))`. Establish `ha0 : a ≠ 0` using `fun e => by rw [e, map_zero] at hg; exact not_lt_of_ge zero_le' hg`. Establish `hinv : Valued.v a⁻¹ < 1`. Rewrite using `[map_inv₀]`.

Conclude with `inv_lt_one_of_one_lt₀ hg`. Establish `h2` using `hlt _ hinv`. Rewrite `h2` using `[map_inv₀, map_inv₀, h, inv_one]`. Conclude with `lt_irrefl _ h2`. Introduce `h`.

Establish `ha0 : a ≠ 0` using `fun e => by rw [e, map_zero] at h; exact zero_ne_one h`. Use `le_antisymm (hle a h.le) ?_` and prove the remaining obligations. Establish `h2` using `hle a⁻¹ (by rw [map_inv₀, h, inv_one])`. Establish `h3 : Valued.v (locMap F P a) * Valued.v (locMap F P a⁻¹) = 1`. Rewrite using `[← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem locMap_val_eq_one_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    Valued.v (locMap F P a) = 1 ↔ Valued.v a = 1 := by
  have hle : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b ≤ 1 → Valued.v (locMap F P b) ≤ 1 := fun b hb => by
    simpa using locMap_valued P 0 b (by simpa using hb)
  have hlt : ∀ b : (P.under (𝓞 F)).adicCompletion F, Valued.v b < 1 → Valued.v (locMap F P b) < 1 := fun b hb => by
    have := locMap_valued P 1 b (by simpa using le_exp_neg_one_of_lt_one hb)
    refine lt_of_le_of_lt this ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hg
    · exact absurd h (ne_of_lt (hlt a hl))
    · have ha0 : a ≠ 0 := fun e => by rw [e, map_zero] at hg; exact not_lt_of_ge zero_le' hg
      have hinv : Valued.v a⁻¹ < 1 := by
        rw [map_inv₀]
        exact inv_lt_one_of_one_lt₀ hg
      have h2 := hlt _ hinv
      rw [map_inv₀, map_inv₀, h, inv_one] at h2
      exact lt_irrefl _ h2
  · intro h
    have ha0 : a ≠ 0 := fun e => by rw [e, map_zero] at h; exact zero_ne_one h
    refine le_antisymm (hle a h.le) ?_
    have h2 := hle a⁻¹ (by rw [map_inv₀, h, inv_one])
    have h3 : Valued.v (locMap F P a) * Valued.v (locMap F P a⁻¹) = 1 := by
      rw [← map_mul, ← map_mul, mul_inv_cancel₀ ha0, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (locMap F P a) * Valued.v (locMap F P a⁻¹) := h3.symm
      _ ≤ Valued.v (locMap F P a) := mul_le_of_le_one_right' h2

/- English proof (translation)
Rewrite using `[adMap_apply]`. Conclude with `locMap_val_eq_one_iff P _`.
-/
theorem adMap_val_eq_one_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : FiniteAdeleRing (𝓞 F) F) (P : HeightOneSpectrum (𝓞 E)) :
    Valued.v (adMap F E n P) = 1 ↔ Valued.v (n (P.under (𝓞 F))) = 1 := by
  rw [adMap_apply]
  exact locMap_val_eq_one_iff P _

/- English proof (translation)
Take `⟨D, hD, hc⟩` from `exists_coord_denom F E`. Establish `hr : ∀ i, ∃ c : FiniteAdeleRing (𝓞 F) F, ∀ v, c v = algebraMap F (v.adicCompletion F) ((Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v)) i)`. Introduce `i`. Use `exists_finiteAdele_of_denom _ D hD fun v => ?_` and prove the remaining obligations. Establish `h1` using `hc _ (Formalism.UG.P.levelaf_tmul_mem (f v) (one_mem (intAd F))) i v`.

Rewrite `h1` using `[coord_tmul, HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `e : D • (((Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v))) i • (1 : FiniteAdeleRing (𝓞 F) F)) = algebraMap F _ ((D : F) * (Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v)) i)`. Rewrite using `[← Algebra.algebraMap_eq_smul_one, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)), ← map_mul]`. Rewrite `h1` using `[e]`. Conclude with `h1`.

Use `choose c hc' using hr`. Use `⟨∑ i, Module.finBasis F E i ⊗ₜ[F] c i, fun g ι hι P => ?_⟩` and prove the remaining obligations. Establish `e1 : ι (sigR g (FiniteAdeleRing (𝓞 F) F) (∑ i, Module.finBasis F E i ⊗ₜ[F] c i)) = ∑ i, algebraMap E _ (g (Module.finBasis F E i)) * adMap F E (c i)`. Rewrite using `[map_sum, map_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => hι _ _`.

Rewrite using `[e1, ← localComponent_apply₂, map_sum]`. Use `conv_rhs => rw [← (Module.finBasis F E).sum_repr (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))]`. Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, localComponent_algebraMap, localComponent_apply₂, adMap_apply, hc', locMap_algebraMap, Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, mul_comm]`.
-/
theorem exists_glue_of_int {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (f : HeightOneSpectrum (𝓞 F) → 𝓞 E) : ∃ a : AfE F E,
    ∀ (g : E →ₐ[F] E) (ι : AfE F E →+* FiniteAdeleRing (𝓞 E) E),
      (∀ x b, ι (x ⊗ₜ[F] b) = algebraMap E _ x * adMap F E b) →
      ∀ P : HeightOneSpectrum (𝓞 E), ι (sigR g _ a) P =
        algebraMap E _ (g (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))) := by
  obtain ⟨D, hD, hc⟩ := exists_coord_denom F E
  have hr : ∀ i, ∃ c : FiniteAdeleRing (𝓞 F) F, ∀ v, c v = algebraMap F (v.adicCompletion F)
      ((Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v)) i) := by
    intro i
    refine exists_finiteAdele_of_denom _ D hD fun v => ?_
    have h1 := hc _ (Formalism.UG.P.levelaf_tmul_mem (f v) (one_mem (intAd F))) i v
    rw [coord_tmul, HeightOneSpectrum.mem_adicCompletionIntegers] at h1
    have e : D • (((Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v))) i • (1 : FiniteAdeleRing (𝓞 F) F)) =
        algebraMap F _ ((D : F) * (Module.finBasis F E).repr (algebraMap (𝓞 E) E (f v)) i) := by
      rw [← Algebra.algebraMap_eq_smul_one, nsmul_eq_mul, ← map_natCast (algebraMap F (FiniteAdeleRing (𝓞 F) F)),
        ← map_mul]
    rw [e] at h1
    exact h1
  choose c hc' using hr
  refine ⟨∑ i, Module.finBasis F E i ⊗ₜ[F] c i, fun g ι hι P => ?_⟩
  have e1 : ι (sigR g (FiniteAdeleRing (𝓞 F) F) (∑ i, Module.finBasis F E i ⊗ₜ[F] c i)) =
      ∑ i, algebraMap E _ (g (Module.finBasis F E i)) * adMap F E (c i) := by
    rw [map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => hι _ _
  rw [e1, ← localComponent_apply₂, map_sum]
  conv_rhs => rw [← (Module.finBasis F E).sum_repr (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))]
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, localComponent_algebraMap, localComponent_apply₂, adMap_apply, hc', locMap_algebraMap, Algebra.smul_def, map_mul,
    AlgHom.commutes, map_mul, mul_comm]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `h` using `Algebra.FormallyUnramified.ext_of_iInf (R := 𝓞 F) P.asIdeal (Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top) (g₁ := AlgHom.id _ (𝓞 E)) (g₂ := RingOfIntegers.mapAlgHom σ) (fun x => Ideal.Quotient.eq.2 (hn x))`. Apply `hσ.1` to reduce the goal to its premises. Use extensionality with `x`.

Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`. Establish `h1 : ∀ a : 𝓞 E, σ (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a` using `fun a => by`. Use `DFunLike.congr_fun h a` as an intermediate fact. Conclude with `congrArg (algebraMap (𝓞 E) E) this.symm`. Rewrite using `[map_div₀, h1, h1]`.

Both sides reduce to the same expression.
-/
theorem exists_sub_sig_notMem (σ : E →ₐ[F] E) (hσ : IsConjOf σ) [Algebra.Unramified (𝓞 F) (𝓞 E)]
    (P : HeightOneSpectrum (𝓞 E)) : ∃ b : 𝓞 E, b - RingOfIntegers.mapAlgHom σ b ∉ P.asIdeal := by
  by_contra hn
  push_neg at hn
  have h := Algebra.FormallyUnramified.ext_of_iInf (R := 𝓞 F) P.asIdeal
    (Ideal.iInf_pow_eq_bot_of_isDomain P.asIdeal P.isPrime.ne_top) (g₁ := AlgHom.id _ (𝓞 E))
    (g₂ := RingOfIntegers.mapAlgHom σ) (fun x => Ideal.Quotient.eq.2 (hn x))
  apply hσ.1
  ext x
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have h1 : ∀ a : 𝓞 E, σ (algebraMap (𝓞 E) E a) = algebraMap (𝓞 E) E a := fun a => by
    have := DFunLike.congr_fun h a
    exact congrArg (algebraMap (𝓞 E) E) this.symm
  rw [map_div₀, h1, h1]
  rfl

/- English proof (translation)
Take `⟨b, hb⟩` from `exists_sub_sig_notMem σ hσ P`. Use `set g : 𝓞 E → P.adicCompletion E := fun o => algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E o) with hg`. Establish `hval : ∀ o : 𝓞 E, Valued.v (g o) = P.valuation E (algebraMap (𝓞 E) E o)` using `fun o => P.valuedAdicCompletion_eq_valuation (K := E) o`. Establish `hle : ∀ o, Valued.v (g o) ≤ 1` using `fun o => by rw [hval]; exact P.valuation_le_one o`. Establish `hlt : ∀ o, Valued.v (g o) < 1 ↔ o ∈ P.asIdeal` using `fun o => by rw [hval]; exact P.valuation_lt_one_iff_mem o`.

Establish `hσg : ∀ o, algebraMap E (P.adicCompletion E) (σ (algebraMap (𝓞 E) E o)) = g (RingOfIntegers.mapAlgHom σ o)` using `fun o => rfl`. Establish `hle' : ∀ o, Valued.v (g o + dP * g (RingOfIntegers.mapAlgHom σ o)) ≤ 1` using `fun o => Valuation.map_add_le _ (hle o) (by rw [map_mul]; exact mul_le_one' hd (hle _))`. Assume the negation of the conclusion as `hn`. Use `push_neg at hn`. Establish `h1 : Valued.v (g 1 + dP * g (RingOfIntegers.mapAlgHom σ 1)) < 1` using `lt_of_le_of_ne (hle' 1) (by`.

Rewrite using `[← hσg]`. Conclude with `hn 1)`. Establish `h2 : Valued.v (g b + dP * g (RingOfIntegers.mapAlgHom σ b)) < 1` using `lt_of_le_of_ne (hle' b) (by`. Rewrite using `[← hσg]`. Conclude with `hn b)`.

Apply `hb` to reduce the goal to its premises. Rewrite using `[← hlt]`. Establish `e : g (b - RingOfIntegers.mapAlgHom σ b) = (g b + dP * g (RingOfIntegers.mapAlgHom σ b)) - g (RingOfIntegers.mapAlgHom σ b) * (g 1 + dP * g (RingOfIntegers.mapAlgHom σ 1))`. Simplify using `only [hg, map_sub, map_one, mul_one]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 ?_)` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' (hle _)) h1`.
-/
theorem exists_val_add_eq_one (σ : E →ₐ[F] E) (hσ : IsConjOf σ) [Algebra.Unramified (𝓞 F) (𝓞 E)]
    (P : HeightOneSpectrum (𝓞 E)) (dP : P.adicCompletion E) (hd : Valued.v dP ≤ 1) :
    ∃ a : 𝓞 E, Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E a) +
      dP * algebraMap E (P.adicCompletion E) (σ (algebraMap (𝓞 E) E a))) = 1 := by
  obtain ⟨b, hb⟩ := exists_sub_sig_notMem σ hσ P
  set g : 𝓞 E → P.adicCompletion E := fun o => algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E o) with hg
  have hval : ∀ o : 𝓞 E, Valued.v (g o) = P.valuation E (algebraMap (𝓞 E) E o) := fun o =>
    P.valuedAdicCompletion_eq_valuation (K := E) o
  have hle : ∀ o, Valued.v (g o) ≤ 1 := fun o => by rw [hval]; exact P.valuation_le_one o
  have hlt : ∀ o, Valued.v (g o) < 1 ↔ o ∈ P.asIdeal := fun o => by rw [hval]; exact P.valuation_lt_one_iff_mem o
  have hσg : ∀ o, algebraMap E (P.adicCompletion E) (σ (algebraMap (𝓞 E) E o)) = g (RingOfIntegers.mapAlgHom σ o) :=
    fun o => rfl
  have hle' : ∀ o, Valued.v (g o + dP * g (RingOfIntegers.mapAlgHom σ o)) ≤ 1 := fun o =>
    Valuation.map_add_le _ (hle o) (by rw [map_mul]; exact mul_le_one' hd (hle _))
  by_contra hn
  push_neg at hn
  have h1 : Valued.v (g 1 + dP * g (RingOfIntegers.mapAlgHom σ 1)) < 1 := lt_of_le_of_ne (hle' 1) (by
    rw [← hσg]; exact hn 1)
  have h2 : Valued.v (g b + dP * g (RingOfIntegers.mapAlgHom σ b)) < 1 := lt_of_le_of_ne (hle' b) (by
    rw [← hσg]; exact hn b)
  apply hb
  rw [← hlt]
  have e : g (b - RingOfIntegers.mapAlgHom σ b) = (g b + dP * g (RingOfIntegers.mapAlgHom σ b)) -
      g (RingOfIntegers.mapAlgHom σ b) * (g 1 + dP * g (RingOfIntegers.mapAlgHom σ 1)) := by
    simp only [hg, map_sub, map_one, mul_one]
    ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h2 ?_)
  rw [map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hle _)) h1

/- English proof (translation)
Take `⟨ι, hι⟩` from `exists_toAd F E`. Establish `hιaf : ∀ y, ι y = GlobalTheory.Mem.Col2.afIso F E y`. Introduce `y`. Set `e : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E` to `RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩`. Establish `he : GlobalTheory.TwU.IsAdIso e`.

Use `⟨fun x => map_tmul_one hι x, fun y => ⟨fun hy P => ?_, fun h => ?_⟩⟩` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (map_mem_int hι hy P)`. Conclude with `mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)`. Conclude with `GlobalTheory.isAdIso_eq_afIso F E e he y`. Set `S : HeightOneSpectrum (𝓞 F) → Prop` to `fun v => ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = v → ι d P' = 1`.

Establish `hσσ : ∀ x, σ (σ x) = x` using `hσ.2.1`. Establish `htr : ∀ x, ∃ t : F, x + σ x = algebraMap F E t` using `fun x => by`. Take `⟨t, ht⟩` from `hσ.2.2 (x + σ x) (by rw [map_add, hσσ, add_comm])`. Conclude with `⟨t, ht.symm⟩`. Use `set sR := sigR σ (FiniteAdeleRing (𝓞 F) F) with hsR`.

Establish `hss : ∀ z, sR (sR z) = z` using `GlobalTheory.Mem.DetClass.sigR_sigR hσσ`. Establish `hdd : (d : AfE F E) * sR d = 1` using `congrArg Units.val hU`. Take `⟨hdI, hdI'⟩` from `(Submonoid.mem_units_iff _ _).1 hd`. Establish `hstarO : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, algebraMap (𝓞 E) E o' = σ (algebraMap (𝓞 E) E o)` using `fun o => ⟨RingOfIntegers.mapAlgHom σ o, rfl⟩`. Establish `hsR_int : ∀ z ∈ RInt F E, sR z ∈ RInt F E`.

Introduce `z hz`. Establish `h : RInt F E ≤ (RInt F E).comap sR` using `by show Subring.closure _ ≤ _`. Use `Subring.closure_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨y, rfl⟩)`. Take `⟨o', ho'⟩` from `hstarO o show σ (algebraMap (𝓞 E) E o) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ RInt F E`.

Conclude with `Subring.subset_closure (Or.inl ⟨⟨_, o', ho'⟩, rfl⟩)`. Use `show σ 1 ⊗ₜ[F] (y : FiniteAdeleRing (𝓞 F) F) ∈ RInt F E`. Rewrite using `[map_one]`. Conclude with `Subring.subset_closure (Or.inr ⟨y, rfl⟩)`. Conclude with `h hz`.

Establish `hint : ∀ z ∈ RInt F E, ∀ P, Valued.v (ι z P) ≤ 1` using `fun z hz P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (map_mem_int hι hz P)`. Establish `hOint : ∀ (o : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)), Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E o)) ≤ 1` using `fun o P => by`. Establish `h` using `hint _ (Formalism.UG.P.levelaf_tmul_mem o (one_mem (intAd F))) P`. Rewrite `h` using `[map_tmul_one hι]`. Conclude with `h`.

Establish `hval1 : ∀ u w : AfE F E, u ∈ RInt F E → w ∈ RInt F E → u * w = 1 → ∀ P, Valued.v (ι u P) = 1`. Introduce `u w hu hw huw P`. Use `le_antisymm (hint u hu P) ?_` and prove the remaining obligations. Establish `h : ι u P * ι w P = 1`. Rewrite using `[← localComponent_apply₂, ← localComponent_apply₂, ← map_mul, ← map_mul, huw, map_one, map_one]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hsdv : ∀ P, Valued.v (ι (sR d) P) = 1` using `hval1 _ (sR ((d⁻¹ : (AfE F E)ˣ) : AfE F E)) (hsR_int _ hdI) (hsR_int _ hdI') (by rw [← map_mul, Units.mul_inv, map_one])`. Establish `hd1 : ∀ P : HeightOneSpectrum (𝓞 E), S (P.under (𝓞 F)) → ι d P = 1` using `fun P h => h P rfl`. Establish `hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ o : 𝓞 E, (S v → o = 0) ∧ (¬ S v → ∀ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v → ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v ∧ Valued.v (algebraMap E _ (algebraMap (𝓞 E) E o) + ι d Q * algebraMap E _ (σ (algebraMap (𝓞 E) E o))) = 1 …`. Introduce `v`.

Distinguish the cases in `hv : S v`. Conclude with `⟨0, fun _ => rfl, fun h => absurd hv h⟩`. Distinguish the cases in `h : ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v`. Take `⟨P, hP⟩` from `h`. Take `⟨o, ho⟩` from `exists_val_add_eq_one σ hσ P (ι d P) (hint _ hdI P)`.

Conclude with `⟨o, fun h' => absurd h' hv, fun _ _ _ => ⟨P, hP, ho⟩⟩`. Conclude with `⟨0, fun h' => absurd h' hv, fun _ P hP => absurd ⟨P, hP⟩ h⟩`. Use `choose f hf0 hfgood using hloc`. Take `⟨a, ha⟩` from `exists_glue_of_int f`. Establish `haι : ∀ P, ι a P = algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))`.

Introduce `P`. Establish `h` using `ha (AlgHom.id F E) ι hι P`. Establish `e : sigR (AlgHom.id F E) (FiniteAdeleRing (𝓞 F) F) a = a` using `by show (Algebra.TensorProduct.map (AlgHom.id F E) (AlgHom.id F (FiniteAdeleRing (𝓞 F) F))).toRingHom a = a`. Rewrite using `[Algebra.TensorProduct.map_id]`. Both sides reduce to the same expression.

Rewrite `h` using `[e]`. Conclude with `h`. Establish `haσ : ∀ P, ι (sR a) P = algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))))` using `fun P => ha σ ι hι P`. Apply the tactic sequence `obtain ⟨ε, hε⟩ := exists_finiteAdele_of_denom (fun v => if S v then (1 : F) else 0) 1 one_pos (fun v => by split_ifs <;> simp)`. Establish `hεP : ∀ P : HeightOneSpectrum (𝓞 E), adMap F E ε P = if S (P.under (𝓞 F)) then 1 else 0`.

Introduce `P`. Rewrite using `[adMap_apply, hε]`. Apply the tactic sequence `split_ifs <;> simp`. Use `set T : AfE F E := (1 : E) ⊗ₜ[F] ε with hT`. Use `set x0 : AfE F E := T + a + d * sR a with hx0`.

Establish `hιT : ∀ P, ι T P = if S (P.under (𝓞 F)) then 1 else 0` using `fun P => by`. Rewrite using `[hT, hι, map_one, one_mul]`. Conclude with `hεP P`. Establish `ιx : ∀ P, ι x0 P = (if S (P.under (𝓞 F)) then 1 else 0) + algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))) + ι d P * algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))))`. Introduce `P`.

Rewrite using `[hx0, map_add, map_add, map_mul]`. Use `show ι T P + ι a P + ι d P * ι (sR a) P = _`. Rewrite using `[hιT, haι, haσ]`. Establish `hxS : ∀ P : HeightOneSpectrum (𝓞 E), S (P.under (𝓞 F)) → ι x0 P = 1`. Introduce `P h`.

Rewrite using `[ιx, if_pos h, hf0 _ h]`. Simplify using the standard rewrite rules. Establish `hxN : ∀ P : HeightOneSpectrum (𝓞 E), ¬ S (P.under (𝓞 F)) → ι x0 P = algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))) + ι d P * algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))))`. Introduce `P h`. Rewrite using `[ιx, if_neg h, zero_add]`.

Establish `hde : (d : AfE F E) * T = T`. Apply `map_injective hι` to reduce the goal to its premises. Use `FiniteAdeleRing.ext _ fun P => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `show ι d P * ι T P = ι T P`.

Rewrite using `[hιT]`. Use `split_ifs with h`. Rewrite using `[hd1 P h, one_mul]`. Rewrite using `[mul_zero]`. Establish `hsT : sR T = T` using `by show σ 1 ⊗ₜ[F] ε = _`.

Rewrite using `[map_one]`. Establish `hsx : sR x0 = T + sR a + sR d * a`. Rewrite using `[hx0, map_add, map_add, map_mul, hsT, hss]`. Establish `hrel : x0 = d * sR x0`. Rewrite using `[hsx, hx0]`.

Take the linear combination `(-1 : AfE F E) * hde - a * hdd`. Establish `hsx2 : sR x0 = sR d * x0`. Establish `h` using `congrArg sR hrel`. Rewrite `h` using `[map_mul, hss]`. Then use the resulting hypothesis. Take `⟨n, hn⟩` from `GlobalTheory.Mem.DetClass.exists_eq_tmul_of_fixed htr (x0 * sR x0) (by rw [map_mul, hss, mul_comm])`.

Establish `hnv : ∀ P, Valued.v (adMap F E n P) = Valued.v (ι x0 P) * Valued.v (ι x0 P)`. Introduce `P`. Establish `h : ι (x0 * sR x0) P = ι x0 P * (ι (sR d) P * ι x0 P)`. Rewrite using `[hsx2, map_mul, map_mul]`. Both sides reduce to the same expression.

Rewrite `h` using `[hn, hι, map_one, one_mul]`. Rewrite using `[show adMap F E n P = _ from h, map_mul, map_mul, hsdv, one_mul]`. Establish `hle : ∀ P, Valued.v (ι x0 P) ≤ 1`. Introduce `P`. Distinguish the cases in `hSP : S (P.under (𝓞 F))`.

Rewrite using `[hxS P hSP, map_one]`. Rewrite using `[hxN P hSP]`. Take `⟨o', ho'⟩` from `hstarO (f (P.under (𝓞 F)))`. Use `Valuation.map_add_le _ (hOint _ P) ?_` and prove the remaining obligations. Rewrite using `[map_mul, ← ho']`.

Conclude with `mul_le_one' (hint _ hdI P) (hOint _ P)`. Establish `hx1 : ∀ P, Valued.v (ι x0 P) = 1`. Introduce `P`. Distinguish the cases in `hSP : S (P.under (𝓞 F))`. Rewrite using `[hxS P hSP, map_one]`.

Take `⟨Q, hQ, hQv⟩` from `hfgood _ hSP P rfl`. Establish `hxQ : Valued.v (ι x0 Q) = 1`. Rewrite using `[hxN Q (hQ ▸ hSP), hQ]`. Conclude with `hQv`. Establish `h1 : Valued.v (adMap F E n Q) = 1` using `by rw [hnv, hxQ, one_mul]`.

Rewrite `h1` using `[adMap_val_eq_one_iff, hQ]`. Establish `h2 : Valued.v (adMap F E n P) = 1` using `(adMap_val_eq_one_iff n P).2 h1`. Rewrite `h2` using `[hnv]`. Use `le_antisymm (hle P) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hunitι : IsUnit (ι x0)`. Rewrite using `[FiniteAdeleRing.isUnit_iff]`. Use `⟨fun P h => ?_, Filter.Eventually.of_forall hx1⟩` and prove the remaining obligations. Use `hx1 P` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `zero_ne_one this`. Set `e : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E` to `RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩`. Establish `hunit : IsUnit x0` using `(isUnit_map_iff e x0).1 hunitι`. Use `⟨hunit.unit, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `(Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩` and prove the remaining obligations.

Conclude with `mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle P)`. Use `mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_` and prove the remaining obligations. Establish `h : ι x0 P * ι ((hunit.unit⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1`. Rewrite using `[← localComponent_apply₂, ← localComponent_apply₂, ← map_mul, ← map_mul]`. Rewrite using `[IsUnit.mul_val_inv hunit, map_one, map_one]`.

Establish `h'` using `congrArg Valued.v h`. Rewrite `h'` using `[map_mul, hx1, one_mul, map_one]`. Conclude with `h'.le`. Rewrite using `[h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]`. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[Units.val_mul]`. Conclude with `hrel`. Introduce `P hP`. Rewrite using `[← hιaf]`. Conclude with `hxS P fun P' hP' => by rw [hιaf]; exact hP P' hP'`.
-/
theorem exists_integral_h90_preimage_of_mem_intU_unramified (σ : E →ₐ[F] E) (hσ : IsConjOf σ) [Algebra.Unramified (𝓞 F) (𝓞 E)]
    (d : (AfE F E)ˣ) (hU : d ∈ U1 σ) (hd : d ∈ intU F E) :
    ∃ x ∈ intU F E, h90 σ x = d ∧ ∀ P : HeightOneSpectrum (𝓞 E),
      (∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → GlobalTheory.Mem.Col2.afIso F E (d : AfE F E) P' = 1) →
        GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1 := by
  classical
  obtain ⟨ι, hι⟩ := exists_toAd F E

  have hιaf : ∀ y, ι y = GlobalTheory.Mem.Col2.afIso F E y := by
    intro y
    let e : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
    have he : GlobalTheory.TwU.IsAdIso e := by
      refine ⟨fun x => map_tmul_one hι x, fun y => ⟨fun hy P => ?_, fun h => ?_⟩⟩
      · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (map_mem_int hι hy P)
      · exact mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h P)
    exact GlobalTheory.isAdIso_eq_afIso F E e he y
  let S : HeightOneSpectrum (𝓞 F) → Prop := fun v => ∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = v → ι d P' = 1
  have hσσ : ∀ x, σ (σ x) = x := hσ.2.1
  have htr : ∀ x, ∃ t : F, x + σ x = algebraMap F E t := fun x => by
    obtain ⟨t, ht⟩ := hσ.2.2 (x + σ x) (by rw [map_add, hσσ, add_comm])
    exact ⟨t, ht.symm⟩
  set sR := sigR σ (FiniteAdeleRing (𝓞 F) F) with hsR
  have hss : ∀ z, sR (sR z) = z := GlobalTheory.Mem.DetClass.sigR_sigR hσσ
  have hdd : (d : AfE F E) * sR d = 1 := congrArg Units.val hU
  obtain ⟨hdI, hdI'⟩ := (Submonoid.mem_units_iff _ _).1 hd
  have hstarO : ∀ o : 𝓞 E, ∃ o' : 𝓞 E, algebraMap (𝓞 E) E o' = σ (algebraMap (𝓞 E) E o) := fun o =>
    ⟨RingOfIntegers.mapAlgHom σ o, rfl⟩
  have hsR_int : ∀ z ∈ RInt F E, sR z ∈ RInt F E := by
    intro z hz
    have h : RInt F E ≤ (RInt F E).comap sR := by
      show Subring.closure _ ≤ _
      refine Subring.closure_le.2 ?_
      rintro _ (⟨⟨x, o, rfl⟩, rfl⟩ | ⟨y, rfl⟩)
      · obtain ⟨o', ho'⟩ := hstarO o
        show σ (algebraMap (𝓞 E) E o) ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F) ∈ RInt F E
        exact Subring.subset_closure (Or.inl ⟨⟨_, o', ho'⟩, rfl⟩)
      · show σ 1 ⊗ₜ[F] (y : FiniteAdeleRing (𝓞 F) F) ∈ RInt F E
        rw [map_one]
        exact Subring.subset_closure (Or.inr ⟨y, rfl⟩)
    exact h hz
  have hint : ∀ z ∈ RInt F E, ∀ P, Valued.v (ι z P) ≤ 1 := fun z hz P =>
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (map_mem_int hι hz P)
  have hOint : ∀ (o : 𝓞 E) (P : HeightOneSpectrum (𝓞 E)),
      Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E o)) ≤ 1 := fun o P => by
    have h := hint _ (Formalism.UG.P.levelaf_tmul_mem o (one_mem (intAd F))) P
    rw [map_tmul_one hι] at h
    exact h
  have hval1 : ∀ u w : AfE F E, u ∈ RInt F E → w ∈ RInt F E → u * w = 1 → ∀ P, Valued.v (ι u P) = 1 := by
    intro u w hu hw huw P
    refine le_antisymm (hint u hu P) ?_
    have h : ι u P * ι w P = 1 := by
      rw [← localComponent_apply₂, ← localComponent_apply₂, ← map_mul, ← map_mul, huw, map_one, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (ι u P) * Valued.v (ι w P) := by rw [← map_mul, h, map_one]
      _ ≤ Valued.v (ι u P) := mul_le_of_le_one_right' (hint w hw P)
  have hsdv : ∀ P, Valued.v (ι (sR d) P) = 1 := hval1 _ (sR ((d⁻¹ : (AfE F E)ˣ) : AfE F E)) (hsR_int _ hdI)
    (hsR_int _ hdI') (by rw [← map_mul, Units.mul_inv, map_one])
  have hd1 : ∀ P : HeightOneSpectrum (𝓞 E), S (P.under (𝓞 F)) → ι d P = 1 := fun P h => h P rfl

  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ o : 𝓞 E, (S v → o = 0) ∧ (¬ S v → ∀ P : HeightOneSpectrum (𝓞 E),
      P.under (𝓞 F) = v → ∃ Q : HeightOneSpectrum (𝓞 E), Q.under (𝓞 F) = v ∧
        Valued.v (algebraMap E _ (algebraMap (𝓞 E) E o) + ι d Q * algebraMap E _ (σ (algebraMap (𝓞 E) E o))) = 1) := by
    intro v
    by_cases hv : S v
    · exact ⟨0, fun _ => rfl, fun h => absurd hv h⟩
    · by_cases h : ∃ P : HeightOneSpectrum (𝓞 E), P.under (𝓞 F) = v
      · obtain ⟨P, hP⟩ := h
        obtain ⟨o, ho⟩ := exists_val_add_eq_one σ hσ P (ι d P) (hint _ hdI P)
        exact ⟨o, fun h' => absurd h' hv, fun _ _ _ => ⟨P, hP, ho⟩⟩
      · exact ⟨0, fun h' => absurd h' hv, fun _ P hP => absurd ⟨P, hP⟩ h⟩
  choose f hf0 hfgood using hloc
  obtain ⟨a, ha⟩ := exists_glue_of_int f
  have haι : ∀ P, ι a P = algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))) := by
    intro P
    have h := ha (AlgHom.id F E) ι hι P
    have e : sigR (AlgHom.id F E) (FiniteAdeleRing (𝓞 F) F) a = a := by
      show (Algebra.TensorProduct.map (AlgHom.id F E) (AlgHom.id F (FiniteAdeleRing (𝓞 F) F))).toRingHom a = a
      rw [Algebra.TensorProduct.map_id]
      rfl
    rw [e] at h
    exact h
  have haσ : ∀ P, ι (sR a) P = algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))) :=
    fun P => ha σ ι hι P
  obtain ⟨ε, hε⟩ := exists_finiteAdele_of_denom (fun v => if S v then (1 : F) else 0) 1 one_pos (fun v => by
    split_ifs <;> simp)
  have hεP : ∀ P : HeightOneSpectrum (𝓞 E), adMap F E ε P = if S (P.under (𝓞 F)) then 1 else 0 := by
    intro P
    rw [adMap_apply, hε]
    split_ifs <;> simp
  set T : AfE F E := (1 : E) ⊗ₜ[F] ε with hT
  set x0 : AfE F E := T + a + d * sR a with hx0
  have hιT : ∀ P, ι T P = if S (P.under (𝓞 F)) then 1 else 0 := fun P => by
    rw [hT, hι, map_one, one_mul]
    exact hεP P
  have ιx : ∀ P, ι x0 P = (if S (P.under (𝓞 F)) then 1 else 0) + algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))) +
      ι d P * algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))) := by
    intro P
    rw [hx0, map_add, map_add, map_mul]
    show ι T P + ι a P + ι d P * ι (sR a) P = _
    rw [hιT, haι, haσ]
  have hxS : ∀ P : HeightOneSpectrum (𝓞 E), S (P.under (𝓞 F)) → ι x0 P = 1 := by
    intro P h
    rw [ιx, if_pos h, hf0 _ h]
    simp
  have hxN : ∀ P : HeightOneSpectrum (𝓞 E), ¬ S (P.under (𝓞 F)) → ι x0 P =
      algebraMap E _ (algebraMap (𝓞 E) E (f (P.under (𝓞 F)))) +
        ι d P * algebraMap E _ (σ (algebraMap (𝓞 E) E (f (P.under (𝓞 F))))) := by
    intro P h
    rw [ιx, if_neg h, zero_add]
  have hde : (d : AfE F E) * T = T := by
    apply map_injective hι
    refine FiniteAdeleRing.ext _ fun P => ?_
    rw [map_mul]
    show ι d P * ι T P = ι T P
    rw [hιT]
    split_ifs with h
    · rw [hd1 P h, one_mul]
    · rw [mul_zero]
  have hsT : sR T = T := by
    show σ 1 ⊗ₜ[F] ε = _
    rw [map_one]
  have hsx : sR x0 = T + sR a + sR d * a := by
    rw [hx0, map_add, map_add, map_mul, hsT, hss]
  have hrel : x0 = d * sR x0 := by
    rw [hsx, hx0]
    linear_combination (-1 : AfE F E) * hde - a * hdd
  have hsx2 : sR x0 = sR d * x0 := by
    have h := congrArg sR hrel
    rwa [map_mul, hss] at h
  obtain ⟨n, hn⟩ := GlobalTheory.Mem.DetClass.exists_eq_tmul_of_fixed htr (x0 * sR x0) (by rw [map_mul, hss, mul_comm])
  have hnv : ∀ P, Valued.v (adMap F E n P) = Valued.v (ι x0 P) * Valued.v (ι x0 P) := by
    intro P
    have h : ι (x0 * sR x0) P = ι x0 P * (ι (sR d) P * ι x0 P) := by
      rw [hsx2, map_mul, map_mul]
      rfl
    rw [hn, hι, map_one, one_mul] at h
    rw [show adMap F E n P = _ from h, map_mul, map_mul, hsdv, one_mul]
  have hle : ∀ P, Valued.v (ι x0 P) ≤ 1 := by
    intro P
    by_cases hSP : S (P.under (𝓞 F))
    · rw [hxS P hSP, map_one]
    · rw [hxN P hSP]
      obtain ⟨o', ho'⟩ := hstarO (f (P.under (𝓞 F)))
      refine Valuation.map_add_le _ (hOint _ P) ?_
      rw [map_mul, ← ho']
      exact mul_le_one' (hint _ hdI P) (hOint _ P)
  have hx1 : ∀ P, Valued.v (ι x0 P) = 1 := by
    intro P
    by_cases hSP : S (P.under (𝓞 F))
    · rw [hxS P hSP, map_one]
    · obtain ⟨Q, hQ, hQv⟩ := hfgood _ hSP P rfl
      have hxQ : Valued.v (ι x0 Q) = 1 := by
        rw [hxN Q (hQ ▸ hSP), hQ]
        exact hQv
      have h1 : Valued.v (adMap F E n Q) = 1 := by rw [hnv, hxQ, one_mul]
      rw [adMap_val_eq_one_iff, hQ] at h1
      have h2 : Valued.v (adMap F E n P) = 1 := (adMap_val_eq_one_iff n P).2 h1
      rw [hnv] at h2
      refine le_antisymm (hle P) ?_
      calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (ι x0 P) * Valued.v (ι x0 P) := h2.symm
        _ ≤ Valued.v (ι x0 P) := mul_le_of_le_one_right' (hle P)
  have hunitι : IsUnit (ι x0) := by
    rw [FiniteAdeleRing.isUnit_iff]
    refine ⟨fun P h => ?_, Filter.Eventually.of_forall hx1⟩
    have := hx1 P
    rw [h, map_zero] at this
    exact zero_ne_one this
  let e : AfE F E ≃+* FiniteAdeleRing (𝓞 E) E := RingEquiv.ofBijective ι ⟨map_injective hι, map_surjective hι⟩
  have hunit : IsUnit x0 := (isUnit_map_iff e x0).1 hunitι
  refine ⟨hunit.unit, ?_, ?_, ?_⟩
  · refine (Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩
    · exact mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (hle P)
    · refine mem_int_of_map hι fun P => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 ?_
      have h : ι x0 P * ι ((hunit.unit⁻¹ : (AfE F E)ˣ) : AfE F E) P = 1 := by
        rw [← localComponent_apply₂, ← localComponent_apply₂, ← map_mul, ← map_mul]
        rw [IsUnit.mul_val_inv hunit, map_one, map_one]
      have h' := congrArg Valued.v h
      rw [map_mul, hx1, one_mul, map_one] at h'
      exact h'.le
  · rw [h90, MonoidHom.div_apply, MonoidHom.id_apply, div_eq_iff_eq_mul]
    apply Units.ext
    rw [Units.val_mul]
    exact hrel
  · intro P hP
    rw [← hιaf]
    exact hxS P fun P' hP' => by rw [hιaf]; exact hP P' hP'

end GlobalTheory.TwU.IntegralHilbert90Unramified

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ hunr z hz hzI`. Conclude with `GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_of_mem_intU_unramified σ hσ z hz hzI`.
-/
theorem GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_trivial_where_trivial : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsConjOf σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ z ∈ U1 σ, z ∈ intU F E → ∃ x ∈ intU F E, h90 σ x = z ∧ ∀ P : HeightOneSpectrum (𝓞 E), (∀ P' : HeightOneSpectrum (𝓞 E), P'.under (𝓞 F) = P.under (𝓞 F) → GlobalTheory.Mem.Col2.afIso F E (z : AfE F E) P' = 1) → GlobalTheory.Mem.Col2.afIso F E (x : AfE F E) P = 1 := by
  intro F E _ _ _ _ _ σ hσ hunr z hz hzI
  exact GlobalTheory.TwU.IntegralHilbert90Unramified.exists_integral_h90_preimage_of_mem_intU_unramified σ hσ z hz hzI
