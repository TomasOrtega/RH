import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SqrtPowOdd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValMulSqrtUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNumerator
import ReciprocityTheory.GaloisValuations.GlobalA
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharLocPowEqOneOnLocalUnitsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationEmbeddingGeneratorEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationSqrtAbsNormEqOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsElemStdLatticeSandwichSplitSupportStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeriesScal

/- English proof (translation)
Establish `hl : WithZero.log x ≤ 0`. Use `h1` as an intermediate fact. Rewrite `this` using `[← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Conclude with `this`. Use `⟨(-WithZero.log x).toNat, ?_⟩` and prove the remaining obligations.

Rewrite using `[Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]`.
-/
theorem exists_exp_nat {x : WithZero (Multiplicative ℤ)} (h0 : x ≠ 0) (h1 : x ≤ 1) :
    ∃ n : ℕ, x = WithZero.exp (-(n : ℤ)) := by
  have hl : WithZero.log x ≤ 0 := by
    have := h1
    rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at this
    exact this
  refine ⟨(-WithZero.log x).toNat, ?_⟩
  rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]

/- English proof (translation)
Establish `hx : IsIntegral ℤ (σ (x : k))` using `x.2.map σ.toIntAlgHom`. Establish `hi : IsIntegral A (σ (x : k))` using `hx.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 hi`. Rewrite using `[← hy]`. Conclude with `A.valuation_le_one y`.
-/
theorem val_le_one_int {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (A : ValuationSubring ℂ) (x : 𝓞 k) :
    A.valuation (σ (x : k)) ≤ 1 := by
  have hx : IsIntegral ℤ (σ (x : k)) := x.2.map σ.toIntAlgHom
  have hi : IsIntegral A (σ (x : k)) := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  rw [← hy]
  exact A.valuation_le_one y

/- English proof (translation)
Take `⟨h, hh, α, hα⟩` from `GlobalTheory.UnitOverP.exists_gen la`. Establish `hα0 : α ≠ 0`. Introduce and unpack `rfl`. Rewrite `hα` using `[Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `(pow_ne_zero h la.ne_bot) hα.symm`.

Establish `hmem : ∀ v : HeightOneSpectrum (𝓞 k), α ∈ v.asIdeal ↔ v = la`. Introduce `v`. Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `h1 : la.asIdeal ^ h ≤ v.asIdeal`.

Rewrite using `[← hα, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hv`. Establish `h2 : la.asIdeal ≤ v.asIdeal` using `v.isPrime.le_of_pow_le h1`. Conclude with `HeightOneSpectrum.ext ((la.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)`. Introduce and unpack `rfl`.

Establish `h1 : α ∈ Ideal.span {α}` using `Ideal.subset_span rfl`. Rewrite `h1` using `[hα]`. Conclude with `Ideal.pow_le_self hh.ne' h1`. Establish `hv1 : ∀ v : HeightOneSpectrum (𝓞 k), v ≠ la → v.valuation k (α : k) = 1` using `fun v hv => by`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`.

Conclude with `le_antisymm (v.intValuation_le_one α) (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))`. Establish `hαla : α ∈ la.asIdeal` using `(hmem la).2 rfl`. Establish `hαk0 : (α : k) ≠ 0` using `by exact_mod_cast hα0`. Take `⟨e, he⟩` from `exists_exp_nat ((Valuation.ne_zero_iff _).2 hαk0) (la.valuation_le_one α)`. Establish `dec : ∀ c : 𝓞 k, c ≠ 0 → ∃ (m : ℕ) (c' : 𝓞 k), c' ∉ la.asIdeal ∧ (c : k) ^ e = (α : k) ^ m * (c' : k) ∧ la.valuation k (c : k) = WithZero.exp (-(m : ℤ))`.

Introduce `c hc`. Establish `hck : (c : k) ≠ 0` using `by exact_mod_cast hc`. Take `⟨m, hm⟩` from `exists_exp_nat ((Valuation.ne_zero_iff _).2 hck) (la.valuation_le_one c)`. Use `set q : k := (c : k) ^ e / (α : k) ^ m with hq`. Establish `hqv : ∀ v : HeightOneSpectrum (𝓞 k), v.valuation k q ≤ 1`.

Introduce `v`. Distinguish the cases in `hv : v = la`. Substitute `hv` using the available equality. Rewrite using `[hq, map_div₀, map_pow, map_pow, hm, he, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]`. Rewrite using `[show e • (-(m : ℤ)) = m • (-(e : ℤ)) by simp [smul_eq_mul]; ring, div_self (by simp)]`.

Rewrite using `[hq, map_div₀, map_pow, map_pow, hv1 v hv, one_pow, div_one]`. Conclude with `pow_le_one' (v.valuation_le_one c) e`. Take `⟨c', hc'⟩` from `HeightOneSpectrum.mem_integers_of_valuation_le_one (K := k) q hqv`. Use `⟨m, c', ?_, ?_, hm⟩` and prove the remaining obligations. Introduce `hc'la`.

Establish `h1 : la.valuation k (c' : k) < 1` using `(la.valuation_lt_one_iff_mem (K := k) c').2 hc'la`. Rewrite `h1` using `[show la.valuation k (c' : k) = la.valuation k q from by rw [← hc']]`. Rewrite `h1` using `[hq, map_div₀, map_pow, map_pow, hm, he, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, show e • (-(m : ℤ)) = m • (-(e : ℤ)) by simp [smul_eq_mul]; ring, div_self (by simp)]`. Conclude with `lt_irrefl _ h1`. Establish `: ((c' : 𝓞 k) : k) = q` using `hc'`.

Rewrite using `[this, hq, mul_div_cancel₀ _ (pow_ne_zero _ hαk0)]`. Distinguish the cases in `hz0 : z = 0`. Rewrite using `[hz0, map_zero]`. Conclude with `zero_le'`. Take `⟨⟨a, b, hb⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors (𝓞 k)) z`.

Simplify using `only at hab`. Establish `hb0 : b ≠ 0` using `nonZeroDivisors.ne_zero hb`. Establish `hbk : (b : k) ≠ 0` using `by exact_mod_cast hb0`. Establish `hab' : z * (b : k) = (a : k)` using `hab`. Establish `ha0 : a ≠ 0`.

Introduce and unpack `rfl`. Establish `: z * (b : k) = 0` using `by rw [hab']; rfl`. Conclude with `hz0 ((mul_eq_zero.1 this).resolve_right hbk)`. Take `⟨ma, a', ha', hae, hav⟩` from `dec a ha0`. Take `⟨mb, b', hb', hbe, hbv⟩` from `dec b hb0`.

Establish `hw1 : ∀ x : 𝓞 k, x ∉ la.asIdeal → A.valuation (σ (x : k)) = 1` using `fun x hx => le_antisymm (val_le_one_int σ A x) (not_lt.1 fun h' => hx ((hA x).1 h'))`. Establish `hc : A.valuation (σ (α : k)) < 1` using `(hA α).2 hαla`. Establish `hc0 : A.valuation (σ (α : k)) ≠ 0` using `by simp [hαk0]`. Establish `key : A.valuation (σ z) ^ e * A.valuation (σ (α : k)) ^ mb = A.valuation (σ (α : k)) ^ ma`. Establish `e1 : σ ((a : k) ^ e) = σ z ^ e * σ ((b : k) ^ e)` using `by rw [map_pow, map_pow, ← mul_pow, ← map_mul, hab']`.

Rewrite `e1` using `[hae, hbe]`. Establish `e2` using `congrArg A.valuation e1`. Simplify using `only [map_mul, map_pow, hw1 a' ha', hw1 b' hb', mul_one] at e2`. Conclude with `e2.symm`. Establish `hle : mb ≤ ma`.

Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `h1 : A.valuation (σ (α : k)) ^ ma ≤ A.valuation (σ (α : k)) ^ mb`. Rewrite using `[← key]`. Conclude with `mul_le_of_le_one_left' (pow_le_one' hz e)`.

Establish `h2 : A.valuation (σ (α : k)) ^ mb < A.valuation (σ (α : k)) ^ ma` using `pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hc0) hc hlt`. Conclude with `absurd h1 (not_le.2 h2)`. Establish `hzv : la.valuation k z * la.valuation k (b : k) = la.valuation k (a : k)` using `by rw [← map_mul, hab']`. Rewrite `hzv` using `[hav, hbv]`. Establish `hexp : WithZero.exp (-(ma : ℤ)) ≤ WithZero.exp (-(mb : ℤ))` using `WithZero.exp_le_exp.2 (by omega)`.

Rewrite `hexp` using `[← hzv]`. Establish `hne : WithZero.exp (-(mb : ℤ)) ≠ 0` using `WithZero.exp_ne_zero`. Establish `hexp' : la.valuation k z * WithZero.exp (-(mb : ℤ)) ≤ 1 * WithZero.exp (-(mb : ℤ))` using `by rwa [one_mul]`. Use `first`. Consider the case `exact (mul_le_mul_right₀ hne).1 hexp'`.

Consider the case `exact le_of_mul_le_mul_right' hexp'`. Consider the case `exact (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 hne)).1 hexp'`.
-/
theorem val_le_one_of_mem {k : Type} [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k))
    (A : ValuationSubring ℂ) (hA : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal) (z : k)
    (hz : A.valuation (σ z) ≤ 1) : la.valuation k z ≤ 1 := by
  classical
  obtain ⟨h, hh, α, hα⟩ := GlobalTheory.UnitOverP.exists_gen la
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.2 rfl] at hα
    exact (pow_ne_zero h la.ne_bot) hα.symm
  have hmem : ∀ v : HeightOneSpectrum (𝓞 k), α ∈ v.asIdeal ↔ v = la := by
    intro v
    constructor
    · intro hv
      have h1 : la.asIdeal ^ h ≤ v.asIdeal := by
        rw [← hα, Ideal.span_le, Set.singleton_subset_iff]; exact hv
      have h2 : la.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
      exact HeightOneSpectrum.ext ((la.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    · rintro rfl
      have h1 : α ∈ Ideal.span {α} := Ideal.subset_span rfl
      rw [hα] at h1
      exact Ideal.pow_le_self hh.ne' h1
  have hv1 : ∀ v : HeightOneSpectrum (𝓞 k), v ≠ la → v.valuation k (α : k) = 1 := fun v hv => by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one α)
      (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))
  have hαla : α ∈ la.asIdeal := (hmem la).2 rfl
  have hαk0 : (α : k) ≠ 0 := by exact_mod_cast hα0
  obtain ⟨e, he⟩ := exists_exp_nat ((Valuation.ne_zero_iff _).2 hαk0) (la.valuation_le_one α)

  have dec : ∀ c : 𝓞 k, c ≠ 0 → ∃ (m : ℕ) (c' : 𝓞 k), c' ∉ la.asIdeal ∧ (c : k) ^ e = (α : k) ^ m * (c' : k) ∧
      la.valuation k (c : k) = WithZero.exp (-(m : ℤ)) := by
    intro c hc
    have hck : (c : k) ≠ 0 := by exact_mod_cast hc
    obtain ⟨m, hm⟩ := exists_exp_nat ((Valuation.ne_zero_iff _).2 hck) (la.valuation_le_one c)
    set q : k := (c : k) ^ e / (α : k) ^ m with hq
    have hqv : ∀ v : HeightOneSpectrum (𝓞 k), v.valuation k q ≤ 1 := by
      intro v
      by_cases hv : v = la
      · subst hv
        rw [hq, map_div₀, map_pow, map_pow, hm, he, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul]
        rw [show e • (-(m : ℤ)) = m • (-(e : ℤ)) by simp [smul_eq_mul]; ring, div_self (by simp)]
      · rw [hq, map_div₀, map_pow, map_pow, hv1 v hv, one_pow, div_one]
        exact pow_le_one' (v.valuation_le_one c) e
    obtain ⟨c', hc'⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (K := k) q hqv
    refine ⟨m, c', ?_, ?_, hm⟩
    · intro hc'la
      have h1 : la.valuation k (c' : k) < 1 := (la.valuation_lt_one_iff_mem (K := k) c').2 hc'la
      rw [show la.valuation k (c' : k) = la.valuation k q from by rw [← hc']] at h1
      rw [hq, map_div₀, map_pow, map_pow, hm, he, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul,
        show e • (-(m : ℤ)) = m • (-(e : ℤ)) by simp [smul_eq_mul]; ring, div_self (by simp)] at h1
      exact lt_irrefl _ h1
    · have : ((c' : 𝓞 k) : k) = q := hc'
      rw [this, hq, mul_div_cancel₀ _ (pow_ne_zero _ hαk0)]
  by_cases hz0 : z = 0
  · rw [hz0, map_zero]; exact zero_le'
  obtain ⟨⟨a, b, hb⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 k)) z
  simp only at hab
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbk : (b : k) ≠ 0 := by exact_mod_cast hb0
  have hab' : z * (b : k) = (a : k) := hab
  have ha0 : a ≠ 0 := by
    rintro rfl
    have : z * (b : k) = 0 := by rw [hab']; rfl
    exact hz0 ((mul_eq_zero.1 this).resolve_right hbk)
  obtain ⟨ma, a', ha', hae, hav⟩ := dec a ha0
  obtain ⟨mb, b', hb', hbe, hbv⟩ := dec b hb0
  have hw1 : ∀ x : 𝓞 k, x ∉ la.asIdeal → A.valuation (σ (x : k)) = 1 := fun x hx =>
    le_antisymm (val_le_one_int σ A x) (not_lt.1 fun h' => hx ((hA x).1 h'))
  have hc : A.valuation (σ (α : k)) < 1 := (hA α).2 hαla
  have hc0 : A.valuation (σ (α : k)) ≠ 0 := by simp [hαk0]

  have key : A.valuation (σ z) ^ e * A.valuation (σ (α : k)) ^ mb = A.valuation (σ (α : k)) ^ ma := by
    have e1 : σ ((a : k) ^ e) = σ z ^ e * σ ((b : k) ^ e) := by rw [map_pow, map_pow, ← mul_pow, ← map_mul, hab']
    rw [hae, hbe] at e1
    have e2 := congrArg A.valuation e1
    simp only [map_mul, map_pow, hw1 a' ha', hw1 b' hb', mul_one] at e2
    exact e2.symm
  have hle : mb ≤ ma := by
    by_contra hlt
    push_neg at hlt
    have h1 : A.valuation (σ (α : k)) ^ ma ≤ A.valuation (σ (α : k)) ^ mb := by
      rw [← key]
      exact mul_le_of_le_one_left' (pow_le_one' hz e)
    have h2 : A.valuation (σ (α : k)) ^ mb < A.valuation (σ (α : k)) ^ ma :=
      pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hc0) hc hlt
    exact absurd h1 (not_le.2 h2)
  have hzv : la.valuation k z * la.valuation k (b : k) = la.valuation k (a : k) := by rw [← map_mul, hab']
  rw [hav, hbv] at hzv
  have hexp : WithZero.exp (-(ma : ℤ)) ≤ WithZero.exp (-(mb : ℤ)) := WithZero.exp_le_exp.2 (by omega)
  rw [← hzv] at hexp
  have hne : WithZero.exp (-(mb : ℤ)) ≠ 0 := WithZero.exp_ne_zero
  have hexp' : la.valuation k z * WithZero.exp (-(mb : ℤ)) ≤ 1 * WithZero.exp (-(mb : ℤ)) := by rwa [one_mul]
  first
    | exact (mul_le_mul_right₀ hne).1 hexp'
    | exact le_of_mul_le_mul_right' hexp'
    | exact (mul_le_mul_iff_of_pos_right (zero_lt_iff.2 hne)).1 hexp'
end GlobalTheory.LevelSeriesScal

namespace GlobalTheory.LevelSeriesScal

open GlobalTheory.UnitOverP Formalism.L2.Host in

/- English proof (translation)
Take `⟨n, -, hχinf⟩` from `GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D _ χ _ hχ hex`. Take `⟨h, hh, α, hα⟩` from `exists_gen P`. Establish `hα0 : (α : D.host.E) ≠ 0`. Introduce `h0`. Establish `h1 : α = 0` using `by exact_mod_cast h0`.

Rewrite `hα` using `[h1, Ideal.span_singleton_eq_bot.2 rfl]`. Conclude with `(pow_ne_zero h P.ne_bot) hα.symm`. Use `set k : D.host.Eˣ := Units.mk0 _ hα0 with hk`. Establish `hmem : ∀ v : HeightOneSpectrum (𝓞 D.host.E), α ∈ v.asIdeal ↔ v = P`. Introduce `v`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Establish `h1 : P.asIdeal ^ h ≤ v.asIdeal`. Rewrite using `[← hα, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `hv`.

Establish `h2 : P.asIdeal ≤ v.asIdeal` using `v.isPrime.le_of_pow_le h1`. Conclude with `HeightOneSpectrum.ext ((P.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)`. Introduce and unpack `rfl`. Establish `h1 : α ∈ Ideal.span {α}` using `Ideal.subset_span rfl`. Rewrite `h1` using `[hα]`.

Conclude with `Ideal.pow_le_self hh.ne' h1`. Establish `hval : ∀ v : HeightOneSpectrum (𝓞 D.host.E), v.valuation D.host.E (k : D.host.E) = v.intValuation α` using `fun v => HeightOneSpectrum.valuation_of_algebraMap v α`. Establish `hv1 : ∀ v, v ≠ P → v.valuation D.host.E (k : D.host.E) = 1` using `fun v hv => by`. Rewrite using `[hval]`. Conclude with `le_antisymm (v.intValuation_le_one α) (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))`.

Establish `hord : ∀ v, v ≠ P → ordF v k = 0` using `fun v hv => by`. Unfold `ordF`. Rewrite using `[hv1 v hv]`. Simplify using the standard rewrite rules. Establish `hatFin : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ), Valued.v ((atFin v x : (v.adicCompletion D.host.E)ˣ) : v.adicCompletion D.host.E) = v.valuation D.host.E (x : D.host.E)` using `fun v x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : D.host.E)`.

Use `set N := ordF P k with hNdef`. Establish `hPv : P.valuation D.host.E (k : D.host.E) = WithZero.exp (-N)`. Establish `h0 : P.valuation D.host.E (k : D.host.E) ≠ 0` using `by simp`. Rewrite using `[hNdef, ordF, neg_neg]`. Conclude with `(WithZero.exp_log h0).symm`.

Establish `hN : 0 < N`. Establish `h1 : P.valuation D.host.E (k : D.host.E) < 1`. Rewrite using `[hval]`. Conclude with `(P.intValuation_lt_one_iff_mem α).2 ((hmem P).2 rfl)`. Rewrite `h1` using `[hPv, ← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use linear arithmetic over natural numbers and integers. Establish `hfin` using `GlobalTheory.Mem.UnrAe.finite_ramified χ`. Use `set S := insert P hfin.toFinset with hSdef`. Establish `hS : ∀ v, v ∉ S → χ.UnrAt v` using `fun v hv => by`. Assume the negation of the conclusion as `h'`.

Conclude with `hv (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h'))`. Establish `hpr` using `χ.productRule S hS k`. Establish `hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1` using `finprod_eq_one_of_forall_eq_one fun v => by`. Rewrite using `[finprod_eq_if]`. Use `split_ifs with hv`.

Both sides reduce to the same expression. Rewrite using `[hord v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), zpow_zero]`. Rewrite `hpr` using `[hfp, mul_one, ← Finset.mul_prod_erase S _ (Finset.mem_insert_self P _)]`. Use `set u : D.host.Eˣ := k * (unif P ^ N)⁻¹ with hudef`. Establish `hku : k = u * unif P ^ N` using `by rw [hudef, inv_mul_cancel_right]`.

Establish `hlocP : χ.locK P k = χ.locK P u * χ.val P ^ N`. Rewrite using `[hku, map_mul, map_zpow]`. Both sides reduce to the same expression. Establish `hu : IsUnitAt P (atFin P u)`. Establish `h1` using `unif_spec P`.

Unfold `IsUnifAt at h1`. Unfold `IsUnitAt`. Rewrite using `[hudef, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul, map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]`. Simplify using the standard rewrite rules. Establish `hroot : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ), IsUnitAt v (atFin v x) → A.valuation ((χ.locK v x : ℂˣ) : ℂ) = 1`.

Introduce `v x hx`. Take `⟨m, hm, hxm⟩` from `GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits _ χ v _ hx`. Apply `val_eq_one_of_pow A hm.ne'` to reduce the goal to its premises. Rewrite using `[← Units.val_pow_eq_pow_val, show χ.locK v x = χ.loc v (atFin v x) from rfl, hxm, Units.val_one, map_one]`. Establish `hw : ∀ τ, A.valuation (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) = 1`.

Introduce `τ`. Apply `val_eq_one_of_pow A two_ne_zero` to reduce the goal to its premises. Establish `hz : tauE D τ (k : D.host.E) ≠ 0` using `(map_ne_zero _).2 k.ne_zero`. Establish `hz' : starRingEnd ℂ (tauE D τ (k : D.host.E)) ≠ 0` using `(map_ne_zero _).2 hz`. Establish `hn : ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ) ^ 2 = tauE D τ (k : D.host.E) * starRingEnd ℂ (tauE D τ (k : D.host.E))`.

Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e : (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ 2 = tauE D τ (k : D.host.E) / starRingEnd ℂ (tauE D τ (k : D.host.E))`. Rewrite using `[div_pow, hn]`.

Clear the denominators using the available nonvanishing facts. Establish `h1 : A.valuation (tauE D τ (k : D.host.E)) = 1` using `GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα (tauE D τ)`. Establish `h2 : A.valuation (starRingEnd ℂ (tauE D τ (k : D.host.E))) = 1` using `GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα ((starRingEnd ℂ).comp (tauE D τ))`. Rewrite using `[e, map_div₀, h1, h2, div_one]`. Establish `hinfv : A.valuation ((χ.inf k : ℂˣ) : ℂ) = 1`.

Rewrite using `[hχinf k, map_prod]`. Conclude with `Finset.prod_eq_one fun τ _ => by rw [map_zpow₀, hw τ, _root_.one_zpow]`. Establish `hrest : A.valuation ((∏ v ∈ S.erase P, χ.locK v k : ℂˣ) : ℂ) = 1`. Rewrite using `[Units.coe_prod, map_prod]`. Use `Finset.prod_eq_one fun v hv => hroot v k ?_` and prove the remaining obligations.

Unfold `IsUnitAt`. Rewrite using `[hatFin]`. Conclude with `hv1 v (Finset.ne_of_mem_erase hv)`. Establish `key` using `congrArg (fun x : ℂˣ => A.valuation (x : ℂ)) hpr`. Simplify using `only [hlocP, Units.val_mul, map_mul, Units.val_one, map_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hinfv, hrest, hroot P u hu, one_mul, mul_one] at key`.

Establish `hvalP : A.valuation ((χ.val P : ℂˣ) : ℂ) = 1`. Take `⟨M, hM⟩` from `Int.eq_ofNat_of_zero_le hN.le`. Rewrite `key` using `[hM, zpow_natCast]`. Use `val_eq_one_of_pow A (m := M) (by have h3 := hN; rw [hM] at h3; omega) ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `key`. Establish `hfinal : A.valuation (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1`. Rewrite using `[map_mul, hvalP, GlobalTheory.T.valuation_sqrt_absNorm_eq_one' _ A p hp hpA P hpP, one_mul]`. Conclude with `⟨(A.valuation_le_one_iff _).1 hfinal.le, (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hfinal, inv_one])⟩`.
-/
theorem val_mul_sqrt_unit (D : D7) (c : (AE D)ˣ →* Circle) (χ : Formalism.L2.Host.HChar D.host.E) (hχ : ChrEq c χ)
    (ex : D.what₂.Tau → ℚ) (hex : ∀ τ, HasInfExp D c τ (ex τ)) (p : ℕ) (A : ValuationSubring ℂ) (hp : p.Prime)
    (hpA : (p : ℂ) ∈ A.nonunits) (P : HeightOneSpectrum (𝓞 D.host.E)) (hpP : ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ A ∧
      (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ A := by
  classical
  obtain ⟨n, -, hχinf⟩ := GlobalTheory.HeckeInfExp.hasInfQ_of_hasInfExp D _ χ _ hχ hex
  obtain ⟨h, hh, α, hα⟩ := exists_gen P
  have hα0 : (α : D.host.E) ≠ 0 := by
    intro h0
    have h1 : α = 0 := by exact_mod_cast h0
    rw [h1, Ideal.span_singleton_eq_bot.2 rfl] at hα
    exact (pow_ne_zero h P.ne_bot) hα.symm
  set k : D.host.Eˣ := Units.mk0 _ hα0 with hk
  have hmem : ∀ v : HeightOneSpectrum (𝓞 D.host.E), α ∈ v.asIdeal ↔ v = P := by
    intro v
    constructor
    · intro hv
      have h1 : P.asIdeal ^ h ≤ v.asIdeal := by
        rw [← hα, Ideal.span_le, Set.singleton_subset_iff]; exact hv
      have h2 : P.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
      exact HeightOneSpectrum.ext ((P.isMaximal.eq_of_le v.isPrime.ne_top h2).symm)
    · rintro rfl
      have h1 : α ∈ Ideal.span {α} := Ideal.subset_span rfl
      rw [hα] at h1
      exact Ideal.pow_le_self hh.ne' h1
  have hval : ∀ v : HeightOneSpectrum (𝓞 D.host.E), v.valuation D.host.E (k : D.host.E) = v.intValuation α := fun v =>
    HeightOneSpectrum.valuation_of_algebraMap v α
  have hv1 : ∀ v, v ≠ P → v.valuation D.host.E (k : D.host.E) = 1 := fun v hv => by
    rw [hval]
    exact le_antisymm (v.intValuation_le_one α)
      (not_lt.1 fun h' => hv ((hmem v).1 ((v.intValuation_lt_one_iff_mem α).1 h')))
  have hord : ∀ v, v ≠ P → ordF v k = 0 := fun v hv => by
    unfold ordF; rw [hv1 v hv]; simp
  have hatFin : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ),
      Valued.v ((atFin v x : (v.adicCompletion D.host.E)ˣ) : v.adicCompletion D.host.E) = v.valuation D.host.E (x : D.host.E) :=
    fun v x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : D.host.E)
  set N := ordF P k with hNdef
  have hPv : P.valuation D.host.E (k : D.host.E) = WithZero.exp (-N) := by
    have h0 : P.valuation D.host.E (k : D.host.E) ≠ 0 := by simp
    rw [hNdef, ordF, neg_neg]
    exact (WithZero.exp_log h0).symm
  have hN : 0 < N := by
    have h1 : P.valuation D.host.E (k : D.host.E) < 1 := by
      rw [hval]; exact (P.intValuation_lt_one_iff_mem α).2 ((hmem P).2 rfl)
    rw [hPv, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
    omega
  have hfin := GlobalTheory.Mem.UnrAe.finite_ramified χ
  set S := insert P hfin.toFinset with hSdef
  have hS : ∀ v, v ∉ S → χ.UnrAt v := fun v hv => by
    by_contra h'
    exact hv (Finset.mem_insert_of_mem (hfin.mem_toFinset.2 h'))
  have hpr := χ.productRule S hS k
  have hfp : (∏ᶠ (v : HeightOneSpectrum (𝓞 D.host.E)) (_ : v ∉ S), χ.val v ^ ordF v k) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v => by
      rw [finprod_eq_if]
      split_ifs with hv
      · rfl
      · rw [hord v (fun e => hv (e ▸ Finset.mem_insert_self _ _)), zpow_zero]
  rw [hfp, mul_one, ← Finset.mul_prod_erase S _ (Finset.mem_insert_self P _)] at hpr
  set u : D.host.Eˣ := k * (unif P ^ N)⁻¹ with hudef
  have hku : k = u * unif P ^ N := by rw [hudef, inv_mul_cancel_right]
  have hlocP : χ.locK P k = χ.locK P u * χ.val P ^ N := by
    rw [hku, map_mul, map_zpow]; rfl
  have hu : IsUnitAt P (atFin P u) := by
    have h1 := unif_spec P
    unfold IsUnifAt at h1
    unfold IsUnitAt
    rw [hudef, map_mul, map_inv, map_zpow, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h1, hatFin, hPv, ← WithZero.exp_zsmul, ← WithZero.exp_neg, ← WithZero.exp_add]
    simp
  have hroot : ∀ (v : HeightOneSpectrum (𝓞 D.host.E)) (x : D.host.Eˣ), IsUnitAt v (atFin v x) →
      A.valuation ((χ.locK v x : ℂˣ) : ℂ) = 1 := by
    intro v x hx
    obtain ⟨m, hm, hxm⟩ := GlobalTheory.T.heckeChar_loc_pow_eq_one_on_localUnits _ χ v _ hx
    apply val_eq_one_of_pow A hm.ne'
    rw [← Units.val_pow_eq_pow_val, show χ.locK v x = χ.loc v (atFin v x) from rfl, hxm, Units.val_one, map_one]
  have hw : ∀ τ, A.valuation (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) = 1 := by
    intro τ
    apply val_eq_one_of_pow A two_ne_zero
    have hz : tauE D τ (k : D.host.E) ≠ 0 := (map_ne_zero _).2 k.ne_zero
    have hz' : starRingEnd ℂ (tauE D τ (k : D.host.E)) ≠ 0 := (map_ne_zero _).2 hz
    have hn : ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ) ^ 2 = tauE D τ (k : D.host.E) * starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    have e : (tauE D τ (k : D.host.E) / ((‖tauE D τ (k : D.host.E)‖ : ℝ) : ℂ)) ^ 2 =
        tauE D τ (k : D.host.E) / starRingEnd ℂ (tauE D τ (k : D.host.E)) := by
      rw [div_pow, hn]; field_simp
    have h1 : A.valuation (tauE D τ (k : D.host.E)) = 1 := GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα (tauE D τ)
    have h2 : A.valuation (starRingEnd ℂ (tauE D τ (k : D.host.E))) = 1 :=
      GlobalTheory.T.valuation_embedding_generator_eq_one' _ A p hp hpA P hpP α h hα ((starRingEnd ℂ).comp (tauE D τ))
    rw [e, map_div₀, h1, h2, div_one]
  have hinfv : A.valuation ((χ.inf k : ℂˣ) : ℂ) = 1 := by
    rw [hχinf k, map_prod]
    exact Finset.prod_eq_one fun τ _ => by rw [map_zpow₀, hw τ, _root_.one_zpow]
  have hrest : A.valuation ((∏ v ∈ S.erase P, χ.locK v k : ℂˣ) : ℂ) = 1 := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_eq_one fun v hv => hroot v k ?_
    unfold IsUnitAt
    rw [hatFin]
    exact hv1 v (Finset.ne_of_mem_erase hv)
  have key := congrArg (fun x : ℂˣ => A.valuation (x : ℂ)) hpr
  simp only [hlocP, Units.val_mul, map_mul, Units.val_one, map_one, Units.val_zpow_eq_zpow_val, map_zpow₀, hinfv, hrest,
    hroot P u hu, one_mul, mul_one] at key
  have hvalP : A.valuation ((χ.val P : ℂˣ) : ℂ) = 1 := by
    obtain ⟨M, hM⟩ := Int.eq_ofNat_of_zero_le hN.le
    rw [hM, zpow_natCast] at key
    refine val_eq_one_of_pow A (m := M) (by have h3 := hN; rw [hM] at h3; omega) ?_
    rw [map_pow]; exact key
  have hfinal : A.valuation (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)) = 1 := by
    rw [map_mul, hvalP, GlobalTheory.T.valuation_sqrt_absNorm_eq_one' _ A p hp hpA P hpP, one_mul]
  exact ⟨(A.valuation_le_one_iff _).1 hfinal.le, (A.valuation_le_one_iff _).1 (by rw [map_inv₀, hfinal, inv_one])⟩

end GlobalTheory.LevelSeriesScal

namespace GlobalTheory.LevelSeriesScal

/- English proof (translation)
Rewrite using `[Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]`. Use `push_cast`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem natCast_cpow_half (n : ℕ) : ((n : ℕ) : ℂ) ^ (-(((-1 / 2 : ℝ)) : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg n)]
  push_cast
  congr 1
  ring

end GlobalTheory.LevelSeriesScal

/- English proof (translation)
Introduce `D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ b p bad hχ hp hbb hpb k _ _ σ la O hla hVR hVI h Λ e' Ps y hbad0 he hPs hgf hsupp hy hΛ`. Establish `hpair` using `hv.1`. Establish `hg : V.gram = 1` using `hpair.std`. Establish `hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank` using `SetLike.coe_injective ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans (hv.2.2.1.symm.trans hv.2.2.2.2.2.2.1))`. Establish `hbQ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal` using `fun Q hQ hb => hQ (by obtain ⟨t, rfl⟩ := hbb; rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb)`.

Establish `hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q` using `fun Q hQ => hχ.2.1 Q (hbQ Q hQ)`. Establish `hr` using `hχ.2.2`. Establish `hO : ∀ m : ℕ, Nat.Coprime m p → (m : ℂ)⁻¹ ∈ O` using `fun m hm => by`. Establish `h1` using `hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])`. Simplify using `using h1`.

Use `letI : Algebra k ℂ := σ.toAlgebra`. Take `⟨A, hA⟩` from `ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la`. Establish `hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal` using `hA`. Establish `hpA : (p : ℂ) ∈ A.nonunits`. Rewrite using `[ValuationSubring.mem_nonunits_iff]`.

Establish `h1` using `(hA' (p : 𝓞 k)).2 hla`. Simplify using `using h1`. Use `choose bW hbW using hpair.expW`. Establish `hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P → ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧ (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O`. Introduce `P hP _`.

Take `⟨x, hx⟩` from `hVI P (hu P hP)`. Establish `hx' : σ x = ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ)`. Rewrite using `[hx, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]`. Establish `hpP : ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `fun h1 => hP (by obtain ⟨t, rfl⟩ := hpb; rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h1)`. Take `⟨h1, h2⟩` from `GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW p A hp hpA P hpP`.

Rewrite `h1`, `h2` using `[← hx']`. Establish `hx0 : la.valuation k x ≤ 1` using `GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' x ((A.valuation_le_one_iff _).2 h1)`. Establish `hx1 : la.valuation k x⁻¹ ≤ 1` using `GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' x⁻¹ (by rw [map_inv₀]; exact (A.valuation_le_one_iff _).2 h2)`. Conclude with `⟨hx' ▸ hVR x hx0, by rw [← hx', ← map_inv₀]; exact hVR _ hx1⟩`. Take `⟨cc, c0, c1, c2, c3, c4⟩` from `GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e' Ps y he hsupp hy bad hPs χW χ hχ.1 hu hr`.

Use `set L := Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h) with hLdef`. Set `H` to `Formalism.L2.Pj.hostOfRecord D`. Establish `hbar : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E)` using `RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)`. Take `⟨m, m0, m1, m2, m3⟩` from `GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport D V hg hL h e' Ps bad he hPs hsupp`. Establish `hS : GenLat.SplitSupp H (⟨L⟩ : GenLat D.host.E V.rank)` using `⟨m, m0, m1, m2, fun P hP hm => by rw [hbar]; exact (m3 P hP hm).1⟩`.

Establish `hU` using `GlobalTheory.ClassScalarIn.unimod_hLat V hg (GlobalTheory.ExportSeries.finPt V h)`. Take `⟨kk, k0, hk⟩` from `GlobalTheory.LawOfSquares.index_eq H L cc hU hS (by show cc ⊔ cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤; rw [hbar]; exact c1) (by show Submodule.span _ (detSet L) * idlE (cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc`. Rewrite using `[hbar]`. Conclude with `c3)`. Establish `hΛL : Λ = GlobalTheory.ClassScalarCompare.conjLat L`.

Consider the cases of `Λ with`. Consider the case `mk La`. Use `congr 1`. Use extensionality with `v`. Conclude with `(hΛ v).trans GlobalTheory.ClassScalarCompare.mem_conjLat.symm`.

Establish `hidx : ((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index = Ideal.absNorm cc * kk ^ 2`. Use `GlobalTheory.ClassScalarCompare.stdIndex_conjLat L` as an intermediate fact. Rewrite `this` using `[← hΛL]`. Conclude with `this.trans hk`. Establish `hmp : ∃ a b : 𝓞 D.host.E, a * m + b * (p : 𝓞 D.host.E) = 1`.

Establish `htop : Ideal.span {m, (p : 𝓞 D.host.E)} = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hle⟩` from `Ideal.exists_le_maximal _ hne`. Establish `hm : m ∈ P` using `hle (Ideal.subset_span (Set.mem_insert _ _))`. Establish `hpP : (p : 𝓞 D.host.E) ∈ P` using `hle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))`.

Use `(m3 P hP.isPrime hm).2 ?_` and prove the remaining obligations. Take `⟨t, ht⟩` from `hpb`. Rewrite using `[ht, Nat.cast_mul]`. Conclude with `Ideal.mul_mem_right _ _ hpP`. Take `⟨a, b, hab⟩` from `Ideal.mem_span_pair.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Ideal.span {m, (p : 𝓞 D.host.E)})`.

Conclude with `⟨a, b, hab⟩`. Establish `hcop : Nat.Coprime (Ideal.absNorm cc * kk ^ 2) p`. Take `⟨a, b, hab⟩` from `hmp`. Establish `h0 : Ideal.absNorm cc * kk ^ 2 ≠ 0` using `mul_ne_zero (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (pow_ne_zero _ k0)`. Rewrite `h0`, the goal using `[← hk]`.

Use `haveI := Fact.mk hp`. Use `haveI : Finite (L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) := Nat.finite_of_card_ne_zero h0`. Use `((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_).symm` and prove the remaining obligations. Take `⟨x, hx⟩` from `exists_prime_addOrderOf_dvd_card' p hd`. Take `⟨y, rfl⟩` from `QuotientAddGroup.mk_surjective x`.

Establish `hpy : p • (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0`. Rewrite using `[← hx]`. Conclude with `addOrderOf_nsmul_eq_zero _`. Rewrite `hpy` using `[← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]`. Establish `h1 : ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank` using `(AddSubgroup.mem_addSubgroupOf.1 hpy).2`.

Establish `h2 : (m • (y : Fin V.rank → D.host.E)) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank` using `m1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self m) y.2)`. Establish `h3 : (y : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank`. Establish `e : (y : Fin V.rank → D.host.E) = a • (m • (y : Fin V.rank → D.host.E)) + b • ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E)`. Rewrite using `[AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul, smul_smul, ← add_smul, hab, one_smul]`. Rewrite using `[e]`.

Conclude with `add_mem (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)`. Establish `h4 : (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0` using `(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 ⟨y.2, h3⟩)`. Rewrite `hx` using `[h4, addOrderOf_zero]`. Conclude with `hp.one_lt.ne hx`. Establish `hNcop : Nat.Coprime (Ideal.absNorm cc) p` using `Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop`.

Establish `hkcop : Nat.Coprime kk p` using `(Nat.coprime_pow_left_iff two_pos _ _).1 (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop)`. Establish `hv'` using `GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring D.host.E χ O cc c0 fun P hP => by`. Establish `hb : ((bad : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal` using `fun hb => P.isPrime.ne_top (eq_top_iff.2 (c2 ▸ sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 hb)))`. Establish `hc : GlobalTheory.IdemSupport.cP P ≠ P` using `fun hc => by`. Use `P.isPrime.ne_top (eq_top_iff.2 (c1 ▸ sup_le hP ?_))` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `x hx`. Establish `h1 : x ∈ P.asIdeal` using `hP hx`. Rewrite `h1` using `[← hc]`. Conclude with `Ideal.mem_comap.2 ((GlobalTheory.IdemSupport.mem_cP P x).1 h1)`.

Conclude with `(hval P hb hc).2`. Take `⟨s, hs⟩` from `hodd`. Establish `hq : ((((Ideal.absNorm cc) ^ s * kk ^ (2 * s + 1) : ℕ) : ℂ))⁻¹ ∈ O` using `hO _ (Nat.Coprime.mul (hNcop.pow_left _) (hkcop.pow_left _))`. Unfold `clsScal`. Rewrite using `[hidx, hs, GlobalTheory.ClassScalarIn.sqrt_pow_odd, c4]`.

Use `O.mul_mem hv' hq using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Rewrite using `[mul_inv, mul_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.LevelSeries.clsScal_mem_valRing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (b l bad : ℕ), ChiData χW χ b → l.Prime → b ∣ bad → l ∣ bad → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → χ.ValuesIn (-1 / 2) σ → ∀ (h : GA D V) (Λ : GenLat D.host.E V.rank) (e' : AE D) (Ps : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), bad ≠ 0 → IsIdemSum e' Ps → (∀ PP ∈ Ps, ((bad : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → h ∈ GfC V → SuppAt e' V h → IsDetAt e' V h y → (∀ v, v ∈ Λ.La ↔ (fun j => star (v j)) ∈ Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h)) → clsScal χW y Λ W.rank ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hv hodd χ b p bad hχ hp hbb hpb k _ _ σ la O hla hVR hVI h Λ e' Ps y hbad0 he hPs
    hgf hsupp hy hΛ
  have hpair := hv.1
  have hg : V.gram = 1 := hpair.std
  have hL : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := SetLike.coe_injective
    ((GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice V).trans (hv.2.2.1.symm.trans hv.2.2.2.2.2.2.1))
  have hbQ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → ((b : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    fun Q hQ hb => hQ (by obtain ⟨t, rfl⟩ := hbb; rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ hb)
  have hu : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ((bad : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal → χ.UnrAt Q :=
    fun Q hQ => hχ.2.1 Q (hbQ Q hQ)
  have hr := hχ.2.2
  have hO : ∀ m : ℕ, Nat.Coprime m p → (m : ℂ)⁻¹ ∈ O := fun m hm => by
    have h1 := hVR ((m : k)⁻¹) (by rw [map_inv₀, GlobalTheory.ScalarUnit.val_natCast la hla hm, inv_one])
    simpa using h1
  letI : Algebra k ℂ := σ.toAlgebra
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_valuationSubring_over (Ω := ℂ) la
  have hA' : ∀ x : 𝓞 k, A.valuation (σ (x : k)) < 1 ↔ x ∈ la.asIdeal := hA
  have hpA : (p : ℂ) ∈ A.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff]
    have h1 := (hA' (p : 𝓞 k)).2 hla
    simpa using h1
  choose bW hbW using hpair.expW
  have hval : ∀ P : HeightOneSpectrum (𝓞 D.host.E), (bad : 𝓞 D.host.E) ∉ P.asIdeal → GlobalTheory.IdemSupport.cP P ≠ P →
      ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) ∈ O ∧
        (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O := by
    intro P hP _
    obtain ⟨x, hx⟩ := hVI P (hu P hP)
    have hx' : σ x = ((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ) := by
      rw [hx, Formalism.L2.Host.HChar.valTw, GlobalTheory.LevelSeriesScal.natCast_cpow_half]
    have hpP : ((p : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h1 =>
      hP (by obtain ⟨t, rfl⟩ := hpb; rw [Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h1)
    obtain ⟨h1, h2⟩ := GlobalTheory.LevelSeriesScal.val_mul_sqrt_unit D χW χ hχ.1 _ hbW p A hp hpA P hpP
    rw [← hx'] at h1 h2
    have hx0 : la.valuation k x ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' x ((A.valuation_le_one_iff _).2 h1)
    have hx1 : la.valuation k x⁻¹ ≤ 1 :=
      GlobalTheory.LevelSeriesScal.val_le_one_of_mem σ la A hA' x⁻¹ (by rw [map_inv₀]; exact (A.valuation_le_one_iff _).2 h2)
    exact ⟨hx' ▸ hVR x hx0, by rw [← hx', ← map_inv₀]; exact hVR _ hx1⟩
  obtain ⟨cc, c0, c1, c2, c3, c4⟩ := GlobalTheory.ClassScalarValue.exists_ideal V hg hL h e' Ps y he hsupp hy bad hPs
    χW χ hχ.1 hu hr
  set L := Bridge.hLat V (GlobalTheory.ExportSeries.finPt V h) with hLdef
  let H := Formalism.L2.Pj.hostOfRecord D
  have hbar : (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = (GlobalTheory.IdemSupport.cO D : 𝓞 D.host.E →+* 𝓞 D.host.E) :=
    RingHom.ext fun a => RingOfIntegers.ext (H.bar_eq a)
  obtain ⟨m, m0, m1, m2, m3⟩ := GlobalTheory.T.exists_elem_stdLattice_sandwich_splitSupport D V hg hL h e' Ps bad he hPs hsupp
  have hS : GenLat.SplitSupp H (⟨L⟩ : GenLat D.host.E V.rank) :=
    ⟨m, m0, m1, m2, fun P hP hm => by rw [hbar]; exact (m3 P hP hm).1⟩
  have hU := GlobalTheory.ClassScalarIn.unimod_hLat V hg (GlobalTheory.ExportSeries.finPt V h)
  obtain ⟨kk, k0, hk⟩ := GlobalTheory.LawOfSquares.index_eq H L cc hU hS
    (by show cc ⊔ cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) = ⊤; rw [hbar]; exact c1)
    (by show Submodule.span _ (detSet L) * idlE (cc.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E)) = idlE cc
        rw [hbar]; exact c3)
  have hΛL : Λ = GlobalTheory.ClassScalarCompare.conjLat L := by
    cases Λ with
    | mk La =>
      congr 1
      ext v
      exact (hΛ v).trans GlobalTheory.ClassScalarCompare.mem_conjLat.symm
  have hidx : ((Λ.La ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      Ideal.absNorm cc * kk ^ 2 := by
    have := GlobalTheory.ClassScalarCompare.stdIndex_conjLat L
    rw [← hΛL] at this
    exact this.trans hk
  have hmp : ∃ a b : 𝓞 D.host.E, a * m + b * (p : 𝓞 D.host.E) = 1 := by
    have htop : Ideal.span {m, (p : 𝓞 D.host.E)} = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hne
      have hm : m ∈ P := hle (Ideal.subset_span (Set.mem_insert _ _))
      have hpP : (p : 𝓞 D.host.E) ∈ P := hle (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      refine (m3 P hP.isPrime hm).2 ?_
      obtain ⟨t, ht⟩ := hpb
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hpP
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.1 (htop ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ Ideal.span {m, (p : 𝓞 D.host.E)})
    exact ⟨a, b, hab⟩
  have hcop : Nat.Coprime (Ideal.absNorm cc * kk ^ 2) p := by
    obtain ⟨a, b, hab⟩ := hmp
    have h0 : Ideal.absNorm cc * kk ^ 2 ≠ 0 :=
      mul_ne_zero (fun h0 => c0 (Ideal.absNorm_eq_zero_iff.1 h0)) (pow_ne_zero _ k0)
    rw [← hk] at h0 ⊢
    haveI := Fact.mk hp
    haveI : Finite (L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) :=
      Nat.finite_of_card_ne_zero h0
    refine ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_).symm
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' p hd
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hpy : p • (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 := by
      rw [← hx]; exact addOrderOf_nsmul_eq_zero _
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff] at hpy
    have h1 : ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := (AddSubgroup.mem_addSubgroupOf.1 hpy).2
    have h2 : (m • (y : Fin V.rank → D.host.E)) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank :=
      m1 (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self m) y.2)
    have h3 : (y : Fin V.rank → D.host.E) ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
      have e : (y : Fin V.rank → D.host.E) = a • (m • (y : Fin V.rank → D.host.E)) + b • ((p • y : L.toAddSubgroup) : Fin V.rank → D.host.E) := by
        rw [AddSubgroupClass.coe_nsmul, ← Nat.cast_smul_eq_nsmul (𝓞 D.host.E), smul_smul, smul_smul, ← add_smul,
          hab, one_smul]
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ h2) (Submodule.smul_mem _ _ h1)
    have h4 : (QuotientAddGroup.mk y : L.toAddSubgroup ⧸ (L ⊓ Formalism.L2.Pj.stdLat D.host.E V.rank).toAddSubgroup.addSubgroupOf L.toAddSubgroup) = 0 :=
      (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_addSubgroupOf.2 ⟨y.2, h3⟩)
    rw [h4, addOrderOf_zero] at hx
    exact hp.one_lt.ne hx
  have hNcop : Nat.Coprime (Ideal.absNorm cc) p := Nat.Coprime.coprime_dvd_left (dvd_mul_right _ _) hcop
  have hkcop : Nat.Coprime kk p :=
    (Nat.coprime_pow_left_iff two_pos _ _).1 (Nat.Coprime.coprime_dvd_left (dvd_mul_left _ _) hcop)
  have hv' := GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring D.host.E χ O cc c0 fun P hP => by
    have hb : ((bad : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun hb =>
      P.isPrime.ne_top (eq_top_iff.2 (c2 ▸ sup_le hP ((Ideal.span_singleton_le_iff_mem _).2 hb)))
    have hc : GlobalTheory.IdemSupport.cP P ≠ P := fun hc => by
      refine P.isPrime.ne_top (eq_top_iff.2 (c1 ▸ sup_le hP ?_))
      rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : x ∈ P.asIdeal := hP hx
      rw [← hc] at h1
      exact Ideal.mem_comap.2 ((GlobalTheory.IdemSupport.mem_cP P x).1 h1)
    exact (hval P hb hc).2
  obtain ⟨s, hs⟩ := hodd
  have hq : ((((Ideal.absNorm cc) ^ s * kk ^ (2 * s + 1) : ℕ) : ℂ))⁻¹ ∈ O :=
    hO _ (Nat.Coprime.mul (hNcop.pow_left _) (hkcop.pow_left _))
  unfold clsScal
  rw [hidx, hs, GlobalTheory.ClassScalarIn.sqrt_pow_odd, c4]
  convert O.mul_mem hv' hq using 1
  push_cast
  rw [mul_inv, mul_inv]
  ring
