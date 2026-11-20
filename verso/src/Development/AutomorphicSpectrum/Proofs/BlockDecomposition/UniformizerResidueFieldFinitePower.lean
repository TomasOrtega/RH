import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEmbeddingRangeEqField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSubLeOfNear
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteQuotientPow
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical
open GlobalTheory.CompanionTheory.LTPer.Tilt

namespace GlobalTheory.CompanionTheory.LTPer.Tilt

/- English proof (translation)
Introduce `l _ K π hπ`. Take `⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩` from `GlobalTheory.LocalIntegers.good_integers l K`. Establish `hlp : l.Prime` using `Fact.out`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K))`. Introduce `a b hab`.

Establish `h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b` using `congrArg Subtype.val hab`. Rewrite `h1` using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b]`. Conclude with `IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)`. Establish `hi : Algebra.IsIntegral ℤ_[l] ↥(OL K)` using `integralClosure.AlgebraIsIntegral`. Establish `hf : FaithfulSMul ℤ_[l] ↥(OL K)` using `(faithfulSMul_iff_algebraMap_injective _ _).mpr hinj`.

Establish `hl : ¬ IsUnit ((l : ℕ) : ↥(OL K))`. Introduce `hu`. Rewrite `hu` using `[← map_natCast (algebraMap ℤ_[l] ↥(OL K))]`. Conclude with `PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)`. Establish `hdvd : π ∣ ((l : ℕ) : ↥(OL K))`.

Establish `hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K)` using `hl`. Rewrite `hm` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Then use the resulting hypothesis. Establish `hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π}`. Rewrite using `[pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]`. Conclude with `hdvd`.

Establish `hmax : (Ideal.span {π}).IsMaximal`. Rewrite using `[← hπ.maximalIdeal_eq]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal _`. Establish `hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π})`. Use `hfin 1` as an intermediate fact.

Conclude with `Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)`. Use `⟨hmax, hfinQ, ?_⟩` and prove the remaining obligations. Use `letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _`. Use `haveI : Fintype (↥(OL K) ⧸ Ideal.span {π}) := Fintype.ofFinite _`. Establish `hz : ((l : ℕ) : ↥(OL K) ⧸ Ideal.span {π}) = 0`.

Rewrite using `[← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `hdvd`. Use `haveI : CharP (↥(OL K) ⧸ Ideal.span {π}) l := (CharP.charP_iff_prime_eq_zero hlp).2 hz`. Take `⟨n, -, hn⟩` from `FiniteField.card (↥(OL K) ⧸ Ideal.span {π}) l`. Use `⟨n, n.pos, ?_⟩` and prove the remaining obligations.

Rewrite using `[qOf, Nat.card_eq_fintype_card, hn]`.
-/
theorem resfield_of_irreducible : ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) (π : ↥(OL K)), Irreducible π →
    (Ideal.span {π}).IsMaximal ∧ Finite (↥(OL K) ⧸ Ideal.span {π}) ∧ ∃ f : ℕ, 0 < f ∧ qOf π = l ^ f := by
  intro l _ K π hπ
  obtain ⟨⟨⟨hD, hV, -⟩, -⟩, hfin⟩ := GlobalTheory.LocalIntegers.good_integers l K
  have hlp : l.Prime := Fact.out
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL K)) := by
    intro a b hab
    have h1 : algebraMap ℤ_[l] ↥K.1 a = algebraMap ℤ_[l] ↥K.1 b := congrArg Subtype.val hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1,
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1 b] at h1
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] ↥K.1).injective h1)
  have hi : Algebra.IsIntegral ℤ_[l] ↥(OL K) := integralClosure.AlgebraIsIntegral
  have hf : FaithfulSMul ℤ_[l] ↥(OL K) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hl : ¬ IsUnit ((l : ℕ) : ↥(OL K)) := by
    intro hu
    rw [← map_natCast (algebraMap ℤ_[l] ↥(OL K))] at hu
    exact PadicInt.irreducible_p.not_isUnit (isUnit_of_map_unit _ _ hu)
  have hdvd : π ∣ ((l : ℕ) : ↥(OL K)) := by
    have hm : ((l : ℕ) : ↥(OL K)) ∈ IsLocalRing.maximalIdeal ↥(OL K) := hl
    rwa [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
  have hle : Ideal.span {((l : ℕ) : ↥(OL K)) ^ 1} ≤ Ideal.span {π} := by
    rw [pow_one, Ideal.span_singleton_le_iff_mem, Ideal.mem_span_singleton]
    exact hdvd
  have hmax : (Ideal.span {π}).IsMaximal := by
    rw [← hπ.maximalIdeal_eq]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hfinQ : Finite (↥(OL K) ⧸ Ideal.span {π}) := by
    have := hfin 1
    exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  refine ⟨hmax, hfinQ, ?_⟩
  letI : Field (↥(OL K) ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  haveI : Fintype (↥(OL K) ⧸ Ideal.span {π}) := Fintype.ofFinite _
  have hz : ((l : ℕ) : ↥(OL K) ⧸ Ideal.span {π}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {π})), Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton]
    exact hdvd
  haveI : CharP (↥(OL K) ⧸ Ideal.span {π}) l := (CharP.charP_iff_prime_eq_zero hlp).2 hz
  obtain ⟨n, -, hn⟩ := FiniteField.card (↥(OL K) ⧸ Ideal.span {π}) l
  refine ⟨n, n.pos, ?_⟩
  rw [qOf, Nat.card_eq_fintype_card, hn]

end GlobalTheory.CompanionTheory.LTPer.Tilt
