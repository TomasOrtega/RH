import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqZeroOfForallLeExp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemPowHeightOneIdealIffDvdEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SurjectiveAlgebraMapAdicCompletionCompleteDvrStatement

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
open WithZero

namespace GlobalTheory.DenseCompl

/- English proof (translation)
Introduce `E _ _ P W Qq _ _ _ _ _ _ p hp hc ρ h1 h2`. Use `set v := closedPoint W`. Establish `hint : ∀ x : 𝓞 E, v.valuation Qq (ρ x) = P.valuation E x`. Introduce `x`. Take `⟨y, hy, -⟩` from `h1 x`.

Establish `hx : (x : E) = algebraMap (𝓞 E) E x` using `rfl`. Rewrite using `[hy, hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `key : ∀ k : ℕ, P.intValuation x ≤ exp (-(k : ℤ)) ↔ v.intValuation y ≤ exp (-(k : ℤ))`. Introduce `k`. Rewrite using `[HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem, asIdeal_eq_span hp v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]`.

Conclude with `GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding P p hp ρ h1 h2 x y k hy`. Conclude with `le_antisymm (le_of_forall_le_exp (P.intValuation_le_one x) fun k hk => (key k).1 hk) (le_of_forall_le_exp (v.intValuation_le_one y) fun k hk => (key k).2 hk)`. Establish `hval : ∀ x : E, v.valuation Qq (ρ x) = P.valuation E x`. Introduce `x`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := 𝓞 E) x`.

Rewrite using `[map_div₀, map_div₀, map_div₀]`. Conclude with `congrArg₂ (· / ·) (hint a) (hint b)`. Establish `hf : ∀ x : E, Valued.v (((algebraMap Qq (v.adicCompletion Qq)).comp ρ) x) = P.valuation E x` using `fun x => by rw [RingHom.comp_apply, GlobalTheory.Idele.valued_algebraMap, hval]`. Take `⟨ψ, -, hψ, hψv⟩` from `exists_extension P v _ hf`. Establish `hψW : ∀ y : W, algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) ∈ Set.range ψ`.

Introduce `y`. Use `choose x z hxz using fun n : ℕ => h2 y n`. Set `u : ℕ → P.adicCompletion E` to `fun n => algebraMap E _ (x n : E)`. Establish `hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ))`. Introduce `m n hnm`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le hnm`. Simplify using `only [u]`. Rewrite using `[← map_sub, GlobalTheory.Idele.valued_algebraMap, ← hval, map_sub, hxz, hxz, ← map_sub]`. Use `(exists_eq_pow_mul_iff hp v _ n).1 ⟨(p : W) ^ k * z (n + k) - z n, ?_⟩` and prove the remaining obligations. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨t, ht⟩` from `GlobalTheory.Idele.exists_limit P u hu`. Use `⟨t, ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`. Use `Valued.v.zero_iff.1 (eq_zero_of_forall_le_exp fun n => ?_)` and prove the remaining obligations.

Establish `e : ψ t - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) = ψ (t - u n) + algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq ((p : W) ^ n * z n))`. Rewrite using `[map_sub, hψ, RingHom.comp_apply, hxz, map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Use `(Valuation.map_add _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[hψv]`. Conclude with `ht n`. Rewrite using `[GlobalTheory.Idele.valued_algebraMap]`. Conclude with `(exists_eq_pow_mul_iff hp v _ n).1 ⟨z n, rfl⟩`. Establish `hι` using `GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr (Qq := Qq) (p : W) hp hc v`.

Establish `hsurj : Function.Surjective ψ`. Introduce `a`. Take `⟨q, rfl⟩` from `hι a`. Take `⟨a, b, -, rfl⟩` from `IsFractionRing.div_surjective (A := W) q`. Take `⟨s, hs⟩` from `hψW a`.

Take `⟨t, ht⟩` from `hψW b`. Conclude with `⟨s / t, by rw [map_div₀, hs, ht, map_div₀]⟩`. Set `eψ` to `RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩`. Set `eι` to `RingEquiv.ofBijective (algebraMap Qq (v.adicCompletion Qq)) ⟨(algebraMap Qq (v.adicCompletion Qq)).injective, hι⟩`. Establish `hφ : ∀ z, algebraMap Qq (v.adicCompletion Qq) ((eψ.trans eι.symm) z) = ψ z` using `fun z => eι.apply_symm_apply (ψ z)`.

Establish `hS : ∀ (n : ℕ) (z : P.adicCompletion E), (∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)) ↔ Valued.v z ≤ exp (-(n : ℤ))`. Introduce `n z`. Rewrite using `[exists_eq_pow_mul_iff hp v, ← GlobalTheory.Idele.valued_algebraMap v, hφ, hψv]`. Use `⟨eψ.trans eι.symm, fun x => ?_, fun n => ?_, fun U hU => ?_⟩` and prove the remaining obligations. Apply `(algebraMap Qq (v.adicCompletion Qq)).injective` to reduce the goal to its premises.

Rewrite using `[hφ, hψ]`. Both sides reduce to the same expression. Establish `e : {z : P.adicCompletion E | ∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)} = {z | Valued.v z ≤ exp (-(n : ℤ))}` using `Set.ext fun z => hS n z`. Rewrite using `[e]`. Conclude with `GlobalTheory.Idele.isOpen_valued_le P (-(n : ℤ))`.

Take `⟨γ, hγ⟩` from `Valued.mem_nhds_zero.1 hU`. Take `⟨n, hn⟩` from `GlobalTheory.Idele.exists_exp_neg_lt (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)`. Use `⟨n, fun z hz => hγ ?_⟩` and prove the remaining obligations. Establish `hz'` using `(hS n z).1 hz`. Simplify using `only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]`.

Conclude with `hz'.trans_lt hn`.
-/
theorem completion_ringEquiv_of_dense : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (hc : IsAdicComplete (Ideal.span {(p : W)}) W) (ρ : E →+* Qq) (h1 : ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Qq y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)), ∃ φ : P.adicCompletion E ≃+* Qq, (∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) ∧ (∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) ∧ ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U := by
  intro E _ _ P W Qq _ _ _ _ _ _ p hp hc ρ h1 h2
  classical
  set v := closedPoint W
  have hint : ∀ x : 𝓞 E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨y, hy, -⟩ := h1 x
    have hx : (x : E) = algebraMap (𝓞 E) E x := rfl
    rw [hy, hx, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
    have key : ∀ k : ℕ, P.intValuation x ≤ exp (-(k : ℤ)) ↔ v.intValuation y ≤ exp (-(k : ℤ)) := by
      intro k
      rw [HeightOneSpectrum.intValuation_le_pow_iff_mem, HeightOneSpectrum.intValuation_le_pow_iff_mem,
        asIdeal_eq_span hp v, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact GlobalTheory.T.mem_pow_heightOneIdeal_iff_dvd_embedding P p hp ρ h1 h2 x y k hy
    exact le_antisymm (le_of_forall_le_exp (P.intValuation_le_one x) fun k hk => (key k).1 hk)
      (le_of_forall_le_exp (v.intValuation_le_one y) fun k hk => (key k).2 hk)
  have hval : ∀ x : E, v.valuation Qq (ρ x) = P.valuation E x := by
    intro x
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hint a) (hint b)
  have hf : ∀ x : E, Valued.v (((algebraMap Qq (v.adicCompletion Qq)).comp ρ) x) = P.valuation E x :=
    fun x => by rw [RingHom.comp_apply, GlobalTheory.Idele.valued_algebraMap, hval]
  obtain ⟨ψ, -, hψ, hψv⟩ := exists_extension P v _ hf
  have hψW : ∀ y : W, algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) ∈ Set.range ψ := by
    intro y
    choose x z hxz using fun n : ℕ => h2 y n
    let u : ℕ → P.adicCompletion E := fun n => algebraMap E _ (x n : E)
    have hu : ∀ m n : ℕ, n ≤ m → Valued.v (u m - u n) ≤ exp (-(n : ℤ)) := by
      intro m n hnm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
      simp only [u]
      rw [← map_sub, GlobalTheory.Idele.valued_algebraMap, ← hval, map_sub, hxz, hxz, ← map_sub]
      refine (exists_eq_pow_mul_iff hp v _ n).1 ⟨(p : W) ^ k * z (n + k) - z n, ?_⟩
      congr 1
      ring
    obtain ⟨t, ht⟩ := GlobalTheory.Idele.exists_limit P u hu
    refine ⟨t, ?_⟩
    rw [← sub_eq_zero]
    refine Valued.v.zero_iff.1 (eq_zero_of_forall_le_exp fun n => ?_)
    have e : ψ t - algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq y) =
        ψ (t - u n) + algebraMap Qq (v.adicCompletion Qq) (algebraMap W Qq ((p : W) ^ n * z n)) := by
      rw [map_sub, hψ, RingHom.comp_apply, hxz, map_add, map_add]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · rw [hψv]
      exact ht n
    · rw [GlobalTheory.Idele.valued_algebraMap]
      exact (exists_eq_pow_mul_iff hp v _ n).1 ⟨z n, rfl⟩
  have hι := GlobalTheory.T.surjective_algebraMap_adicCompletion_complete_dvr (Qq := Qq) (p : W) hp hc v
  have hsurj : Function.Surjective ψ := by
    intro a
    obtain ⟨q, rfl⟩ := hι a
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := W) q
    obtain ⟨s, hs⟩ := hψW a
    obtain ⟨t, ht⟩ := hψW b
    exact ⟨s / t, by rw [map_div₀, hs, ht, map_div₀]⟩
  let eψ := RingEquiv.ofBijective ψ ⟨ψ.injective, hsurj⟩
  let eι := RingEquiv.ofBijective (algebraMap Qq (v.adicCompletion Qq))
    ⟨(algebraMap Qq (v.adicCompletion Qq)).injective, hι⟩
  have hφ : ∀ z, algebraMap Qq (v.adicCompletion Qq) ((eψ.trans eι.symm) z) = ψ z :=
    fun z => eι.apply_symm_apply (ψ z)
  have hS : ∀ (n : ℕ) (z : P.adicCompletion E),
      (∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)) ↔ Valued.v z ≤ exp (-(n : ℤ)) := by
    intro n z
    rw [exists_eq_pow_mul_iff hp v, ← GlobalTheory.Idele.valued_algebraMap v, hφ, hψv]
  refine ⟨eψ.trans eι.symm, fun x => ?_, fun n => ?_, fun U hU => ?_⟩
  · apply (algebraMap Qq (v.adicCompletion Qq)).injective
    rw [hφ, hψ]
    rfl
  · have e : {z : P.adicCompletion E | ∃ w : W, (eψ.trans eι.symm) z = algebraMap W Qq ((p : W) ^ n * w)} =
        {z | Valued.v z ≤ exp (-(n : ℤ))} := Set.ext fun z => hS n z
    rw [e]
    exact GlobalTheory.Idele.isOpen_valued_le P (-(n : ℤ))
  · obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hU
    obtain ⟨n, hn⟩ := GlobalTheory.Idele.exists_exp_neg_lt
      (γ := MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by simp)
    refine ⟨n, fun z hz => hγ ?_⟩
    have hz' := (hS n z).1 hz
    simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
    exact hz'.trans_lt hn

end GlobalTheory.DenseCompl
