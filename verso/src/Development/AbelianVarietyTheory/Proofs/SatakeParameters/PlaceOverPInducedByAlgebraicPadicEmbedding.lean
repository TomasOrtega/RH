import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TypePrimeBadPrimesLevelsHypotheses
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicNumbersPadicPlacesFacts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.DatumJets.Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]

/- English proof (translation)
The claim follows from `GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y) exact Subsingleton.elim _ _)`.
-/
theorem norm_int_le (ι : K →+* ℂ_[p]) (y : 𝓞 K) : ‖ι (y : K)‖ ≤ 1 :=
  GlobalTheory.MomPlace.norm_le_one_of_isIntegral_int (by
    convert map_isIntegral_int ι (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

def smallIdeal (ι : K →+* ℂ_[p]) : Ideal (𝓞 K) where
  carrier := {y | ‖ι (y : K)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have : ι ((a + b : 𝓞 K) : K) = ι (a : K) + ι (b : K) := by simp
    rw [this]
    exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have : ι ((c • a : 𝓞 K) : K) = ι (c : K) * ι (a : K) := by simp
    rw [this, norm_mul]
    have h1 := norm_int_le ι c
    nlinarith [norm_nonneg (ι (c : K)), norm_nonneg (ι (a : K))]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_smallIdeal (ι : K →+* ℂ_[p]) (y : 𝓞 K) : y ∈ smallIdeal ι ↔ ‖ι (y : K)‖ < 1 := Iff.rfl

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ideal.ne_top_iff_one, mem_smallIdeal]`. Simplify using the standard rewrite rules. Introduce `a b hab`. Rewrite `hab` using `[mem_smallIdeal]`.

Rewrite using `[mem_smallIdeal, mem_smallIdeal]`. Establish `: ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K)` using `by simp`. Rewrite `hab` using `[this, norm_mul]`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Use polynomial arithmetic with `[hcon.1, hcon.2]`.
-/
theorem smallIdeal_isPrime (ι : K →+* ℂ_[p]) : (smallIdeal ι).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_smallIdeal]
    simp
  · intro a b hab
    rw [mem_smallIdeal] at hab
    rw [mem_smallIdeal, mem_smallIdeal]
    have : ι ((a * b : 𝓞 K) : K) = ι (a : K) * ι (b : K) := by simp
    rw [this, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    nlinarith [hcon.1, hcon.2]

/- English proof (translation)
Assume the negation of the conclusion as `hnd`. Establish `hc : Nat.Coprime q M` using `(Nat.Prime.coprime_iff_not_dvd hq).2 hnd`. Take `⟨u, v, huv⟩ : IsCoprime (q : R) (M : R)` from `Nat.Coprime.cast hc`. Conclude with `hI ((Ideal.eq_top_iff_one _).2 (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))`.
-/
theorem dvd_of_natCast_mem {R : Type*} [CommRing R] (I : Ideal R) (hI : I ≠ ⊤) {q M : ℕ} (hq : q.Prime)
    (h1 : (q : R) ∈ I) (h2 : (M : R) ∈ I) : q ∣ M := by
  by_contra hnd
  have hc : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).2 hnd
  obtain ⟨u, v, huv⟩ : IsCoprime (q : R) (M : R) := Nat.Coprime.cast hc
  exact hI ((Ideal.eq_top_iff_one _).2
    (huv ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)))

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' p (p : ℚ_[p])`. Establish `h2 : ‖(p : ℚ_[p])‖ < 1` using `Padic.norm_p_lt_one`. Rewrite `h2` using `[← h]`. Simplify using `using h2`.
-/
theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p])`. Introduce `σ hle`. Conclude with `hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)`.

Establish `σ0 : K →ₐ[ℚ] ℂ_[p]` using `IsAlgClosed.lift`. Establish `hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆ ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])), (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K)))`. Rewrite using `[Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]`. Introduce and unpack `⟨σ, -, hle⟩`. Conclude with `hnle σ hle`.

Take `⟨x, hxw, hx⟩` from `Set.not_subset.1 hav`. Establish `hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖`. Introduce `σ`. Assume the negation of the conclusion as `hlt`. Conclude with `hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))`.

Establish `hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal`. Establish `h1` using `Ideal.absNorm_mem (Ideal.span {x})`. Rewrite `h1` using `[Ideal.absNorm_span_singleton]`. Conclude with `(Ideal.span_singleton_le_iff_mem _).2 hxw h1`. Establish `hpN : p ∣ (Algebra.norm ℤ x).natAbs` using `dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN`.

Take `⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x` from `Int.natCast_dvd.2 hpN`. Establish `hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K)`. Rewrite using `[← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]`. Simplify using the standard rewrite rules. Establish `h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖`.

Rewrite using `[hprod, norm_prod]`. Conclude with `Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl fun σ _ => hxσ σ`. Establish `h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p])`. Rewrite using `[hm]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1` using `IsUltrametricDist.norm_intCast_le_one _ m`. Rewrite `h1` using `[h2, norm_mul]`. Establish `h4` using `norm_p_lt_one (p := p)`. Use polynomial arithmetic with `[norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]`.
-/
theorem exists_embedding (w : HeightOneSpectrum (𝓞 K)) (hw : (p : 𝓞 K) ∈ w.asIdeal) :
    ∃ ι : K →+* ℂ_[p], w.asIdeal = smallIdeal ι := by
  by_contra hcon
  push Not at hcon
  have hnle : ∀ σ : K →ₐ[ℚ] ℂ_[p], ¬ w.asIdeal ≤ smallIdeal (σ : K →+* ℂ_[p]) := by
    intro σ hle
    exact hcon (σ : K →+* ℂ_[p]) (w.isMaximal.eq_of_le (smallIdeal_isPrime _).ne_top hle)
  have σ0 : K →ₐ[ℚ] ℂ_[p] := IsAlgClosed.lift
  have hav : ¬ ((w.asIdeal : Set (𝓞 K)) ⊆
      ⋃ σ ∈ ((Finset.univ : Finset (K →ₐ[ℚ] ℂ_[p])) : Set (K →ₐ[ℚ] ℂ_[p])),
        (smallIdeal (σ : K →+* ℂ_[p]) : Set (𝓞 K))) := by
    rw [Ideal.subset_union_prime σ0 σ0 (fun σ _ _ _ => smallIdeal_isPrime _)]
    rintro ⟨σ, -, hle⟩
    exact hnle σ hle
  obtain ⟨x, hxw, hx⟩ := Set.not_subset.1 hav
  have hxσ : ∀ σ : K →ₐ[ℚ] ℂ_[p], 1 ≤ ‖σ (x : K)‖ := by
    intro σ
    by_contra hlt
    exact hx (Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ σ)) (not_le.1 hlt))
  have hN : ((Algebra.norm ℤ x).natAbs : 𝓞 K) ∈ w.asIdeal := by
    have h1 := Ideal.absNorm_mem (Ideal.span {x})
    rw [Ideal.absNorm_span_singleton] at h1
    exact (Ideal.span_singleton_le_iff_mem _).2 hxw h1
  have hpN : p ∣ (Algebra.norm ℤ x).natAbs :=
    dvd_of_natCast_mem w.asIdeal w.isPrime.ne_top Fact.out hw hN
  obtain ⟨m, hm⟩ : (p : ℤ) ∣ Algebra.norm ℤ x := Int.natCast_dvd.2 hpN
  have hprod : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = ∏ σ : K →ₐ[ℚ] ℂ_[p], σ (x : K) := by
    rw [← Algebra.norm_eq_prod_embeddings ℚ ℂ_[p] (x : K), ← Algebra.coe_norm_int x]
    simp
  have h1 : 1 ≤ ‖((Algebra.norm ℤ x : ℤ) : ℂ_[p])‖ := by
    rw [hprod, norm_prod]
    exact Finset.prod_induction _ (fun t : ℝ => 1 ≤ t) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
      le_rfl fun σ _ => hxσ σ
  have h2 : ((Algebra.norm ℤ x : ℤ) : ℂ_[p]) = (p : ℂ_[p]) * ((m : ℤ) : ℂ_[p]) := by
    rw [hm]; push_cast; ring
  have h3 : ‖((m : ℤ) : ℂ_[p])‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ m
  rw [h2, norm_mul] at h1
  have h4 := norm_p_lt_one (p := p)
  nlinarith [norm_nonneg (p : ℂ_[p]), norm_nonneg ((m : ℤ) : ℂ_[p])]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Establish `hgt : 1 < w.valuation K x` using `not_le.1 hcon`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hgt`.

Establish `hinv : w.valuation K x⁻¹ < 1`. Rewrite using `[map_inv₀]`. Conclude with `inv_lt_one_of_one_lt₀ hgt`. Take `⟨n, d, h⟩` from `w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le`. Establish `hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖` using `not_lt.1 fun hlt => d.2 ((hw _).2 hlt)`.

Establish `hn : n ∈ w.asIdeal`. Rewrite using `[← w.valuation_lt_one_iff_mem (K := K)]`. Express the relevant statement in the definitionally equal form `w.valuation K (algebraMap (𝓞 K) K n) < 1`. Rewrite using `[← h, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hn'` using `(hw n).1 hn`. Establish `h2 : ((d : 𝓞 K) : K) = x * (n : K)`. Establish `h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K)` using `h`. Rewrite using `[← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]`. Rewrite `hd` using `[h2, map_mul, norm_mul]`.

Use polynomial arithmetic with `[norm_nonneg (ι x), norm_nonneg (ι (n : K))]`.
-/
theorem valuation_le_one_of_norm (ι : K →+* ℂ_[p]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1) (x : K) (hx : ‖ι x‖ ≤ 1) :
    w.valuation K x ≤ 1 := by
  by_contra hcon
  have hgt : 1 < w.valuation K x := not_le.1 hcon
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hgt
  have hinv : w.valuation K x⁻¹ < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ hgt
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x⁻¹ hinv.le
  have hd : 1 ≤ ‖ι ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have hn : n ∈ w.asIdeal := by
    rw [← w.valuation_lt_one_iff_mem (K := K)]
    change w.valuation K (algebraMap (𝓞 K) K n) < 1
    rw [← h, map_mul]
    calc w.valuation K x⁻¹ * w.valuation K (algebraMap (𝓞 K) K d) ≤ w.valuation K x⁻¹ * 1 :=
          mul_le_mul_right (w.valuation_le_one _) _
      _ < 1 := by rwa [mul_one]
  have hn' := (hw n).1 hn
  have h2 : ((d : 𝓞 K) : K) = x * (n : K) := by
    have h' : x⁻¹ * ((d : 𝓞 K) : K) = (n : K) := h
    rw [← h', ← mul_assoc, mul_inv_cancel₀ hx0, one_mul]
  rw [h2, map_mul, norm_mul] at hd
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι (n : K))]

/- English proof (translation)
Introduce `K _ _ σ p _ w hw`. Take `⟨ι, hι⟩` from `exists_embedding w hw`. Establish `hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1` using `fun y => by rw [hι]; rfl`. Take `⟨lam, hlam⟩` from `GlobalTheory.MomPlace.exists_extension K p σ ι`. Use `⟨lam, fun k => ?_⟩` and prove the remaining obligations.

Unfold `GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt`. Rewrite using `[(hlam k).2]`. Conclude with `⟨fun h => valuation_le_one_of_norm ι w hw' k h.2, fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩`.
-/
theorem placeAbove : GlobalTheory.DatumJets.PlaceAbove := by
  intro K _ _ σ p _ w hw
  obtain ⟨ι, hι⟩ := exists_embedding w hw
  have hw' : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖ι (y : K)‖ < 1 := fun y => by rw [hι]; rfl
  obtain ⟨lam, hlam⟩ := GlobalTheory.MomPlace.exists_extension K p σ ι
  refine ⟨lam, fun k => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.IntegralityWeylConditions.IntAt
  rw [(hlam k).2]
  exact ⟨fun h => valuation_le_one_of_norm ι w hw' k h.2,
    fun h => ⟨(hlam k).1, GlobalTheory.MomPlace.norm_le_one_of_valuation K p ι w hw' k h⟩⟩

end GlobalTheory.DatumJets.Place
