import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PVocabDivCycle
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.VerticalDivisorGeometricNumberStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)

namespace GlobalTheory.CompanionTheory.Ar.Num.RecSplit

section SlopeTestRemainingChoices

variable {K : Type} {ι : K → Type}

/- English proof (translation)
Unfold `intNumL intNum mixedDiff`. Rewrite using `[List.ofFn_get]`.
-/
theorem intNumL_ofFn [DecidableEq K] (F : Type) [Field F] (Q : Ideal (MRing ι F)) {n : ℕ}
    (b : Fin n → K → ℤ) : intNumL F Q (List.ofFn b) = intNum F Q b := by
  unfold intNumL intNum mixedDiff
  rw [List.ofFn_get]

/- English proof (translation)
Use `set J : Ideal ℤ := W.comap (C : ℤ →+* MRing ι ℤ) with hJ`. Establish `hJp : J.IsPrime` using `Ideal.comap_isPrime _ _`. Establish `hJ0 : J ≠ ⊥` using `h`. Take `⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g}` from `⟨_, (Ideal.span_singleton_generator J).symm⟩`. Establish `hg0 : g ≠ 0`.

Introduce and unpack `rfl`. Conclude with `hJ0 (by simpa using hg)`. Establish `hgp : Prime g` using `(Ideal.span_singleton_prime hg0).1 (hg ▸ hJp)`. Use `⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.1 hgp⟩, ?_⟩` and prove the remaining obligations. Establish `: ((g.natAbs : ℕ) : ℤ) ∈ J`.

Rewrite using `[hg]`. Conclude with `Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)`. Conclude with `this`.
-/
theorem exists_prime_mem (W : Ideal (MRing ι ℤ)) (hW : W.IsPrime) (h : ¬ IsHorizontal W) :
    ∃ p : Nat.Primes, (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W := by
  set J : Ideal ℤ := W.comap (C : ℤ →+* MRing ι ℤ) with hJ
  have hJp : J.IsPrime := Ideal.comap_isPrime _ _
  have hJ0 : J ≠ ⊥ := h
  obtain ⟨g, hg⟩ : ∃ g : ℤ, J = Ideal.span {g} := ⟨_, (Ideal.span_singleton_generator J).symm⟩
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hJ0 (by simpa using hg)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).1 (hg ▸ hJp)
  refine ⟨⟨g.natAbs, Int.prime_iff_natAbs_prime.1 hgp⟩, ?_⟩
  have : ((g.natAbs : ℕ) : ℤ) ∈ J := by
    rw [hg]
    exact Ideal.mem_span_singleton.2 (Int.dvd_natAbs.2 dvd_rfl)
  exact this

variable [Fintype K] [∀ k, Fintype (ι k)]

/- English proof (translation)
Unfold `divCycle`. Conclude with `dif_neg h`.
-/
theorem divCycle_eq_zero_of_not_mem (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) : divCycle P s W = 0 := by
  unfold divCycle
  exact dif_neg h

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Conclude with `h (divCycle_eq_zero_of_not_mem P s W hc)`.
-/
theorem mem_of_divCycle_ne (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : divCycle P s W ≠ 0) : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := by
  by_contra hc
  exact h (divCycle_eq_zero_of_not_mem P s W hc)

/- English proof (translation)
The claim follows from `(ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).subset fun W hW => mem_of_divCycle_ne P s W hW`.
-/
theorem divCycle_support_finite (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) :
    (Function.support (divCycle P s)).Finite :=
  (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).subset fun W hW => mem_of_divCycle_ne P s W hW

/- English proof (translation)
Rewrite using `[← VocabDivCycle.proof ℤ K ι P s W]`. Use `congr 1`. Use `show _ = (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0)`. Rewrite using `[if_pos h]`.
-/
theorem multAt_eq (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (W : Ideal (MRing ι ℤ))
    (h : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s) :
    ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℤ) = divCycle P s W := by
  rw [← VocabDivCycle.proof ℤ K ι P s W]
  congr 1
  classical
  show _ = (if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0)
  rw [if_pos h]

end SlopeTestRemainingChoices

section Main

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

open Classical in

noncomputable def vertTerm (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ)) : ℤ :=
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  if (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W then intNumL (ZMod p) (extTo (ZMod p) W) l else 0

/- English proof (translation)
Unfold `vertTerm`. Conclude with `if_neg h`.
-/
theorem vertTerm_of_not_mem (p : Nat.Primes) (W : Ideal (MRing ι ℤ)) (l : List (K → ℤ))
    (h : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∉ W) : vertTerm p W l = 0 := by
  unfold vertTerm
  exact if_neg h

/- English proof (translation)
Unfold `vertAt cycEval`. Conclude with `finsum_eq_sum_of_support_subset _ fun W hW => hT (left_ne_zero_of_mul hW)`.
-/
theorem vertAt_eq_sum (p : Nat.Primes) (P : Ideal (MRing ι ℤ)) (s : MRing ι ℤ) (l : List (K → ℤ))
    (T : Finset (Ideal (MRing ι ℤ))) (hT : Function.support (divCycle P s) ⊆ T) :
    vertAt p P s l = ∑ W ∈ T, divCycle P s W * vertTerm p W l := by
  unfold vertAt cycEval
  exact finsum_eq_sum_of_support_subset _ fun W hW => hT (left_ne_zero_of_mul hW)

/- English proof (translation)
Use `haveI : Fact (p : ℕ).Prime := ⟨p.2⟩`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.vertical_divisor_geometric_number K ι P D hP a s hs hsP W hW (p : ℕ) hp`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[h3 b]`. Unfold `vertTerm`.

Rewrite using `[if_pos hp, intNumL_ofFn]`.
-/
theorem key_of_mem {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    {W : Ideal (MRing ι ℤ)} (hW : divCycle P s W ≠ 0) (p : Nat.Primes)
    (hp : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W) :
    charOf W = p ∧ ¬ IsHorizontal W ∧ geoNum D W b = vertTerm p W (List.ofFn b) := by
  haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.vertical_divisor_geometric_number K ι P D hP a s hs hsP W hW (p : ℕ) hp
  refine ⟨h1, h2, ?_⟩
  rw [h3 b]
  unfold vertTerm
  rw [if_pos hp, intNumL_ofFn]

/- English proof (translation)
Distinguish the cases in `hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W`. Conclude with `(key_of_mem hP hs hsP b hW p hm).1`. Conclude with `absurd (vertTerm_of_not_mem p W _ hm) hp`.
-/
theorem support_term_subset {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) {p : Nat.Primes} (hW : divCycle P s W ≠ 0)
    (hp : vertTerm p W (List.ofFn b) ≠ 0) : charOf W = p := by
  by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
  · exact (key_of_mem hP hs hsP b hW p hm).1
  · exact absurd (vertTerm_of_not_mem p W _ hm) hp

open Classical in

/- English proof (translation)
Distinguish the cases in `hW : divCycle P s W = 0`. Simplify using `[hW]`. Distinguish the cases in `hh : IsHorizontal W`. Rewrite using `[if_pos hh, mul_zero]`. Use `finsum_eq_zero_of_forall_eq_zero fun p => ?_` and prove the remaining obligations.

Establish `: vertTerm p W (List.ofFn b) = 0`. Assume the negation of the conclusion as `hne`. Distinguish the cases in `hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W`. Conclude with `(key_of_mem hP hs hsP b hW p hm).2.1 hh`. Conclude with `hne (vertTerm_of_not_mem p W _ hm)`.

Simplify using `[this]`. Rewrite using `[if_neg hh]`. Establish `hWp : W.IsPrime` using `(mem_of_divCycle_ne P s W hW).1.1.1`. Take `⟨q, hq⟩` from `exists_prime_mem W hWp hh`. Take `⟨hc, -, hg⟩` from `key_of_mem hP hs hsP b hW q hq`.

Rewrite using `[finsum_eq_single _ q]`. Rewrite using `[hc, hg]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `p hpq`.

Establish `: vertTerm p W (List.ofFn b) = 0`. Assume the negation of the conclusion as `hne`. Establish `h2` using `support_term_subset hP hs hsP b W hW hne`. Conclude with `hpq (Nat.Primes.coe_nat_injective (h2.symm.trans hc))`. Simplify using `[this]`.
-/
theorem finsum_term {P : Ideal (MRing ι ℤ)} {D : ℕ} (hP : IsArithVar P (D + 1)) {a : K → ℕ}
    {s : MRing ι ℤ} (hs : IsMultiHomog s a) (hsP : s ∉ P) (b : Fin D → K → ℤ)
    (W : Ideal (MRing ι ℤ)) :
    ∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) =
      (divCycle P s W : ℝ) *
        (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
  by_cases hW : divCycle P s W = 0
  · simp [hW]
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, mul_zero]
    refine finsum_eq_zero_of_forall_eq_zero fun p => ?_
    have : vertTerm p W (List.ofFn b) = 0 := by
      by_contra hne
      by_cases hm : (C ((p : ℕ) : ℤ) : MRing ι ℤ) ∈ W
      · exact (key_of_mem hP hs hsP b hW p hm).2.1 hh
      · exact hne (vertTerm_of_not_mem p W _ hm)
    simp [this]
  · rw [if_neg hh]
    have hWp : W.IsPrime := (mem_of_divCycle_ne P s W hW).1.1.1
    obtain ⟨q, hq⟩ := exists_prime_mem W hWp hh
    obtain ⟨hc, -, hg⟩ := key_of_mem hP hs hsP b hW q hq
    rw [finsum_eq_single _ q]
    · rw [hc, hg]
      push_cast
      ring
    · intro p hpq
      have : vertTerm p W (List.ofFn b) = 0 := by
        by_contra hne
        have h2 := support_term_subset hP hs hsP b W hW hne
        exact hpq (Nat.Primes.coe_nat_injective (h2.symm.trans hc))
      simp [this]

/- English proof (translation)
Introduce `K _ _ ι _ P D hP I a s hs hsP L A`. Use `set b : Fin D → K → ℤ := fun j => (L j).a with hb`. Use `set T : Finset (Ideal (MRing ι ℤ)) := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).toFinset with hT`. Establish `hTm : ∀ W, W ∈ T ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s` using `fun W => by simp [hT]`. Establish `hsub : Function.support (divCycle P s) ⊆ T` using `fun W hW => (hTm W).2 (mem_of_divCycle_ne P s W hW)`.

Prove the components needed by the constructor for the conclusion. Establish `hfin : ((fun W : Ideal (MRing ι ℤ) => charOf W) '' (T : Set _)).Finite` using `T.finite_toSet.image _`. Use `(hfin.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_` and prove the remaining obligations. Establish `hp' : vertAt p P s (List.ofFn b) ≠ 0` using `hp`. Rewrite `hp'` using `[vertAt_eq_sum p P s _ T hsub]`.

Take `⟨W, hWT, hW⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hp'`. Conclude with `⟨W, hWT, support_term_subset hP hs hsP b W (left_ne_zero_of_mul hW) (right_ne_zero_of_mul hW)⟩`. Establish `h1 : (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s, ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) * (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) = ∑ W ∈ T, (divCycle P s W : ℝ) * (if IsHorizont …`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]`. Use `Finset.sum_congr rfl fun W hW => ?_` and prove the remaining obligations.

Rewrite using `[← multAt_eq P s W ((hTm W).1 hW)]`. Use `norm_cast`. Establish `h2 : (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) = ∑ W ∈ T, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W`. Use `finsum_eq_sum_of_support_subset _ fun W hW => hsub ?_` and prove the remaining obligations. Use `left_ne_zero_of_mul hW` as an intermediate fact.

Conclude with `fun h0 => this (by simp [h0])`. Establish `h3 : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ)) = ∑ W ∈ T, (divCycle P s W : ℝ) * (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W))`. Establish `e : ∀ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ) = ∑ W ∈ T, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ)`. Introduce `p`. Rewrite using `[vertAt_eq_sum p P s _ T hsub, Int.cast_sum, Finset.mul_sum]`.

Repeatedly rewrite using `[e]`. Rewrite using `[finsum_sum_comm]`. Conclude with `Finset.sum_congr rfl fun W _ => finsum_term hP hs hsP b W`. Introduce `W _`. Use `((Set.finite_singleton (charOf W)).preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_` and prove the remaining obligations.

Establish `hne` using `right_ne_zero_of_mul (show _ ≠ (0 : ℝ) from hp)`. Establish `hne' : divCycle P s W * vertTerm p W (List.ofFn b) ≠ 0` using `by exact_mod_cast hne`. Conclude with `(support_term_subset hP hs hsP b W (left_ne_zero_of_mul hne') (right_ne_zero_of_mul hne')).symm`. Establish `h0 : recR I P L A s = (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s, ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) * (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) - arInt P s A L` using `rfl`. Rewrite using `[h0, h1, h2, h3, ← Finset.sum_add_distrib]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Distinguish the cases in `hh : IsHorizontal W`. Simplify using `[hh, Set.indicator]`. Simplify using `[hh, Set.indicator]`.
-/
theorem recR_split : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι ℤ)) (D : ℕ), IsArithVar P (D + 1) → ∀ (I : Ideal (MRing ι ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (a : K → ℕ) (s : MRing ι ℤ), IsMultiHomog s a → s ∉ P → ∀ (L : Fin D → HermLine ι) (A : HermLine ι), (Function.support fun p : Nat.Primes => vertAt p P s (List.ofFn fun j => (L j).a)).Finite ∧ recR I P L A s = (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) + (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn fun j => (L j).a) : ℝ)) - arInt P s A L := by
  intro K _ _ ι _ P D hP I a s hs hsP L A
  classical
  set b : Fin D → K → ℤ := fun j => (L j).a with hb
  set T : Finset (Ideal (MRing ι ℤ)) := (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s).toFinset with hT
  have hTm : ∀ W, W ∈ T ↔ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := fun W => by simp [hT]
  have hsub : Function.support (divCycle P s) ⊆ T := fun W hW =>
    (hTm W).2 (mem_of_divCycle_ne P s W hW)
  constructor
  · have hfin : ((fun W : Ideal (MRing ι ℤ) => charOf W) '' (T : Set _)).Finite :=
      T.finite_toSet.image _
    refine (hfin.preimage (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
    have hp' : vertAt p P s (List.ofFn b) ≠ 0 := hp
    rw [vertAt_eq_sum p P s _ T hsub] at hp'
    obtain ⟨W, hWT, hW⟩ := Finset.exists_ne_zero_of_sum_ne_zero hp'
    exact ⟨W, hWT, support_term_subset hP hs hsP b W (left_ne_zero_of_mul hW)
      (right_ne_zero_of_mul hW)⟩
  · have h1 : (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (ReciprocityTheory.ChartRestriction.G.Geo.divSupp_finite P s)]
      refine Finset.sum_congr rfl fun W hW => ?_
      rw [← multAt_eq P s W ((hTm W).1 hW)]
      norm_cast
    have h2 : (∑ᶠ W, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W) =
        ∑ W ∈ T, (divCycle P s W : ℝ) * Set.indicator {W | IsHorizontal W} (fun W => I W D L) W := by
      refine finsum_eq_sum_of_support_subset _ fun W hW => hsub ?_
      have := left_ne_zero_of_mul hW
      exact fun h0 => this (by simp [h0])
    have h3 : (∑ᶠ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ)) =
        ∑ W ∈ T, (divCycle P s W : ℝ) *
          (if IsHorizontal W then 0 else (geoNum D W b : ℝ) * Real.log (charOf W)) := by
      have e : ∀ p : Nat.Primes, Real.log (p : ℕ) * (vertAt p P s (List.ofFn b) : ℝ) =
          ∑ W ∈ T, Real.log (p : ℕ) * ((divCycle P s W * vertTerm p W (List.ofFn b) : ℤ) : ℝ) := by
        intro p
        rw [vertAt_eq_sum p P s _ T hsub, Int.cast_sum, Finset.mul_sum]
      simp_rw [e]
      rw [finsum_sum_comm]
      · exact Finset.sum_congr rfl fun W _ => finsum_term hP hs hsP b W
      · intro W _
        refine ((Set.finite_singleton (charOf W)).preimage
          (Nat.Primes.coe_nat_injective.injOn)).subset fun p hp => ?_
        have hne := right_ne_zero_of_mul (show _ ≠ (0 : ℝ) from hp)
        have hne' : divCycle P s W * vertTerm p W (List.ofFn b) ≠ 0 := by exact_mod_cast hne
        exact (support_term_subset hP hs hsP b W (left_ne_zero_of_mul hne')
          (right_ne_zero_of_mul hne')).symm
    have h0 : recR I P L A s = (∑ᶠ W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s,
          ((ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W : ℕ) : ℝ) *
            (if IsHorizontal W then I W D L else (geoNum D W b : ℝ) * Real.log (charOf W))) -
        arInt P s A L := rfl
    rw [h0, h1, h2, h3, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hh : IsHorizontal W
    · simp [hh, Set.indicator]
    · simp [hh, Set.indicator]

end Main

end GlobalTheory.CompanionTheory.Ar.Num.RecSplit
