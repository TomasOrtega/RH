import Development.AbelianVarietyTheory.Definitions.Divisors.CentreAtOfIsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.RegDom
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PointSep

open IsLocalRing

/- English proof (translation)
Introduce `R _ _ a b ha hb h`. Establish `hdom : IsDomain R` using `ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing`. Establish `hp` using `LinearIndependent.pair_iff.mp h`. Establish `hsmul : ∀ (r : R) (x : maximalIdeal R), (maximalIdeal R).toCotangent (r • x) = (residue R r) • (maximalIdeal R).toCotangent x`. Introduce `r x`.

Rewrite using `[map_smul]`. Both sides reduce to the same expression. Establish `ha2 : a ∉ maximalIdeal R ^ 2`. Introduce `h2`. Establish `h0 : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0`.

Rewrite using `[Ideal.toCotangent_eq_zero]`. Conclude with `h2`. Use `hp 1 0 (by simp [h0])` as an intermediate fact. Conclude with `one_ne_zero this.1`. Establish `hpa : Prime a` using `ReciprocityTheory.AnForm.R.prime_of_not_mem_sq ha ha2`.

Establish `ha0 : a ≠ 0` using `hpa.ne_zero`. Establish `hba : b ∉ Ideal.span {a}`. Introduce `hb'`. Take `⟨r, hr⟩` from `Ideal.mem_span_singleton'.mp hb'`. Establish `heq : (⟨b, hb⟩ : maximalIdeal R) = r • ⟨a, ha⟩` using `by ext; simp [hr]`.

Use `hp (-(residue R r)) 1 (by rw [heq, hsmul]; simp)` as an intermediate fact. Conclude with `one_ne_zero this.2`. Establish `hfin` using `(IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance`. Establish `hle` using `h.fintype_card_le_finrank`. Simplify using `only [Fintype.card_fin] at hle`.

Use `set n := Module.finrank (ResidueField R) (CotangentSpace R) with hn`. Establish `hdim : ringKrullDim R = (((n - 2) + 2 : ℕ) : WithBot ℕ∞)`. Rewrite using `[← hfin, Nat.sub_add_cancel hle]`. Establish `hind : ∀ c : Fin 2 → R, ∑ i, c i * (![a, b] : Fin 2 → R) i ∈ maximalIdeal R ^ 2 → ∀ i, c i ∈ maximalIdeal R`. Introduce `c hc`.

Establish `hc' : (maximalIdeal R).toCotangent (c 0 • ⟨a, ha⟩ + c 1 • ⟨b, hb⟩) = 0`. Rewrite using `[Ideal.toCotangent_eq_zero]`. Simplify `hc` using `[Fin.sum_univ_two]`. Rewrite `hc'` using `[map_add, hsmul, hsmul]`. Take `⟨h0, h1⟩` from `hp _ _ hc'`.

Introduce `i`. Use `fin_cases i`. Conclude with `(residue_eq_zero_iff _).mp h0`. Conclude with `(residue_eq_zero_iff _).mp h1`. Establish `hmem : ∀ i, (![a, b] : Fin 2 → R) i ∈ maximalIdeal R`.

Introduce `i`. Use `fin_cases i`. Conclude with `ha`. Conclude with `hb`. Take `⟨hreg, -⟩` from `GlobalTheory.RegularQuotient.quotient_span_range R (n - 2) 2 ![a, b] hdim hmem hind`.

Establish `hrange : Set.range (![a, b] : Fin 2 → R) = {a, b}`. Rewrite using `[Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]`. Rewrite `hreg` using `[hrange]`. Establish `hqdom : IsDomain (R ⧸ Ideal.span {a, b})` using `ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing`. Establish `hP : (Ideal.span {a, b}).IsPrime` using `(Ideal.Quotient.isDomain_iff_prime _).mp hqdom`.

Use `⟨hP, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Establish `hmin : Ideal.span {a, b} ∈ (Ideal.span ((({a, b} : Finset R)) : Set R)).minimalPrimes`. Rewrite using `[Finset.coe_insert, Finset.coe_singleton, Ideal.minimalPrimes_eq_subsingleton_self]`. Both sides reduce to the same expression. Use `(Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_` and prove the remaining obligations.

Conclude with `Finset.card_le_two` after adjusting the coercions. Establish `hPa : (Ideal.span {a}).IsPrime` using `(Ideal.span_singleton_prime ha0).mpr hpa`. Establish `h1 : (⊥ : Ideal R) < Ideal.span {a}`. Rewrite using `[bot_lt_iff_ne_bot]`. Simplify using `using ha0`.

Establish `h2 : Ideal.span {a} < Ideal.span {a, b}`. Use `lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_` and prove the remaining obligations. Introduce `he`. Conclude with `hba (he ▸ Ideal.subset_span (by simp))`. Establish `hlt1` using `Ideal.height_strict_mono_of_isPrime h1`.

Establish `hlt2` using `Ideal.height_strict_mono_of_isPrime h2`. Establish `hne : (Ideal.span {a}).height ≠ ⊤` using `Ideal.height_ne_top_of_isPrime`. Establish `e1 : (⊥ : Ideal R).height + 1 ≤ (Ideal.span {a}).height` using `Order.add_one_le_of_lt hlt1`. Establish `e2 : (Ideal.span {a}).height + 1 ≤ (Ideal.span {a, b}).height` using `Order.add_one_le_of_lt hlt2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem span_pair_isPrime_and_height_eq_two : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] (a b : R) (ha : a ∈ IsLocalRing.maximalIdeal R) (hb : b ∈ IsLocalRing.maximalIdeal R), LinearIndependent (IsLocalRing.ResidueField R) (![(IsLocalRing.maximalIdeal R).toCotangent ⟨a, ha⟩, (IsLocalRing.maximalIdeal R).toCotangent ⟨b, hb⟩] : Fin 2 → IsLocalRing.CotangentSpace R) → (Ideal.span {a, b}).IsPrime ∧ (Ideal.span {a, b}).height = 2 := by
  intro R _ _ a b ha hb h
  classical
  have hdom : IsDomain R := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hp := LinearIndependent.pair_iff.mp h
  have hsmul : ∀ (r : R) (x : maximalIdeal R),
      (maximalIdeal R).toCotangent (r • x) = (residue R r) • (maximalIdeal R).toCotangent x := by
    intro r x
    rw [map_smul]; rfl

  have ha2 : a ∉ maximalIdeal R ^ 2 := by
    intro h2
    have h0 : (maximalIdeal R).toCotangent ⟨a, ha⟩ = 0 := by
      rw [Ideal.toCotangent_eq_zero]; exact h2
    have := hp 1 0 (by simp [h0])
    exact one_ne_zero this.1
  have hpa : Prime a := ReciprocityTheory.AnForm.R.prime_of_not_mem_sq ha ha2
  have ha0 : a ≠ 0 := hpa.ne_zero

  have hba : b ∉ Ideal.span {a} := by
    intro hb'
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hb'
    have heq : (⟨b, hb⟩ : maximalIdeal R) = r • ⟨a, ha⟩ := by
      ext; simp [hr]
    have := hp (-(residue R r)) 1 (by rw [heq, hsmul]; simp)
    exact one_ne_zero this.2

  have hfin := (IsRegularLocalRing.iff_finrank_cotangentSpace R).mp inferInstance
  have hle := h.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  set n := Module.finrank (ResidueField R) (CotangentSpace R) with hn
  have hdim : ringKrullDim R = (((n - 2) + 2 : ℕ) : WithBot ℕ∞) := by
    rw [← hfin, Nat.sub_add_cancel hle]
  have hind : ∀ c : Fin 2 → R, ∑ i, c i * (![a, b] : Fin 2 → R) i ∈ maximalIdeal R ^ 2 →
      ∀ i, c i ∈ maximalIdeal R := by
    intro c hc
    have hc' : (maximalIdeal R).toCotangent (c 0 • ⟨a, ha⟩ + c 1 • ⟨b, hb⟩) = 0 := by
      rw [Ideal.toCotangent_eq_zero]
      simpa [Fin.sum_univ_two] using hc
    rw [map_add, hsmul, hsmul] at hc'
    obtain ⟨h0, h1⟩ := hp _ _ hc'
    intro i
    fin_cases i
    · exact (residue_eq_zero_iff _).mp h0
    · exact (residue_eq_zero_iff _).mp h1
  have hmem : ∀ i, (![a, b] : Fin 2 → R) i ∈ maximalIdeal R := by
    intro i; fin_cases i
    · exact ha
    · exact hb
  obtain ⟨hreg, -⟩ := GlobalTheory.RegularQuotient.quotient_span_range R (n - 2) 2 ![a, b] hdim hmem hind
  have hrange : Set.range (![a, b] : Fin 2 → R) = {a, b} := by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  rw [hrange] at hreg
  have hqdom : IsDomain (R ⧸ Ideal.span {a, b}) := ReciprocityTheory.AnForm.R.isDomain_of_isRegularLocalRing
  have hP : (Ideal.span {a, b}).IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hqdom
  refine ⟨hP, le_antisymm ?_ ?_⟩
  · have hmin : Ideal.span {a, b} ∈ (Ideal.span ((({a, b} : Finset R)) : Set R)).minimalPrimes := by
      rw [Finset.coe_insert, Finset.coe_singleton, Ideal.minimalPrimes_eq_subsingleton_self]
      rfl
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans ?_
    exact_mod_cast Finset.card_le_two
  · have hPa : (Ideal.span {a}).IsPrime := (Ideal.span_singleton_prime ha0).mpr hpa
    have h1 : (⊥ : Ideal R) < Ideal.span {a} := by
      rw [bot_lt_iff_ne_bot]; simpa using ha0
    have h2 : Ideal.span {a} < Ideal.span {a, b} := by
      refine lt_of_le_of_ne (Ideal.span_mono (by simp)) ?_
      intro he
      exact hba (he ▸ Ideal.subset_span (by simp))
    have hlt1 := Ideal.height_strict_mono_of_isPrime h1
    have hlt2 := Ideal.height_strict_mono_of_isPrime h2
    have hne : (Ideal.span {a}).height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
    have e1 : (⊥ : Ideal R).height + 1 ≤ (Ideal.span {a}).height := Order.add_one_le_of_lt hlt1
    have e2 : (Ideal.span {a}).height + 1 ≤ (Ideal.span {a, b}).height := Order.add_one_le_of_lt hlt2
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (⊥ : Ideal R).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Ideal.span {a}).height + 1 := by gcongr
      _ ≤ _ := e2

end GlobalTheory.PointSep
