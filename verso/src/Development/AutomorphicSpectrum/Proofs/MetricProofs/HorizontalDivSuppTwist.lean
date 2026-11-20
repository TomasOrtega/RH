import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

/- English proof (translation)
Use `sup_le (sup_le ?_ le_sup_right) ?_` and prove the remaining obligations. Conclude with `(Ideal.map_mono (le_sup_left.trans h)).trans le_sup_left`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))))`.
-/
theorem twist_sup_span_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} (h : P ⊔ Ideal.span {s} ≤ W) :
    twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ twist p W := by
  refine sup_le (sup_le ?_ le_sup_right) ?_
  · exact (Ideal.map_mono (le_sup_left.trans h)).trans le_sup_left
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (h (Ideal.mem_sup_right
      (Ideal.mem_span_singleton_self s))))

/- English proof (translation)
Use `sup_le ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.map_le_iff_le_comap.mp ((le_sup_left.trans le_sup_left).trans h)`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))`.
-/
theorem sup_span_le_comap_inc {K : Type} {ι : K → Type} (p : ℕ) {P : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) :
    P ⊔ Ideal.span {s} ≤ Q.comap inc := by
  refine sup_le ?_ ?_
  · exact Ideal.map_le_iff_le_comap.mp ((le_sup_left.trans le_sup_left).trans h)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))

/- English proof (translation)
The claim follows from `sup_le (Ideal.map_le_iff_le_comap.mpr hW) ((le_sup_right.trans le_sup_left).trans h)`.
-/
theorem twist_le_of_map_le {K : Type} {ι : K → Type} (p : ℕ) {P W : Ideal (MRing ι)}
    {s : MRing ι} {Q : Ideal (MRing (Tb ι))}
    (h : twist p P ⊔ Ideal.span {(inc s : MRing (Tb ι))} ≤ Q) (hW : W ≤ Q.comap inc) :
    twist p W ≤ Q :=
  sup_le (Ideal.map_le_iff_le_comap.mpr hW) ((le_sup_right.trans le_sup_left).trans h)

/- English proof (translation)
Use extensionality with `W'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hmin, hrel⟩, hhor⟩`. Establish `hprime : W'.IsPrime` using `hmin.1.1`. Establish `hle` using `hmin.1.2`.

Establish `hc : P ⊔ Ideal.span {s} ≤ W'.comap inc` using `sup_span_le_comap_inc p hle`. Establish `: (W'.comap inc).IsPrime` using `Ideal.comap_isPrime _ _`. Take `⟨W0, hW0, hW0le⟩` from `Ideal.exists_minimalPrimes_le hc`. Establish `hrel0 : IsRelevant W0`. Introduce `k`.

Take `⟨i, hi⟩` from `hrel (some k)`. Use `⟨i, fun h => hi ?_⟩` and prove the remaining obligations. Use `hW0le h` as an intermediate fact. Simplify `this` using `[inc, oldIdx]`. Establish `hhor0 : IsHorizontal W0`.

Rewrite `hhor`, the goal using `[IsHorizontal, eq_bot_iff]`. Introduce `n hn`. Use `hhor ?_` and prove the remaining obligations. Establish `h1 : (C n : MRing ι) ∈ W'.comap inc` using `hW0le hn`. Simplify `h1` using `[inc]`.

Establish `hmem : W0 ∈ divSupp P s` using `⟨hW0, hrel0⟩`. Use `⟨W0, ⟨hmem, hhor0⟩, ?_⟩` and prove the remaining obligations. Establish `htw : twist p W0 ≤ W'` using `twist_le_of_map_le p hle hW0le`. Conclude with `le_antisymm htw (hmin.2 ⟨hp W0 hmem hhor0, twist_sup_span_le p hW0.1.2⟩ htw)`. Introduce and unpack `⟨W, ⟨⟨hmin, hrel⟩, hhor⟩, rfl⟩`.

Establish `hprime : W.IsPrime` using `hmin.1.1`. Use `⟨⟨⟨⟨hp W ⟨hmin, hrel⟩ hhor, twist_sup_span_le p hmin.1.2⟩, ?_⟩, isRelevant_twist p hprime.ne_top hrel⟩, isHorizontal_twist p hhor⟩` and prove the remaining obligations. Introduce and unpack `Q ⟨hQ, hQle⟩ hQtw`. Establish `hcomap : Q.comap inc ≤ W`. Use `Ideal.comap_mono (f := inc) hQtw` as an intermediate fact.

Rewrite `this` using `[comap_inc_twist]`. Then use the resulting hypothesis. Use `hQ` as an intermediate fact. Establish `hW : W ≤ Q.comap inc` using `hmin.2 ⟨Ideal.comap_isPrime _ _, sup_span_le_comap_inc p hQle⟩ hcomap`. Conclude with `twist_le_of_map_le p hQle hW`.
-/
theorem horizontal_divSupp_twist (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (P : Ideal (MRing ι)) (s : MRing ι)
    (hp : ∀ W, W ∈ divSupp P s → IsHorizontal W → (twist p W).IsPrime) :
    {W' | W' ∈ divSupp (twist p P) (inc s) ∧ IsHorizontal W'} =
      twist p '' {W | W ∈ divSupp P s ∧ IsHorizontal W} := by
  ext W'
  constructor
  · rintro ⟨⟨hmin, hrel⟩, hhor⟩
    have hprime : W'.IsPrime := hmin.1.1
    have hle := hmin.1.2
    have hc : P ⊔ Ideal.span {s} ≤ W'.comap inc := sup_span_le_comap_inc p hle
    have : (W'.comap inc).IsPrime := Ideal.comap_isPrime _ _
    obtain ⟨W0, hW0, hW0le⟩ := Ideal.exists_minimalPrimes_le hc
    have hrel0 : IsRelevant W0 := by
      intro k
      obtain ⟨i, hi⟩ := hrel (some k)
      refine ⟨i, fun h => hi ?_⟩
      have := hW0le h
      simpa [inc, oldIdx] using this
    have hhor0 : IsHorizontal W0 := by
      rw [IsHorizontal, eq_bot_iff] at hhor ⊢
      intro n hn
      refine hhor ?_
      have h1 : (C n : MRing ι) ∈ W'.comap inc := hW0le hn
      simpa [inc] using h1
    have hmem : W0 ∈ divSupp P s := ⟨hW0, hrel0⟩
    refine ⟨W0, ⟨hmem, hhor0⟩, ?_⟩
    have htw : twist p W0 ≤ W' := twist_le_of_map_le p hle hW0le
    exact le_antisymm htw (hmin.2 ⟨hp W0 hmem hhor0, twist_sup_span_le p hW0.1.2⟩ htw)
  · rintro ⟨W, ⟨⟨hmin, hrel⟩, hhor⟩, rfl⟩
    have hprime : W.IsPrime := hmin.1.1
    refine ⟨⟨⟨⟨hp W ⟨hmin, hrel⟩ hhor, twist_sup_span_le p hmin.1.2⟩, ?_⟩,
      isRelevant_twist p hprime.ne_top hrel⟩, isHorizontal_twist p hhor⟩
    rintro Q ⟨hQ, hQle⟩ hQtw
    have hcomap : Q.comap inc ≤ W := by
      have := Ideal.comap_mono (f := inc) hQtw
      rwa [comap_inc_twist] at this
    have := hQ
    have hW : W ≤ Q.comap inc :=
      hmin.2 ⟨Ideal.comap_isPrime _ _, sup_span_le_comap_inc p hQle⟩ hcomap
    exact twist_le_of_map_le p hQle hW

end GlobalTheory.CompanionTheory.Ar.Tw
