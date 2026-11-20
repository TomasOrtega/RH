import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonSlope

/- English proof (translation)
Use `revert hT hc`. Use `Finset.induction_on T ?_ ?_` and prove the remaining obligations. Introduce `hT`. Conclude with `absurd hT Finset.not_nonempty_empty`. Introduce `a s ha ih hT hc`.

Break down `s.eq_empty_or_nonempty with hs | hs` into its components or cases. Substitute `hs` using the available equality. Use `⟨a, Finset.mem_insert_self a ∅, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Rewrite `hj` using `[Finset.mem_insert]`.

Break down `hj with rfl | hj` into its components or cases. Conclude with `dvd_refl _`. Conclude with `absurd hj (Finset.notMem_empty j)`. Take `⟨i₀, hi₀, hmax⟩` from `ih hs (fun i hi j hj => hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))`. Break down `hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h` into its components or cases.

Use `⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Conclude with `h`. Conclude with `hmax j hj`.

Use `⟨a, Finset.mem_insert_self a s, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Break down `Finset.mem_insert.mp hj with rfl | hj` into its components or cases. Conclude with `dvd_refl _`. Conclude with `(hmax j hj).trans h`.
-/
theorem exists_dvd_all {S ι : Type} [CommRing S] (T : Finset ι) (hT : T.Nonempty) (r : ι → S)
    (hc : ∀ i ∈ T, ∀ j ∈ T, r i ∣ r j ∨ r j ∣ r i) :
    ∃ i₀ ∈ T, ∀ j ∈ T, r j ∣ r i₀ := by
  classical
  revert hT hc
  refine Finset.induction_on T ?_ ?_
  · intro hT
    exact absurd hT Finset.not_nonempty_empty
  · intro a s ha ih hT hc
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_refl _
      · exact absurd hj (Finset.notMem_empty j)
    · obtain ⟨i₀, hi₀, hmax⟩ := ih hs (fun i hi j hj =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      rcases hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h
      · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact (hmax j hj).trans h

/- English proof (translation)
Take `⟨k, hk⟩` from `h`. Use `hD a b ⟨M, ?_⟩` and prove the remaining obligations. Rewrite using `[hk]`. Conclude with `Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))`.
-/
theorem dich_of_dvd {S : Type} [CommRing S] {ϖ : S} (hD : Dich ϖ) {a b : S} {M : ℕ}
    (h : a ∣ ϖ ^ M) : b ∣ a ∨ a ∣ b := by
  obtain ⟨k, hk⟩ := h
  refine hD a b ⟨M, ?_⟩
  rw [hk]
  exact Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))

/- English proof (translation)
Introduce `S _ ϖ hD hR q d M hd hqd h0`. Establish `hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j))`. Introduce `j`. Distinguish the cases in `hj : 1 ≤ j ∧ q j ∣ q 0`. Take `⟨t, ht⟩` from `hj.2`.

Establish `htd : t ∣ ϖ ^ M` using `(Dvd.intro_left (q j) ht.symm).trans h0`. Take `⟨r, u, hru⟩` from `hR t M j htd (by omega)`. Conclude with `⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩`. Conclude with `⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩`. Use `choose s hs using hex`.

Use `set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef`. Establish `hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0`. Introduce `j`. Rewrite using `[hTdef, Finset.mem_filter, Finset.mem_Icc]`. Establish `hdT : d ∈ T` using `(hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩`.

Establish `hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M`. Introduce `j hj`. Take `⟨⟨hj1, _⟩, hjq⟩` from `(hmemT j).mp hj`. Take `⟨u, hu⟩` from `hs j hj1 hjq`. Establish `h1 : s j ^ j ∣ q 0` using `⟨q j * ↑u, by rw [hu]; ring⟩`.

Conclude with `((dvd_pow_self (s j) (by omega)).trans h1).trans h0`. Establish `hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i`. Introduce `i hi j _`. Conclude with `(dich_of_dvd hD (b := s j) (hsdvd i hi)).symm`. Take `⟨i₀, hi₀T, hmax⟩` from `exists_dvd_all T ⟨d, hdT⟩ s hcomp`.

Take `⟨⟨hi₀1, hi₀d⟩, hi₀q⟩` from `(hmemT i₀).mp hi₀T`. Use `⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩` and prove the remaining obligations. Introduce `i hi1 hid`. Break down `dich_of_dvd hD (b := q i) h0 with h | h` into its components or cases. Establish `hiT : i ∈ T` using `(hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩`.

Take `⟨u, hu⟩` from `hs i hi1 h`. Establish `h2 : q 0 ∣ q i * s i ^ i`. Rewrite using `[hu, mul_left_comm, Units.mul_left_dvd]`. Take `⟨k, hk⟩` from `hmax i hiT`. Conclude with `h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩`.

Conclude with `dvd_mul_of_dvd_left h _`. Take `⟨u, hu⟩` from `hs i₀ hi₀1 hi₀q`. Conclude with `⟨↑u, by rw [hu]; ring⟩`.
-/
theorem first_slope : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ),
    0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧
      ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  intro S _ ϖ hD hR q d M hd hqd h0
  classical
  have hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ q j ∣ q 0
    · obtain ⟨t, ht⟩ := hj.2
      have htd : t ∣ ϖ ^ M := (Dvd.intro_left (q j) ht.symm).trans h0
      obtain ⟨r, u, hru⟩ := hR t M j htd (by omega)
      exact ⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose s hs using hex
  set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef
  have hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0 := by
    intro j
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc]
  have hdT : d ∈ T := (hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩
  have hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M := by
    intro j hj
    obtain ⟨⟨hj1, _⟩, hjq⟩ := (hmemT j).mp hj
    obtain ⟨u, hu⟩ := hs j hj1 hjq
    have h1 : s j ^ j ∣ q 0 := ⟨q j * ↑u, by rw [hu]; ring⟩
    exact ((dvd_pow_self (s j) (by omega)).trans h1).trans h0
  have hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i := by
    intro i hi j _
    exact (dich_of_dvd hD (b := s j) (hsdvd i hi)).symm
  obtain ⟨i₀, hi₀T, hmax⟩ := exists_dvd_all T ⟨d, hdT⟩ s hcomp
  obtain ⟨⟨hi₀1, hi₀d⟩, hi₀q⟩ := (hmemT i₀).mp hi₀T
  refine ⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩
  · intro i hi1 hid
    rcases dich_of_dvd hD (b := q i) h0 with h | h
    · have hiT : i ∈ T := (hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩
      obtain ⟨u, hu⟩ := hs i hi1 h
      have h2 : q 0 ∣ q i * s i ^ i := by
        rw [hu, mul_left_comm, Units.mul_left_dvd]
      obtain ⟨k, hk⟩ := hmax i hiT
      exact h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩
    · exact dvd_mul_of_dvd_left h _
  · obtain ⟨u, hu⟩ := hs i₀ hi₀1 hi₀q
    exact ⟨↑u, by rw [hu]; ring⟩

end GlobalTheory.CompanionTheory.NewtonSlope
