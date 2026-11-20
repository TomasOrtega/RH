import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

namespace UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp at hs`. Consider the case `insert a s ha ih`. Distinguish the cases in `hs' : s.Nonempty`. Take `⟨k₁, hk₁, hmin⟩` from `ih hs' (fun k hk => hw k (Finset.mem_insert_of_mem hk))`.

Break down `hd a k₁ (hw a (Finset.mem_insert_self a s)) with h | h` into its components or cases. Use `⟨a, Finset.mem_insert_self a s, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Break down `Finset.mem_insert.mp hk with rfl | hk` into its components or cases. Conclude with `dvd_refl _`.

Conclude with `h.trans (hmin k hk)`. Use `⟨k₁, Finset.mem_insert_of_mem hk₁, ?_⟩` and prove the remaining obligations. Introduce `k hk`. Break down `Finset.mem_insert.mp hk with rfl | hk` into its components or cases. Conclude with `h`.

Conclude with `hmin k hk`. Rewrite `hs'` using `[Finset.not_nonempty_iff_eq_empty]`. Substitute `hs'` using the available equality. Use `⟨a, by simp, fun k hk => ?_⟩` and prove the remaining obligations. Simplify using `at hk`.

Substitute `hk` using the available equality. Conclude with `dvd_refl _`.
-/
private theorem exists_min_dvd {B ι : Type} [CommRing B] (w : B) (d : ι → B)
    (hd : ∀ k k', d k ∣ w → d k ∣ d k' ∨ d k' ∣ d k) (s : Finset ι) (hs : s.Nonempty)
    (hw : ∀ k ∈ s, d k ∣ w) : ∃ k₀ ∈ s, ∀ k ∈ s, d k₀ ∣ d k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | insert a s ha ih =>
    by_cases hs' : s.Nonempty
    · obtain ⟨k₁, hk₁, hmin⟩ := ih hs' (fun k hk => hw k (Finset.mem_insert_of_mem hk))
      rcases hd a k₁ (hw a (Finset.mem_insert_self a s)) with h | h
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact dvd_refl _
        · exact h.trans (hmin k hk)
      · refine ⟨k₁, Finset.mem_insert_of_mem hk₁, ?_⟩
        intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact h
        · exact hmin k hk
    · rw [Finset.not_nonempty_iff_eq_empty] at hs'
      subst hs'
      refine ⟨a, by simp, fun k hk => ?_⟩
      simp at hk
      subst hk
      exact dvd_refl _

/- English proof (translation)
Introduce `B ι _ _ w d hex hd`. Take `⟨k₀, hk₀, hmin⟩` from `exists_min_dvd w d hd (Finset.univ.filter fun k => d k ∣ w) (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by simpa using hk⟩) (fun k hk => (Finset.mem_filter.mp hk).2)`. Establish `hk₀w : d k₀ ∣ w` using `(Finset.mem_filter.mp hk₀).2`. Establish `hall : ∀ k, d k₀ ∣ d k`. Introduce `k`.

Break down `hd k₀ k hk₀w with h | h` into its components or cases. Conclude with `h`. Conclude with `hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hk₀w⟩)`. Use `⟨d k₀, fun k => if k = k₀ then 1 else (hall k).choose, k₀, hk₀w, by simp, ?_⟩` and prove the remaining obligations. Introduce `k`.

Distinguish the cases in `hk : k = k₀`. Substitute `hk` using the available equality. Simplify using the standard rewrite rules. Simplify using `only [hk, if_false]`. Conclude with `(hall k).choose_spec`.
-/
theorem linFactor_of : LinFactor := by
  intro B ι _ _ w d hex hd
  classical
  obtain ⟨k₀, hk₀, hmin⟩ := exists_min_dvd w d hd (Finset.univ.filter fun k => d k ∣ w)
    (by obtain ⟨k, hk⟩ := hex; exact ⟨k, by simpa using hk⟩)
    (fun k hk => (Finset.mem_filter.mp hk).2)
  have hk₀w : d k₀ ∣ w := (Finset.mem_filter.mp hk₀).2
  have hall : ∀ k, d k₀ ∣ d k := by
    intro k
    rcases hd k₀ k hk₀w with h | h
    · exact h
    · exact hmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.trans hk₀w⟩)
  refine ⟨d k₀, fun k => if k = k₀ then 1 else (hall k).choose, k₀, hk₀w, by simp, ?_⟩
  intro k
  by_cases hk : k = k₀
  · subst hk
    simp
  · simp only [hk, if_false]
    exact (hall k).choose_spec

end UpperTheory.Gal.crystallineComparison
