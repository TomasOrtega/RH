import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `ι _ s hs`. Use `haveI := Fintype.ofFinite ι`. Use `set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def`. Establish `henc : Function.Injective enc` using `fun a b h => (Fintype.equivFin ι).injective (Fin.ext h)`. Use `set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS`.

Establish `memS : ∀ x : S, enc (x : ι) < enc (s x)` using `fun x => (Finset.mem_filter.1 x.2).2`. Use `⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j k h`. Conclude with `S.equivFin.symm.injective (Subtype.ext h)`. Introduce `j k h`.

Simplify using `only at h`. Establish `hj` using `memS (S.equivFin.symm j)`. Establish `hk` using `memS (S.equivFin.symm k)`. Generalize the expression as in `(S.equivFin.symm j : ι) = a at h hj`. Generalize the expression as in `(S.equivFin.symm k : ι) = b at h hk`.

Substitute `h` using the available equality. Rewrite `hk` using `[hs]`. Use linear arithmetic over natural numbers and integers. Introduce `i`. Distinguish the cases in `hi : s i = i`.

Conclude with `Or.inl hi`. Use `right`. Establish `hne : enc i ≠ enc (s i)` using `fun h => hi (henc h).symm`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Establish `hm : i ∈ S` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩`.

Conclude with `⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩`. Establish `hm : s i ∈ S` using `Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩`. Conclude with `⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩`.
-/
theorem involution_pair_representatives :
    ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι),
      (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧
        ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  intro ι _ s hs
  classical
  haveI := Fintype.ofFinite ι
  set enc : ι → ℕ := fun i => (Fintype.equivFin ι i : ℕ) with henc_def
  have henc : Function.Injective enc := fun a b h =>
    (Fintype.equivFin ι).injective (Fin.ext h)
  set S : Finset ι := Finset.univ.filter (fun i => enc i < enc (s i)) with hS
  have memS : ∀ x : S, enc (x : ι) < enc (s x) := fun x => (Finset.mem_filter.1 x.2).2
  refine ⟨S.card, fun j => (S.equivFin.symm j : ι), ?_, ?_, ?_⟩
  · intro j k h
    exact S.equivFin.symm.injective (Subtype.ext h)
  · intro j k h
    simp only at h
    have hj := memS (S.equivFin.symm j)
    have hk := memS (S.equivFin.symm k)
    generalize (S.equivFin.symm j : ι) = a at h hj
    generalize (S.equivFin.symm k : ι) = b at h hk
    subst h
    rw [hs] at hk
    omega
  · intro i
    by_cases hi : s i = i
    · exact Or.inl hi
    right
    have hne : enc i ≠ enc (s i) := fun h => hi (henc h).symm
    rcases lt_or_gt_of_ne hne with h | h
    · have hm : i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩
      exact ⟨S.equivFin ⟨i, hm⟩, Or.inl (by simp)⟩
    · have hm : s i ∈ S := Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [hs]; exact h⟩
      exact ⟨S.equivFin ⟨s i, hm⟩, Or.inr (by simp [hs])⟩

end GlobalTheory
