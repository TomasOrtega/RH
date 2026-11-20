import Mathlib

namespace GlobalTheory

/- English proof (translation)
Take `⟨s0, hs0s, hs0⟩` from `(Ideal.span_eq_top_iff_finite s).1 hs`. Use `choose! E hEm using hE`. Set `T : Set A` to `⋃ g ∈ (s0 : Set R), (E g : Set A)`. Establish `hT : T.Finite` using `Set.Finite.biUnion s0.finite_toSet fun g _ => (E g).finite_toSet`. Use `Submodule.FG.of_le (Submodule.fg_span hT) ?_` and prove the remaining obligations.

Introduce `b hb`. Use `Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s0 : Set R) hs0 b ?_` and prove the remaining obligations. Introduce `g`. Take `⟨m, hm⟩` from `hEm g.1 (hs0s g.2) b hb`. Use `⟨m, ?_⟩` and prove the remaining obligations.

Establish `hle : Submodule.span R (E g.1 : Set A) ≤ Submodule.span R T` using `Submodule.span_mono (Set.subset_biUnion_of_mem (u := fun g => (E g : Set A)) g.2)`. Establish `: (g.1 ^ m) • b = algebraMap R A g.1 ^ m * b`. Rewrite using `[Algebra.smul_def, map_pow]`. Rewrite using `[this]`. Conclude with `hle hm`.
-/
theorem submodule_fg_of_locally_le_fg {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] (M : Submodule R A) (s : Set R) (hs : Ideal.span s = ⊤)
    (hE : ∀ g ∈ s, ∃ E : Finset A, ∀ b ∈ M, ∃ m : ℕ,
      algebraMap R A g ^ m * b ∈ Submodule.span R (E : Set A)) : M.FG := by
  classical
  obtain ⟨s0, hs0s, hs0⟩ := (Ideal.span_eq_top_iff_finite s).1 hs
  choose! E hEm using hE
  let T : Set A := ⋃ g ∈ (s0 : Set R), (E g : Set A)
  have hT : T.Finite := Set.Finite.biUnion s0.finite_toSet fun g _ => (E g).finite_toSet
  refine Submodule.FG.of_le (Submodule.fg_span hT) ?_
  intro b hb
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (s0 : Set R) hs0 b ?_
  intro g
  obtain ⟨m, hm⟩ := hEm g.1 (hs0s g.2) b hb
  refine ⟨m, ?_⟩
  have hle : Submodule.span R (E g.1 : Set A) ≤ Submodule.span R T :=
    Submodule.span_mono (Set.subset_biUnion_of_mem (u := fun g => (E g : Set A)) g.2)
  have : (g.1 ^ m) • b = algebraMap R A g.1 ^ m * b := by
    rw [Algebra.smul_def, map_pow]
  rw [this]
  exact hle hm

end GlobalTheory
