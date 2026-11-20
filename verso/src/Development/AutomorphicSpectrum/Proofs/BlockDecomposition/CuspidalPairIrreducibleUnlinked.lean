import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

namespace GlobalTheory.CompanionTheory.BZPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `a`. Proceed by induction on `a with`. Consider the case `zero`. Introduce `_`. Rewrite using `[Nat.cast_zero, IrrGL.nu_zero, hu]`.

Consider the case `succ n ih`. Introduce `hn`. Establish `h1 : Γ.first.nu ((n + 1 : ℕ) : ℂ) = u.nu 1`. Rewrite using `[← ih (by omega), IrrGL.nu_nu, Nat.cast_succ]`. Establish `hmem : Γ.first.nu ((n + 1 : ℕ) : ℂ) ∈ Γ.carrier` using `Segment.mem_carrier.2 ⟨n + 1, hn, rfl⟩`.

Break down `(Set.mem_union _ _ _).1 (hΓ hmem) with h | h` into its components or cases. Conclude with `Set.mem_singleton_iff.1 h`. Conclude with `absurd ((Set.mem_singleton_iff.1 h).symm.trans h1) hv`.
-/
theorem terms_eq_first (Γ : Segment k) {u v : IrrGL k} (hu : Γ.first = u)
    (hΓ : Γ.carrier ⊆ {u} ∪ {v}) (hv : v ≠ u.nu 1) :
    ∀ a : ℕ, a < Γ.len → Γ.first.nu a = u := by
  intro a
  induction a with
  | zero =>
    intro _
    rw [Nat.cast_zero, IrrGL.nu_zero, hu]
  | succ n ih =>
    intro hn
    have h1 : Γ.first.nu ((n + 1 : ℕ) : ℂ) = u.nu 1 := by
      rw [← ih (by omega), IrrGL.nu_nu, Nat.cast_succ]
    have hmem : Γ.first.nu ((n + 1 : ℕ) : ℂ) ∈ Γ.carrier := Segment.mem_carrier.2 ⟨n + 1, hn, rfl⟩
    rcases (Set.mem_union _ _ _).1 (hΓ hmem) with h | h
    · exact Set.mem_singleton_iff.1 h
    · exact absurd ((Set.mem_singleton_iff.1 h).symm.trans h1) hv

/- English proof (translation)
Introduce and unpack `⟨⟨Γ, hΓ⟩, hxy, -⟩`. Simplify using `only [Segment.carrier_single] at hΓ hxy`. Establish `hne : x ≠ y` using `fun h => hxy (by subst h; exact subset_rfl)`. Establish `key : ∀ u v : IrrGL k, Γ.first = u → Γ.carrier ⊆ {u} ∪ {v} → v ≠ u.nu 1 → v ∈ Γ.carrier → v = u`. Introduce `u v hu hsub hv hvmem`.

Take `⟨a, ha, hav⟩` from `Segment.mem_carrier.1 hvmem`. Rewrite using `[← hav]`. Conclude with `terms_eq_first Γ hu hsub hv a ha`. Establish `hfirst : Γ.first ∈ Γ.carrier` using `Segment.mem_carrier.2 ⟨0, Γ.len_pos, by rw [Nat.cast_zero, IrrGL.nu_zero]⟩`. Rewrite `hfirst` using `[hΓ]`.

Break down `(Set.mem_union _ _ _).1 hfirst with h | h` into its components or cases. Use `hne (key x y (Set.mem_singleton_iff.1 h) hΓ.subset h1 ?_).symm` and prove the remaining obligations. Rewrite using `[hΓ]`. Conclude with `Set.mem_union_right _ (Set.mem_singleton y)`. Use `hne (key y x (Set.mem_singleton_iff.1 h) ?_ h2 ?_)` and prove the remaining obligations.

Introduce `z hz`. Rewrite `hz` using `[hΓ]`. Break down `(Set.mem_union _ _ _).1 hz with hz | hz` into its components or cases. Conclude with `Set.mem_union_right _ hz`. Conclude with `Set.mem_union_left _ hz`.

Rewrite using `[hΓ]`. Conclude with `Set.mem_union_left _ (Set.mem_singleton x)`.
-/
theorem not_linked_single {x y : IrrGL k} (hx : x.IsCusp) (hy : y.IsCusp) (h1 : y ≠ x.nu 1) (h2 : x ≠ y.nu 1) :
    ¬ (Segment.single x hx).Linked (Segment.single y hy) := by
  rintro ⟨⟨Γ, hΓ⟩, hxy, -⟩
  simp only [Segment.carrier_single] at hΓ hxy
  have hne : x ≠ y := fun h => hxy (by subst h; exact subset_rfl)
  have key : ∀ u v : IrrGL k, Γ.first = u → Γ.carrier ⊆ {u} ∪ {v} → v ≠ u.nu 1 → v ∈ Γ.carrier → v = u := by
    intro u v hu hsub hv hvmem
    obtain ⟨a, ha, hav⟩ := Segment.mem_carrier.1 hvmem
    rw [← hav]
    exact terms_eq_first Γ hu hsub hv a ha
  have hfirst : Γ.first ∈ Γ.carrier :=
    Segment.mem_carrier.2 ⟨0, Γ.len_pos, by rw [Nat.cast_zero, IrrGL.nu_zero]⟩
  rw [hΓ] at hfirst
  rcases (Set.mem_union _ _ _).1 hfirst with h | h
  · refine hne (key x y (Set.mem_singleton_iff.1 h) hΓ.subset h1 ?_).symm
    rw [hΓ]
    exact Set.mem_union_right _ (Set.mem_singleton y)
  · refine hne (key y x (Set.mem_singleton_iff.1 h) ?_ h2 ?_)
    · intro z hz
      rw [hΓ] at hz
      rcases (Set.mem_union _ _ _).1 hz with hz | hz
      · exact Set.mem_union_right _ hz
      · exact Set.mem_union_left _ hz
    · rw [hΓ]
      exact Set.mem_union_left _ (Set.mem_singleton x)

end GlobalTheory.CompanionTheory.BZPair

end
