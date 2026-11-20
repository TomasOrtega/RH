import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension

open Matrix

/- English proof (translation)
Introduce `d`. Proceed by induction on `d with`. Consider the case `zero`. Introduce `a u0 hu0 hd har`. Use `⟨0, Fin.elim0, by omega, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fin.append_right_nil u0 _ rfl]`. Conclude with `hu0.comp _ (Fin.cast_injective _)`. Consider the case `succ d ih`. Introduce `a u0 hu0 hd har`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, w j ∉ Submodule.span ℚ (Set.range u0) := by`.

Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Use `haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩`. Establish `htop : Submodule.span ℚ (Set.range w) = ⊤` using `hw.span_eq_top_of_card_eq_finrank (by simp)`. Establish `hle : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range u0)` using `Submodule.span_le.mpr (Set.range_subset_iff.mpr hcon)`.

Rewrite `hle` using `[htop, top_le_iff]`. Establish `h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range u0)) ≤ Fintype.card (Fin a)` using `finrank_range_le_card (R := ℚ) u0`. Rewrite `h1` using `[hle, finrank_top]`. Simplify using `at h1`. Use linear arithmetic over natural numbers and integers.

Establish `hu1 : LinearIndependent ℚ (Fin.snoc u0 (w j) : Fin (a + 1) → (Fin r → ℚ))` using `linearIndependent_fin_snoc.mpr ⟨hu0, hj⟩`. Take `⟨m, f, hm, hli⟩` from `ih (a + 1) (Fin.snoc u0 (w j)) hu1 (by omega) (by omega)`. Use `⟨m + 1, Fin.cons j f, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.comp_cons, Fin.append_right_cons]`. Conclude with `hli.comp _ (Fin.cast_injective _)`.
-/
private theorem exists_linearIndependent_append_of_codim {r : ℕ} (w : Fin r → (Fin r → ℚ))
    (hw : LinearIndependent ℚ w) :
    ∀ d a (u0 : Fin a → (Fin r → ℚ)), LinearIndependent ℚ u0 → r - a = d → a ≤ r →
      ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  intro d
  induction d with
  | zero =>
    intro a u0 hu0 hd har
    refine ⟨0, Fin.elim0, by omega, ?_⟩
    rw [Fin.append_right_nil u0 _ rfl]
    exact hu0.comp _ (Fin.cast_injective _)
  | succ d ih =>
    intro a u0 hu0 hd har
    obtain ⟨j, hj⟩ : ∃ j, w j ∉ Submodule.span ℚ (Set.range u0) := by
      by_contra hcon
      push_neg at hcon
      haveI : Nonempty (Fin r) := ⟨⟨0, by omega⟩⟩
      have htop : Submodule.span ℚ (Set.range w) = ⊤ :=
        hw.span_eq_top_of_card_eq_finrank (by simp)
      have hle : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range u0) :=
        Submodule.span_le.mpr (Set.range_subset_iff.mpr hcon)
      rw [htop, top_le_iff] at hle
      have h1 : Module.finrank ℚ (Submodule.span ℚ (Set.range u0)) ≤ Fintype.card (Fin a) :=
        finrank_range_le_card (R := ℚ) u0
      rw [hle, finrank_top] at h1
      simp at h1
      omega
    have hu1 : LinearIndependent ℚ (Fin.snoc u0 (w j) : Fin (a + 1) → (Fin r → ℚ)) :=
      linearIndependent_fin_snoc.mpr ⟨hu0, hj⟩
    obtain ⟨m, f, hm, hli⟩ := ih (a + 1) (Fin.snoc u0 (w j)) hu1 (by omega) (by omega)
    refine ⟨m + 1, Fin.cons j f, by omega, ?_⟩
    rw [Fin.comp_cons, Fin.append_right_cons]
    exact hli.comp _ (Fin.cast_injective _)

/- English proof (translation)
Establish `har : a ≤ r`. Establish `h` using `hu0.fintype_card_le_finrank`. Simplify using `using h`. Conclude with `exists_linearIndependent_append_of_codim w hw _ a u0 hu0 rfl har`.
-/
theorem exists_append_li {a r : ℕ} (u0 : Fin a → (Fin r → ℚ)) (hu0 : LinearIndependent ℚ u0)
    (w : Fin r → (Fin r → ℚ)) (hw : LinearIndependent ℚ w) :
    ∃ m, ∃ f : Fin m → Fin r, a + m = r ∧ LinearIndependent ℚ (Fin.append u0 (w ∘ f)) := by
  have har : a ≤ r := by
    have h := hu0.fintype_card_le_finrank
    simpa using h
  exact exists_linearIndependent_append_of_codim w hw _ a u0 hu0 rfl har

end ReciprocityTheory.GeometryOfNumbersTheory.LinearIndependentExtension
