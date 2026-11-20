import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

/- English proof (translation)
Introduce `G _ Λ B hB`. Establish `hneg : ∀ r x, x ∈ B r → -x ∈ B r`. Introduce `r x hx`. Establish `h` using `hB.sub_mem 0 r 0 x (hB.zero_mem 0 le_rfl) hx`. Simplify using `using h`.

Use `⟨?_, hneg, ?_⟩` and prove the remaining obligations. Introduce `r r' hrr' x hx`. Establish `h` using `hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.mpr hrr'))`. Simplify using `using h`. Introduce `r r' x y hx hy`.

Establish `h` using `hB.sub_mem r r' x (-y) hx (hneg r' y hy)`. Simplify using `using h`.
-/
theorem isBallFam_mono_neg_add :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (∀ r r', r ≤ r' → B r ⊆ B r') ∧ (∀ r x, x ∈ B r → -x ∈ B r) ∧
        (∀ r r' x y, x ∈ B r → y ∈ B r' → x + y ∈ B (r + r')) := by
  intro G _ Λ B hB
  have hneg : ∀ r x, x ∈ B r → -x ∈ B r := by
    intro r x hx
    have h := hB.sub_mem 0 r 0 x (hB.zero_mem 0 le_rfl) hx
    simpa using h
  refine ⟨?_, hneg, ?_⟩
  · intro r r' hrr' x hx
    have h := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.mpr hrr'))
    simpa using h
  · intro r r' x y hx hy
    have h := hB.sub_mem r r' x (-y) hx (hneg r' y hy)
    simpa using h

end GlobalTheory.VolBr
