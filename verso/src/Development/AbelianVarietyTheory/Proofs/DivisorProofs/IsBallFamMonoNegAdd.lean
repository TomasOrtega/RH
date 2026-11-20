import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.
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
