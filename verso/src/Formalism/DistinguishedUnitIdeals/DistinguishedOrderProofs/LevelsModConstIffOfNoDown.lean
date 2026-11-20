import Mathlib
import Formalism.DistinguishedUnitIdeals.CoprimeProd

noncomputable section

namespace Formalism.ExponentWindows

open PowerSeries

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.
-/
theorem lam_eq_pow_mul {O : Type} [CommRing O] (p : ℕ → PowerSeries O) (H : ℕ → ℕ) (ell s : ℕ)
    (hs : s < ell) :
    abelian₂ p H ell = p s ^ H s * ∏ t ∈ (Finset.range ell).erase s, p t ^ H t := by
  unfold abelian₂
  rw [← Finset.mul_prod_erase (Finset.range ell) (fun t => p t ^ H t) (Finset.mem_range.mpr hs)]

/- English proof (translation)
Split into cases according to the possible forms of the given data. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Treat this case separately. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Normalize the expressions using the abelian group laws. Treat this case separately.
-/
theorem levelCond_of_sub_pow_smul {O : Type} [CommRing O] {r : ℕ} (ϖ : O) (P : PowerSeries O)
    (H b : ℕ) (k : Kind) (hk : k ≠ Kind.down) (V : Submodule O (Fin r → O))
    (y w : Fin r → PowerSeries O) (m : ℕ)
    (h : LevelCond ϖ P H b k V (C (ϖ ^ m) • y - P ^ H • w)) :
    LevelCond ϖ P H b k V y := by
  cases k with
  | thin =>
    obtain ⟨N, z, hz⟩ := h
    refine ⟨N + m, z + C (ϖ ^ N) • w, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, ← hz, smul_sub, smul_comm (P ^ H) (C (ϖ ^ N)) w]
    abel
  | up =>
    obtain ⟨N, c, z, hc, hz⟩ := h
    refine ⟨N + m, c, z + C (ϖ ^ N) • w, hc, ?_⟩
    rw [pow_add, map_mul, mul_smul, smul_add, smul_comm (P ^ H) (C (ϖ ^ N)) w, ← add_assoc, ← hz,
      smul_sub]
    abel
  | down => exact absurd rfl hk

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the indicated hypotheses using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem levels_mod_const_iff_of_no_down : MNone := by
  intro O _ _ _ ϖ _ ℓ ell r p H b kind V _ _ _ _ hnd y
  constructor
  · intro hII s hs
    obtain ⟨d, k, hd⟩ := hII s hs
    rw [lam_eq_pow_mul p H ell s hs, mul_smul] at hd
    exact levelCond_of_sub_pow_smul ϖ (p s) (H s) (b s) (kind s) (hnd s hs) (V s) y _ k hd
  · intro hNN s hs
    refine ⟨0, 0, ?_⟩
    have h0 : (cst (0 : Fin r → O) : Fin r → PowerSeries O) = 0 := by
      funext i; simp [cst]
    simpa [h0] using hNN s hs

end Formalism.ExponentWindows
