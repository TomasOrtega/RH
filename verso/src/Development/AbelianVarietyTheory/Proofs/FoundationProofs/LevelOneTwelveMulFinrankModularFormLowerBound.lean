import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. Extract witnesses or component facts from the available result. Replace the chosen expression with an arbitrary variable.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Replace the chosen expression with an arbitrary variable. Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
theorem levelOne_twelve_mul_finrank_lower_bound :
    ∀ n : ℤ, Even n → n + 5 + 3 * (if n % 4 = 0 then 1 else -1) +
      4 * (if n % 6 = 0 then 1 else if n % 6 = 2 then -1 else 0) ≤
        12 * (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := by
  intro n hn
  rcases lt_or_ge n 0 with hneg | hpos
  · have h0 : (0 : ℤ) ≤ (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) := Int.natCast_nonneg _
    obtain ⟨m, hm⟩ := hn
    generalize (Module.finrank ℂ (ModularForm 𝒮ℒ n) : ℤ) = d at h0 ⊢
    split_ifs <;> omega
  · lift n to ℕ using hpos
    have hke : Even n := by exact_mod_cast hn
    have hrank := ModularForm.dimension_level_one n hke
    have hfin : Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) =
        if n % 12 = 2 then n / 12 else n / 12 + 1 := by
      exact Module.finrank_eq_of_rank_eq hrank
    obtain ⟨m, hm⟩ := hke
    generalize Module.finrank ℂ (ModularForm 𝒮ℒ (n : ℤ)) = d at hfin ⊢
    split_ifs at hfin ⊢ <;> omega

end GlobalTheory.OddFrame
