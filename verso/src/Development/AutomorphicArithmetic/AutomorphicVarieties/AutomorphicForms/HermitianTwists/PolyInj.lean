import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf

open Polynomial in
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Both sides reduce to the same expression.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Treat this case separately. Treat this case separately.

Treat this case separately. A detailed English derivation is pending.
-/
theorem UpperTheory.V.Af.Rn.polyInj :
    UpperTheory.V.Af.Rn.PolyInj := by
  intro q hq j B B' h
  have key : ∀ s : Multiset ℂ,
      (Multiset.map (fun b ↦ Polynomial.X - Polynomial.C ((q : ℂ) ^ j * b)) s).prod.roots
        = s.map (fun b ↦ (q : ℂ) ^ j * b) := by
    intro s
    rw [← Polynomial.roots_multiset_prod_X_sub_C (s.map (fun b ↦ (q : ℂ) ^ j * b)), Multiset.map_map]
    rfl
  have hroots := congrArg Polynomial.roots h
  rw [key, key] at hroots
  have hqC : ((q : ℂ) ^ j) ≠ 0 := zpow_ne_zero _ (by exact_mod_cast hq.ne')
  have h1 := Multiset.map_injective (mul_right_injective₀ hqC) hroots
  unfold UpperTheory.V.Af.algSat at h1
  simp only [Multiset.bind_def, Multiset.pure_def, Multiset.bind_singleton, ← Multiset.map_map] at h1
  refine Multiset.map_injective (fun _ _ e ↦ Units.ext e) (Multiset.map_injective (mul_right_injective₀ ?_) h1)
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  first
    | exact Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hq' _).ne'
    | simp [hq.ne']
    | exact_mod_cast (Real.rpow_pos_of_pos hq' _).ne'
