import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IndexCocycleOrbits.OrbStabZ

namespace Formalism.L2.SG.Pf.IndexCocycleOrbits

/- English proof (translation)
Establish `keyR : (aB : ℝ) * n = m * aC` using `by exact_mod_cast key`. Establish `hmR : (m : ℝ) ≠ 0` using `by exact_mod_cast hm`. Establish `hnR : (n : ℝ) ≠ 0` using `by exact_mod_cast hn`. Use `push_cast`. Distinguish the cases in `haC : (aC : ℝ) = 0`.

Establish `haB : (aB : ℝ) = 0`. Establish `h0 : (aB : ℝ) * n = 0` using `by rw [keyR, haC, mul_zero]`. Break down `mul_eq_zero.mp h0 with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h hnR`.

Rewrite using `[haB, haC]`. Simplify using the standard rewrite rules. Establish `haB : (aB : ℝ) ≠ 0`. Introduce `h`. Establish `h0 : (m : ℝ) * aC = 0` using `by rw [← keyR, h, zero_mul]`.

Break down `mul_eq_zero.mp h0 with h' | h'` into its components or cases. Conclude with `hmR h'`. Conclude with `haC h'`. Rewrite using `[eq_comm, mul_div_assoc', div_eq_div_iff haC haB]`. Take the linear combination `(cA : ℝ) * keyR`.
-/
theorem index_ratio_identity (m n aB aC cA : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (key : aB * n = m * aC) :
    ((m * cA : ℕ) : ℝ) / (aB : ℝ) = (n : ℝ) * ((cA : ℝ) / (aC : ℝ)) := by
  have keyR : (aB : ℝ) * n = m * aC := by exact_mod_cast key
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  push_cast
  by_cases haC : (aC : ℝ) = 0
  · have haB : (aB : ℝ) = 0 := by
      have h0 : (aB : ℝ) * n = 0 := by rw [keyR, haC, mul_zero]
      rcases mul_eq_zero.mp h0 with h | h
      · exact h
      · exact absurd h hnR
    rw [haB, haC]
    simp
  · have haB : (aB : ℝ) ≠ 0 := by
      intro h
      have h0 : (m : ℝ) * aC = 0 := by rw [← keyR, h, zero_mul]
      rcases mul_eq_zero.mp h0 with h' | h'
      · exact hmR h'
      · exact haC h'
    rw [eq_comm, mul_div_assoc', div_eq_div_iff haC haB]
    linear_combination (cA : ℝ) * keyR

/- English proof (translation)
Introduce `G _ A B C hBC hn`. Establish `hBinf : B ⊓ C = B` using `inf_eq_left.mpr hBC`. Establish `e1 : B.relIndex (C ⊓ A) * C.relIndex A = B.relIndex A`. Establish `h` using `Subgroup.relIndex_inf_mul_relIndex B C A`. Rewrite `h` using `[hBinf]`. Then use the resulting hypothesis.

Establish `e2 : A.relIndex (B ⊓ C) * B.relIndex C = (A ⊓ B).relIndex C` using `Subgroup.relIndex_inf_mul_relIndex A B C`. Rewrite `e2` using `[hBinf]`. Establish `e3 : B.relIndex (A ⊓ C) * A.relIndex C = (B ⊓ A).relIndex C` using `Subgroup.relIndex_inf_mul_relIndex B A C`. Rewrite `e3` using `[inf_comm B A, inf_comm A C]`. Establish `hm : B.relIndex (C ⊓ A) ≠ 0` using `fun h => hn (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)`.

Establish `key : A.relIndex B * B.relIndex C = B.relIndex (C ⊓ A) * A.relIndex C` using `by rw [e2, e3]`. Unfold `IdxRatio`. Rewrite using `[← e1]`. Conclude with `index_ratio_identity _ _ _ _ _ hm hn key`.
-/
theorem idxCocycle : IdxCocycle := by
  intro G _ A B C hBC hn
  have hBinf : B ⊓ C = B := inf_eq_left.mpr hBC
  have e1 : B.relIndex (C ⊓ A) * C.relIndex A = B.relIndex A := by
    have h := Subgroup.relIndex_inf_mul_relIndex B C A
    rwa [hBinf] at h
  have e2 : A.relIndex (B ⊓ C) * B.relIndex C = (A ⊓ B).relIndex C :=
    Subgroup.relIndex_inf_mul_relIndex A B C
  rw [hBinf] at e2
  have e3 : B.relIndex (A ⊓ C) * A.relIndex C = (B ⊓ A).relIndex C :=
    Subgroup.relIndex_inf_mul_relIndex B A C
  rw [inf_comm B A, inf_comm A C] at e3
  have hm : B.relIndex (C ⊓ A) ≠ 0 := fun h =>
    hn (Subgroup.relIndex_eq_zero_of_le_right inf_le_left h)
  have key : A.relIndex B * B.relIndex C = B.relIndex (C ⊓ A) * A.relIndex C := by rw [e2, e3]
  unfold IdxRatio
  rw [← e1]
  exact index_ratio_identity _ _ _ _ _ hm hn key

end Formalism.L2.SG.Pf.IndexCocycleOrbits
