import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (authored)
Expand the character sums and exchange the sums over characters and integers. Because a is a unit modulo q, character orthogonality makes the inner sum equal to the totient when the residue of n equals a, and zero otherwise. The surviving von Mangoldt sum is exactly the progression sum.
-/
lemma chebyshev_progression_orthogonality (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    (q.totient : ℂ) * ((psiAP q a x : ℝ) : ℂ) =
      ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * psiChi χ x := by
  have hu : IsUnit ((a : ZMod q)) := (ZMod.isUnit_iff_coprime a q).mpr ha
  unfold psiAP psiChi
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have key : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q,
      χ ((a : ZMod q)⁻¹) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) =
      ((Λ n : ℝ) : ℂ) * (if (a : ZMod q) = n then (q.totient : ℂ) else 0) := by
    intro n
    rw [← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q), Finset.mul_sum]
    exact Finset.sum_congr rfl (fun χ _ => by ring)
  simp_rw [key]
  rw [Complex.ofReal_sum, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hiff : (n ≡ a [MOD q]) ↔ (a : ZMod q) = n := by
    rw [eq_comm, ZMod.natCast_eq_natCast_iff]
  by_cases h : n ≡ a [MOD q]
  · rw [if_pos h, if_pos (hiff.mp h)]; ring
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]; simp

/- English proof (authored)
Only the principal character contributes to the finite sum. The inverse of a is a unit, so the character value at it is one. Its contribution is therefore x.
-/
lemma principal_character_orthogonality_term (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (if χ = 1 then (x : ℂ) else 0) = (x : ℂ) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [← hu, ZMod.inv_coe_unit]
  simp [mul_ite, mul_zero, Finset.sum_ite_eq', MulChar.one_apply (Units.isUnit _)]

/- English proof (authored)
The complex numbers contain the roots of unity needed for the full character group of the finite unit group. The character group has the same cardinality as the unit group, namely the totient. Taking the real value of that cardinality gives the formula.
-/
lemma card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

end Formalism.ZeroFreeDirichlet
