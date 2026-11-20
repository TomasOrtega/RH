import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

open Complex Finset ArithmeticFunction

noncomputable section

namespace Formalism.ZeroFreeDirichlet

/- English proof (translation)
Establish `hu : IsUnit ((a : ZMod q))` using `(ZMod.isUnit_iff_coprime a q).mpr ha`. Unfold `psiAP psiChi`. Repeatedly rewrite using `[Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Establish `key : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (((Λ n : ℝ) : ℂ) * χ (n : ZMod q)) = ((Λ n : ℝ) : ℂ) * (if (a : ZMod q) = n then (q.totient : ℂ) else 0)`.

Introduce `n`. Rewrite using `[← DirichletCharacter.sum_char_inv_mul_char_eq ℂ hu (n : ZMod q), Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl (fun χ _ => by ring)`. Repeatedly rewrite using `[key]`. Rewrite using `[Complex.ofReal_sum, Finset.sum_filter, Finset.mul_sum]`.

Use `Finset.sum_congr rfl (fun n _ => ?_)` and prove the remaining obligations. Establish `hiff : (n ≡ a [MOD q]) ↔ (a : ZMod q) = n`. Rewrite using `[eq_comm, ZMod.natCast_eq_natCast_iff]`. Distinguish the cases in `h : n ≡ a [MOD q]`. Rewrite using `[if_pos h, if_pos (hiff.mp h)]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_neg h, if_neg (fun h' => h (hiff.mpr h'))]`. Simplify using the standard rewrite rules.
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

/- English proof (translation)
Take `⟨u, hu⟩` from `(ZMod.isUnit_iff_coprime a q).mpr ha`. Rewrite using `[← hu, ZMod.inv_coe_unit]`. Simplify using `[mul_ite, mul_zero, Finset.sum_ite_eq', MulChar.one_apply (Units.isUnit _)]`.
-/
lemma principal_character_orthogonality_term (q a : ℕ) [NeZero q] (ha : Nat.Coprime a q) (x : ℝ) :
    ∑ χ : DirichletCharacter ℂ q, χ ((a : ZMod q)⁻¹) * (if χ = 1 then (x : ℂ) else 0) = (x : ℂ) := by
  obtain ⟨u, hu⟩ := (ZMod.isUnit_iff_coprime a q).mpr ha
  rw [← hu, ZMod.inv_coe_unit]
  simp [mul_ite, mul_zero, Finset.sum_ite_eq', MulChar.one_apply (Units.isUnit _)]

/- English proof (translation)
Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]`.
-/
lemma card_dirichletCharacter_eq_totient (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).card : ℝ) = (q.totient : ℝ) := by
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]

end Formalism.ZeroFreeDirichlet
