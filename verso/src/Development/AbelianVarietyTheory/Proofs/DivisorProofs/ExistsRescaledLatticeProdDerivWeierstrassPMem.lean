import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledPeriodPairInvariantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStableStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

/- English proof (translation)
Introduce `p F L t hp h4 h3 hD`. Use `set c := sqProd p L t with hc`. Establish `hc0 : c ≠ 0` using `(GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2`. Establish `hc2 : c ^ 2 ∈ F` using `(GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1`. Take `⟨L', hlat, hg₂, hg₃, hder, hj⟩` from `GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0`.

Take `⟨hcard, -⟩` from `GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4`. Use `⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩` and prove the remaining obligations. Introduce `ω hω`. Establish `hz : c * (c⁻¹ * ω) ∈ L'.lattice` using `by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]`. Establish `hz'` using `(hlat _).1 hz`.

Use `(hlat _).2 (hD.mul _ hz')` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul]`. Then use the resulting hypothesis. Rewrite using `[hg₂]`. Establish `: (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹` using `by ring`. Rewrite using `[this]`.

Conclude with `mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem`. Rewrite using `[hg₃]`. Establish `: (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹` using `by ring`. Rewrite using `[this]`. Conclude with `mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem`.

Rewrite using `[hlat]`. Conclude with `hD.notMem`. Use `(hlat _).2 hD.ker` as an intermediate fact. Rewrite `this` using `[← mul_assoc, mul_comm c, mul_assoc]`. Then use the resulting hypothesis. Establish `hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c`.

Unfold `sqProd`. Establish `: ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) = (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k)`. Introduce `k`. Unfold `sqPt`. Rewrite using `[← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]`.

Rewrite using `[Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hc]`. Both sides reduce to the same expression. Rewrite using `[hprod]`. Use `set n := Fintype.card (Sq p) with hn`. Establish `: ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹`.

Take `⟨m, hm⟩ : Odd n` from `(GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2`. Rewrite using `[hm]`. Establish `: (2 * m + 1 - 1) / 2 = m` using `by omega`. Rewrite using `[this]`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises.

Rewrite using `[inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring, inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]`. Rewrite using `[this]`. Conclude with `inv_mem (pow_mem hc2 _)`.
-/
theorem exists_datum_sqProd_mem :
    ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p →
      Datum p F L t → ∃ (L' : PeriodPair) (t' : ℂ), Datum p F L' t' ∧
        (latticeCurve L').j = (latticeCurve L).j ∧ sqProd p L' t' ∈ F := by
  intro p F L t hp h4 h3 hD
  set c := sqProd p L t with hc
  have hc0 : c ≠ 0 := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
  have hc2 : c ^ 2 ∈ F := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_sq_mem_stable p F L t hp h4 h3 hD).1
  obtain ⟨L', hlat, hg₂, hg₃, hder, hj⟩ := GlobalTheory.T.exists_scaled_periodPair_invariants L c hc0
  obtain ⟨hcard, -⟩ := GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4
  refine ⟨L', c * t, ⟨?_, ?_, ?_, ?_, ?_⟩, hj, ?_⟩
  · intro ω hω
    have hz : c * (c⁻¹ * ω) ∈ L'.lattice := by rwa [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
    have hz' := (hlat _).1 hz
    have := (hlat _).2 (hD.mul _ hz')
    rwa [← mul_assoc, mul_comm c, mul_assoc, ← mul_assoc c, mul_inv_cancel₀ hc0, one_mul] at this
  · rw [hg₂]
    have : (c ^ 4)⁻¹ = ((c ^ 2) ^ 2)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₂_mem
  · rw [hg₃]
    have : (c ^ 6)⁻¹ = ((c ^ 2) ^ 3)⁻¹ := by ring
    rw [this]
    exact mul_mem (inv_mem (pow_mem hc2 _)) hD.g₃_mem
  · rw [hlat]; exact hD.notMem
  · have := (hlat _).2 hD.ker
    rwa [← mul_assoc, mul_comm c, mul_assoc] at this
  · have hprod : sqProd p L' (c * t) = ((c ^ 3)⁻¹) ^ Fintype.card (Sq p) * c := by
      unfold sqProd
      have : ∀ k : Sq p, L'.derivWeierstrassP (sqPt p (c * t) k) =
          (c ^ 3)⁻¹ * L.derivWeierstrassP (sqPt p t k) := by
        intro k
        unfold sqPt
        rw [← hder, ← mul_assoc, mul_comm ((k.1 : ℕ) : ℂ) c, mul_assoc]
      rw [Finset.prod_congr rfl (fun k _ => this k), Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, hc]
      rfl
    rw [hprod]
    set n := Fintype.card (Sq p) with hn
    have : ((c ^ 3)⁻¹) ^ n * c = ((c ^ 2) ^ (3 * ((n - 1) / 2) + 1))⁻¹ := by
      obtain ⟨m, hm⟩ : Odd n := (GlobalTheory.T.two_mul_card_sq_add_one_eq_and_odd_of_mod_four_eq_three p hp h4).2
      rw [hm]
      have : (2 * m + 1 - 1) / 2 = m := by omega
      rw [this]
      apply eq_inv_of_mul_eq_one_left
      rw [inv_pow, mul_assoc, show c * (c ^ 2) ^ (3 * m + 1) = (c ^ 3) ^ (2 * m + 1) by ring,
        inv_mul_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hc0))]
    rw [this]
    exact inv_mem (pow_mem hc2 _)

end GlobalTheory.CMModel
