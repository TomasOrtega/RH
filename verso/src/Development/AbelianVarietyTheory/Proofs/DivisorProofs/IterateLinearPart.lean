import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationFormalGroupLawIsLinearStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMulStatement

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LinearPartIteration

variable {R : Type} [CommRing R] {d : ℕ}

def part (F : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun α => if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (part F j) = if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0 := rfl

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_part]`. Simplify using the standard rewrite rules.
-/
theorem constantCoeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) :
    constantCoeff (part F j) = coeff (Finsupp.single j 1) F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_part]
  simp

/- English proof (translation)
Rewrite using `[X_def, coeff_monomial_mul, one_mul, coeff_part]`. Distinguish the cases in `h : β j = 0`. Rewrite using `[if_neg, if_neg]`. Simplify using `[h]`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `hle : Finsupp.single j 1 ≤ β` using `by rw [Finsupp.single_le_iff]; omega`. Rewrite using `[if_pos hle, tsub_add_cancel_of_le hle]`. Establish `: (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0)`. Prove the components needed by the constructor for the conclusion.

Introduce `H`. Use `⟨h, fun k hk => ?_⟩` and prove the remaining obligations. Use `H k hk` as an intermediate fact. Rewrite `this` using `[Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero]`. Then use the resulting hypothesis. Introduce `H k hk`.

Rewrite using `[Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]`. Simplify using `only [this]`.
-/
theorem coeff_X_mul_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (β : Fin d →₀ ℕ) :
    coeff β (X j * part F j) = if β j ≠ 0 ∧ ∀ k < j, β k = 0 then coeff β F else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul, coeff_part]
  by_cases h : β j = 0
  · rw [if_neg, if_neg]
    · simp [h]
    · rw [Finsupp.single_le_iff]; omega
  · have hle : Finsupp.single j 1 ≤ β := by rw [Finsupp.single_le_iff]; omega
    rw [if_pos hle, tsub_add_cancel_of_le hle]
    have : (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0) := by
      constructor
      · intro H
        refine ⟨h, fun k hk => ?_⟩
        have := H k hk
        rwa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero] at this
      · intro H k hk
        rw [Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]
    simp only [this]

/- English proof (translation)
Use extensionality with `β`. Rewrite using `[map_add, map_sum, coeff_C]`. Simplify using `only [coeff_X_mul_part]`. Distinguish the cases in `hβ : β = 0`. Substitute `hβ` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hβ, zero_add]`. Establish `hne : β.support.Nonempty` using `Finsupp.support_nonempty_iff.2 hβ`. Establish `h0 : β (β.support.min' hne) ≠ 0` using `Finsupp.mem_support_iff.1 (β.support.min'_mem hne)`. Establish `h1 : ∀ k < β.support.min' hne, β k = 0` using `fun k hk => by`.

Assume the negation of the conclusion as `hk0`. Conclude with `absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)`. Rewrite using `[Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]`. Introduce `j _ hj`. Rewrite using `[if_neg]`.

Introduce and unpack `⟨h2, h3⟩`. Break down `lt_or_gt_of_ne hj with h | h` into its components or cases. Conclude with `h2 (h1 j h)`. Conclude with `h0 (h3 _ h)`. Simplify using the standard rewrite rules.
-/
theorem eq_const_add_sum (F : MvPowerSeries (Fin d) R) :
    F = C (constantCoeff F) + ∑ j, X j * part F j := by
  classical
  ext β
  rw [map_add, map_sum, coeff_C]
  simp only [coeff_X_mul_part]
  by_cases hβ : β = 0
  · subst hβ
    simp
  · rw [if_neg hβ, zero_add]
    have hne : β.support.Nonempty := Finsupp.support_nonempty_iff.2 hβ
    have h0 : β (β.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.1 (β.support.min'_mem hne)
    have h1 : ∀ k < β.support.min' hne, β k = 0 := fun k hk => by
      by_contra hk0
      exact absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)
    rw [Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact h2 (h1 j h)
      · exact h0 (h3 _ h)
    · simp

/- English proof (translation)
Introduce `p hp R _ d μ h0 h1 _ u F`. Take `⟨hadd, hsmul, hC⟩` from `GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u`. Set `D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R` to `{ toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }`. Establish `hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G` using `fun G => by`. Rewrite using `[Module.End.pow_apply]`.

Both sides reduce to the same expression. Establish `hDC : ∀ a : R, (D ^ p) (C a) = 0` using `fun a => by`. Take `⟨n, hn⟩` from `Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero`. Rewrite using `[hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]`. Establish `key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p) (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r` using `fun j => by`.

Rewrite using `[← hD]`. Conclude with `GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])`. Use `choose r hr using key`. Use `⟨∑ j, r j, ?_⟩` and prove the remaining obligations. Establish `hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j))` using `by conv_lhs => rw [eq_const_add_sum F]`.

Rewrite using `[map_add, hDC, zero_add, map_sum, map_sum]`. Simplify using `only [hD]`. Rewrite using `[hF, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul, ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply, smul_eq_mul, mul_comm (constantCoeff _)]`.
-/
theorem iterate_linear_part : ∀ (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [inst : CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ (i : Fin d), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) R → R) (μ i) = (0 : R)) → ((GlobalTheory.Katz.op μ (fun (i : Fin d) ↦ MvPowerSeries.X i) fun (x : Fin d) ↦ (0 : MvPowerSeries (Fin d) R)) = fun (i : Fin d) ↦ MvPowerSeries.X i) → (∀ (i : Fin d), GlobalTheory.Katz.swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ (r : R), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] F) - ∑ j : Fin d, (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] (MvPowerSeries.X j)) * (MvPowerSeries.coeff fun₀ | j => (1 : ℕ) : MvPowerSeries (Fin d) R → R) F = (↑p : R) * r := by
  intro p hp R _ d μ h0 h1 _ u F
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u
  let D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R :=
    { toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G := fun G => by
    rw [Module.End.pow_apply]; rfl
  have hDC : ∀ a : R, (D ^ p) (C a) = 0 := fun a => by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
    rw [hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]
  have key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p)
      (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r := fun j => by
    rw [← hD]
    exact GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])
  choose r hr using key
  refine ⟨∑ j, r j, ?_⟩
  have hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j)) := by
    conv_lhs => rw [eq_const_add_sum F]
    rw [map_add, hDC, zero_add, map_sum, map_sum]
  simp only [hD]
  rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul,
    ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply,
    smul_eq_mul, mul_comm (constantCoeff _)]

end GlobalTheory.LinearPartIteration
