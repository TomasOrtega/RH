import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.RhoFrob
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormSubOnePowThreeLe

open Formalism.ConjugateSelfDual UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Use symmetry to reverse the relation. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. A detailed English derivation is pending.
-/
theorem UpperTheory.exists_integral_powerSeries_of_bounded_distribution :
    ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (ν : ∀ M : ℕ, (ZMod (l ^ M) → Qbar l) →ₗ[Qbar l] Qbar l),
      (∀ M, 1 ≤ M → ∀ (g : ZMod (l ^ M) → Qbar l) (g' : ZMod (l ^ (M + 1)) → Qbar l), (∀ y : ℕ, g' y = g y) → ν (M + 1) g' = ν M g) →
      (∀ M, 1 ≤ M → ∀ x : ZMod (l ^ M), ν M (Pi.single x 1) ∈ c.O) →
      ∃ L : PowerSeries (Qbar l), (∀ n, L.coeff n ∈ c.O) ∧ ∀ r, 1 ≤ r → ∀ z : Qbar l, z ^ (l ^ r) = 1 →
        Cg (2 * r) (tval L (l ^ (3 * r)) z) (ν r (fun x => z ^ x.val)) := by
  intro l _ c ν hcomp hO
  classical
  let μ : (r : ℕ) → ZMod (l ^ r) → Qbar l := fun r x =>
    if r = 0 then ∑ x' : ZMod (l ^ 1), ν 1 (Pi.single x' 1) else ν r (Pi.single x 1)
  have hsum : ∀ r, 1 ≤ r → ∀ x : ZMod (l ^ r), ν r (Pi.single x 1) =
      ∑ x' ∈ Finset.univ.filter (fun x' : ZMod (l ^ (r + 1)) =>
        ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r)) x' = x),
        ν (r + 1) (Pi.single x' 1) := by
    intro r hr x
    rw [← map_sum]
    symm
    apply hcomp r hr
    intro y
    rw [Finset.sum_apply]
    simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and,
      map_natCast]
  obtain ⟨L, hLO, hL⟩ := GlobalTheory.AmiceDist.amice l c μ
    (fun r x => by
      by_cases hr : r = 0
      · simp only [μ, if_pos hr]
        exact sum_mem (fun x' _ => hO 1 le_rfl x')
      · simp only [μ, if_neg hr]
        exact hO r (Nat.one_le_iff_ne_zero.2 hr) x)
    (fun r x => by
      have hr1 : r + 1 ≠ 0 := by omega
      simp only [μ, if_neg hr1]
      by_cases hr : r = 0
      · subst hr
        simp only [if_true]
        have hf : Finset.univ.filter (fun x' : ZMod (l ^ (0 + 1)) =>
            ZMod.castHom (pow_dvd_pow l (Nat.le_succ 0)) (ZMod (l ^ 0)) x' = x) = Finset.univ :=
          Finset.filter_true_of_mem
            (fun x' _ => (show ∀ a b : ZMod 1, a = b from fun a b => Subsingleton.elim a b) _ _)
        rw [hf]
      · simp only [if_neg hr]
        exact hsum r (Nat.one_le_iff_ne_zero.2 hr) x)
  refine ⟨L, hLO, fun r hr z hz => ?_⟩
  have h1 := hL r hr z hz
  have h2 : ∑ x, μ r x * z ^ x.val = ν r (fun x => z ^ x.val) := by
    have hr0 : r ≠ 0 := by omega
    simp only [μ, if_neg hr0]
    have h3 : (fun x : ZMod (l ^ r) => z ^ x.val) = ∑ x, z ^ x.val • Pi.single x (1 : Qbar l) := by
      funext y
      simp [Finset.sum_apply, Pi.single_apply]
    rw [h3, map_sum]
    simp [map_smul, mul_comm]
  rwa [h2] at h1
