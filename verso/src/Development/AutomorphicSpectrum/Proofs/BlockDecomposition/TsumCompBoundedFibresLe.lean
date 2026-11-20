import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsLatIntVec
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.CompanionTheory.SiegelND.Integ.Hua GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.HS
open scoped Matrix

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre

/- English proof (translation)
Introduce `A B π k h g hg hs`. Establish `hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k`. Introduce `u b`. Establish `hf : ({a | π a = b} : Set A).Finite` using `Set.finite_coe_iff.mp (h b).1`. Combine the equalities or inequalities in the displayed calculation.

Apply `Set.ncard_le_ncard _ hf` to reduce the goal to its premises. Introduce `a ha`. Simplify using `only [Finset.coe_filter, Set.mem_setOf_eq] at ha`. Conclude with `ha.2`. Use `_ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm`.

Use `_ ≤ k := (h b).2`. Establish `hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b`. Introduce `u`. Rewrite using `[Finset.sum_comp]`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `b _`. Rewrite using `[nsmul_eq_mul]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)`. Use `_ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]`.

Use `_ ≤ k * ∑' b, g b := mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)`. Establish `hsum : Summable (fun a => g (π a))` using `summable_of_sum_le (fun a => hg (π a)) hbound`. Conclude with `⟨hsum, hsum.tsum_le_of_sum_le hbound⟩`.
-/
theorem summable_comp_of_bounded_fibres :
    ∀ (A B : Type) (π : A → B) (k : ℕ), (∀ b, Finite {a // π a = b} ∧ Nat.card {a // π a = b} ≤ k) → ∀ (g : B → ℝ), (∀ b, 0 ≤ g b) → Summable g → Summable (fun a => g (π a)) ∧ ∑' a, g (π a) ≤ k * ∑' b, g b := by
  intro A B π k h g hg hs
  classical
  have hcard : ∀ (u : Finset A) (b : B), (u.filter (fun a => π a = b)).card ≤ k := by
    intro u b
    have hf : ({a | π a = b} : Set A).Finite := Set.finite_coe_iff.mp (h b).1
    calc (u.filter (fun a => π a = b)).card
        = ((u.filter (fun a => π a = b) : Finset A) : Set A).ncard := (Set.ncard_coe_finset _).symm
      _ ≤ ({a | π a = b} : Set A).ncard := by
          apply Set.ncard_le_ncard _ hf
          intro a ha
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha
          exact ha.2
      _ = Nat.card {a // π a = b} := (Nat.card_coe_set_eq _).symm
      _ ≤ k := (h b).2
  have hbound : ∀ u : Finset A, ∑ a ∈ u, g (π a) ≤ k * ∑' b, g b := by
    intro u
    rw [Finset.sum_comp]
    calc ∑ b ∈ u.image π, (u.filter (fun a => π a = b)).card • g b
        ≤ ∑ b ∈ u.image π, (k : ℝ) * g b := by
          apply Finset.sum_le_sum
          intro b _
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard u b) (hg b)
      _ = k * ∑ b ∈ u.image π, g b := by rw [Finset.mul_sum]
      _ ≤ k * ∑' b, g b :=
          mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ (fun b _ => hg b)) (Nat.cast_nonneg k)
  have hsum : Summable (fun a => g (π a)) := summable_of_sum_le (fun a => hg (π a)) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.SumFibre
