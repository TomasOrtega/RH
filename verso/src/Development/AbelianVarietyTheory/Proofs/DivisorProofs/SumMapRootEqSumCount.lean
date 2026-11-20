import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons p l ih`. Rewrite using `[List.map_cons, List.sum_cons, ih]`. Simplify using `only [List.count_cons, Nat.cast_add, add_smul, Finset.sum_add_distrib]`.

Rewrite using `[add_comm]`. Use `congr 1`. Take `⟨x, y⟩` from `p`. Simplify using `only [beq_iff_eq, Prod.mk.injEq]`. Rewrite using `[Finset.sum_eq_single x]`.

Rewrite using `[Finset.sum_eq_single y]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Ne.symm hb]`. Simplify using the standard rewrite rules.

Introduce `a _ ha`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `b _`. Simplify using `[Ne.symm ha]`. Simplify using the standard rewrite rules.
-/
theorem sum_map_root_eq_sum_count {n : ℕ} (l : List (Fin n × Fin n)) :
    (l.map fun p : Fin n × Fin n => root p.1 p.2).sum
      = ∑ a, ∑ b, (l.count (a, b) : ℝ) • root a b := by
  induction l with
  | nil => simp
  | cons p l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.count_cons, Nat.cast_add, add_smul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    obtain ⟨x, y⟩ := p
    simp only [beq_iff_eq, Prod.mk.injEq]
    rw [Finset.sum_eq_single x]
    · rw [Finset.sum_eq_single y]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    · intro a _ ha; apply Finset.sum_eq_zero; intro b _; simp [Ne.symm ha]
    · simp

/- English proof (translation)
Introduce `n ε μ Λ l hl hsum`. Use `⟨fun a b => l.count (b, a), ?_, ?_⟩` and prove the remaining obligations. Introduce `a b h`. Establish `hm : (b, a) ∈ l` using `List.count_pos_iff.mp (Nat.pos_of_ne_zero h)`. Conclude with `⟨(hl _ hm).2, (hl _ hm).1⟩`.

Rewrite `hsum` using `[sum_map_root_eq_sum_count]`. Establish `key : ∑ a, ∑ b, ((l.count (b, a) : ℕ) : ℝ) • root a b = - ∑ a, ∑ b, ((l.count (a, b) : ℕ) : ℝ) • root a b`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations.

Establish `: root b a = - root a b`. Unfold `root`. Normalize the expressions using the abelian group laws. Rewrite using `[this, smul_neg]`. Rewrite using `[key, ← hsum]`.

Normalize the expressions using the abelian group laws.
-/
theorem root_word_count_letters : ∀ (n : ℕ) (ε : Fin n → Bool) (μ Λ : Fin n → ℝ) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = false ∧ ε p.2 = true) → μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ → ∃ c : Fin n → Fin n → ℕ, (∀ a b, c a b ≠ 0 → ε a = true ∧ ε b = false) ∧ μ = Λ + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
  intro n ε μ Λ l hl hsum
  refine ⟨fun a b => l.count (b, a), ?_, ?_⟩
  · intro a b h
    have hm : (b, a) ∈ l := List.count_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨(hl _ hm).2, (hl _ hm).1⟩
  · rw [sum_map_root_eq_sum_count] at hsum
    have key : ∑ a, ∑ b, ((l.count (b, a) : ℕ) : ℝ) • root a b
        = - ∑ a, ∑ b, ((l.count (a, b) : ℕ) : ℝ) • root a b := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have : root b a = - root a b := by
        unfold root; abel
      rw [this, smul_neg]
    rw [key, ← hsum]; abel

end GlobalTheory
