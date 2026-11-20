import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppInd
open Classical

namespace GlobalTheory.LevelVecNorm

/- English proof (translation)
Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem finsum_indicator_one_eq_ncard' {α : Type} (s : Set α) :
    (∑ᶠ x, s.indicator (fun _ => (1:ℝ)) x) = (s.ncard : ℝ) := by
  by_cases hs : s.Finite
  · rw [← finsum_mem_def, finsum_mem_eq_finite_toFinset_sum _ hs, Set.ncard_eq_toFinset_card s hs]
    simp
  · have hsupp : Function.support (s.indicator (fun _ => (1:ℝ))) = s := by
      ext x; by_cases hx : x ∈ s <;> simp [hx]
    rw [finsum_of_infinite_support (by rw [hsupp]; exact hs), Set.Infinite.ncard hs]
    simp

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Substitute using the available equality. Substitute using the available equality. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules.

Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components. Supply the required witnesses or components. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Evaluate the numerical expressions. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Evaluate the numerical expressions. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem suppInd_sq_sum_eq_card : ∀ {k : Type} [CommRing k] {b a : ℕ} (r t : ℕ), b = r + t → a = r → ∀ H : Subgroup (GL (Fin r) k),
    ∑ᶠ z : Matrix (Fin b) (Fin a) k, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = (Nat.card H : ℝ) := by
  intro k _ b a r t hb ha H
  subst hb; subst a
  let f : GL (Fin r) k → Matrix (Fin (r + t)) (Fin r) k := fun g i j =>
    if h : i.val < r then (g : Matrix (Fin r) (Fin r) k) ⟨i.val, h⟩ j else 0
  have htop : ∀ g, Formalism.IndefR.Datum.topL r (f g) = (g : Matrix (Fin r) (Fin r) k) := by
    intro g; ext i j
    simp [Formalism.IndefR.Datum.topL, f, i.isLt, j.isLt, show i.val < r + t by omega]
  have hlow : ∀ g, Formalism.IndefR.Datum.LowZero r (f g) := by
    intro g i j hi _
    simp [f, show ¬ i.val < r by omega]
  have hinj : Function.Injective f := by
    intro g g' h
    apply Units.ext
    rw [← htop g, ← htop g', h]
  let S : Set (Matrix (Fin (r + t)) (Fin r) k) :=
    {z | Formalism.IndefR.Datum.LowZero r z ∧ ∃ g ∈ H, ((g : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) = Formalism.IndefR.Datum.topL r z}
  have hS : S = f '' (H : Set (GL (Fin r) k)) := by
    ext z
    constructor
    · rintro ⟨hz, g, hg, hgz⟩
      refine ⟨g, hg, ?_⟩
      ext i j
      by_cases hi : i.val < r
      · have := congrFun (congrFun hgz ⟨i.val, hi⟩) j
        simp only [Formalism.IndefR.Datum.topL, j.isLt, show i.val < r + t by omega] at this
        simpa [f, hi] using this
      · simp [f, hi, hz i j (by omega) j.isLt]
    · rintro ⟨g, hg, rfl⟩
      exact ⟨hlow g, g, hg, (htop g).symm⟩
  have hfun : ∀ z, GlobalTheory.LevelVecNorm.suppInd r H z ^ 2 = S.indicator (fun _ => (1:ℝ)) z := by
    intro z
    unfold GlobalTheory.LevelVecNorm.suppInd
    by_cases hz : z ∈ S
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_pos hz', Set.indicator_of_mem hz]; norm_num
    · have hz' := hz
      simp only [S, Set.mem_ofPred_eq] at hz'
      rw [if_neg hz', Set.indicator_of_notMem hz]; norm_num
  simp_rw [hfun]
  rw [finsum_indicator_one_eq_ncard', hS, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq]
  rfl

end GlobalTheory.LevelVecNorm
