import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InjectiveWedgeHighestCoefficient
open GlobalTheory.CompanionTheory.PairMult

noncomputable section

open Finset
open CompanionTheory.D.LK (Pos)

namespace GlobalTheory.CompanionTheory.PairMult.TopCycQ

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem annq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    annq l x B = if l ∈ B then 0 else sgL l B • x (insert l B) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem creq_app (l : Lt n) (x : Cq n V) (B : Finset (Lt n)) :
    creq l x B = if l ∈ B then sgL l B • x (B.erase l) else 0 := rfl

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mem_omQ (lev : Fin n → ℕ) (l : Lt n) :
    l ∈ omQ lev ↔ l.1 = true ∧ lev l.2.1.1 < lev l.2.1.2 := by
  simp [omQ]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Separate the alternatives or extract the components of the hypothesis.

Establish an intermediate fact. Substitute using the available equality. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem insert_ne_omQ (lev : Fin n → ℕ) (s t : Bool) (i j k : Pos n)
    (ht : i.1.2 = j.1.1 ∧ k.1.1 = i.1.1 ∧ k.1.2 = j.1.2) (C : Finset (Lt n)) :
    insert (s, i) (insert (t, j) (C.erase ((s == t), k))) ≠ omQ lev := by
  intro e
  have hi := (mem_omQ lev _).1 (e ▸ mem_insert_self _ _)
  have hj := (mem_omQ lev _).1 (e ▸ mem_insert_of_mem (mem_insert_self _ _))
  obtain ⟨t1, t2, t3⟩ := ht
  have hs : s = true := hi.1
  have htt : t = true := hj.1
  subst hs htt
  have ck : ((true == true), k) ∈ omQ lev := (mem_omQ lev _).2
    ⟨rfl, by rw [t2, t3]; exact (hi.2.trans_eq (congrArg lev t1)).trans hj.2⟩
  rw [← e] at ck
  rcases mem_insert.1 ck with h | h
  · have hk : k = i := congrArg Prod.snd h
    subst hk
    have pj := j.2
    rw [← t1, t3] at pj
    exact lt_irrefl _ pj
  · rcases mem_insert.1 h with h | h
    · have hk : k = j := congrArg Prod.snd h
      subst hk
      have pi := i.2
      rw [← t2, t1] at pi
      exact lt_irrefl _ pi
    · exact notMem_erase _ _ h

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Both sides reduce to the same expression. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem topCyc : TopCyc := by
  intro n lev V _ _ E1 E2 _ v hv
  funext A
  simp only [bdq, LinearMap.add_apply, LinearMap.sum_apply, Pi.add_apply, Finset.sum_apply, Pi.zero_apply]
  rw [Finset.sum_eq_zero, Finset.sum_eq_zero, add_zero]
  · intro s _
    refine Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ =>
      Finset.sum_eq_zero fun k _ => ?_
    split_ifs with ht
    · rw [Module.End.mul_apply, Module.End.mul_apply, creq_app]
      split_ifs with hk
      · rw [annq_app]
        split_ifs with h1
        · exact smul_zero _
        · rw [annq_app]
          split_ifs with h2
          · simp
          · rw [topq, Pi.single_eq_of_ne (insert_ne_omQ lev s t i j k ht A), smul_zero, smul_zero, smul_zero]
      · rfl
    · rfl
  · intro l _
    show Tl E1 E2 l (annq l (topq lev v) A) = 0
    rw [annq_app]
    split_ifs with hl
    · exact map_zero _
    · by_cases e : insert l A = omQ lev
      · have hlK := (mem_omQ lev l).1 (e ▸ mem_insert_self l A)
        rw [topq, e, Pi.single_eq_same, map_smul, hv l hlK, smul_zero]
      · rw [topq, Pi.single_eq_of_ne e, smul_zero, map_zero]

end GlobalTheory.CompanionTheory.PairMult.TopCycQ
