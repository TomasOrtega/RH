import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components.
-/
theorem isPat_colGe (d j : ℕ) : IsPat (colGe d j) := by
  refine ⟨fun i h => lt_irrefl _ h.1, ?_⟩
  intro a b c hab hbc
  exact ⟨hab.1.trans hbc.1, hbc.2⟩

def colGeSplit (d j : ℕ) (hj : j < d) :
    Fin j ⊕ {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} →
      {p : Fin d × Fin d // colGe d j p.1 p.2}
  | Sum.inl i => ⟨(⟨i.1, i.2.trans hj⟩, ⟨j, hj⟩), by
      refine ⟨?_, le_refl _⟩
      exact Fin.mk_lt_mk.2 i.2⟩
  | Sum.inr p => ⟨p.1, p.2.1, Nat.le_of_succ_le p.2.2⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Simplify using the standard rewrite rules.

Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact. Simplify using the standard rewrite rules. Assume the hypotheses and unpack their components.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Use linear arithmetic over natural numbers and integers.

Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem colGeSplit_bijective (d j : ℕ) (hj : j < d) : Function.Bijective (colGeSplit d j hj) := by
  constructor
  · rintro (a | a) (b | b) h
    · have h1 := congrArg (fun x => (x.1.1 : Fin d).1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inl (Fin.ext h1)
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := b.2.2
      omega
    · have h1 := congrArg (fun x => (x.1.2 : Fin d).1) h
      simp only [colGeSplit] at h1
      have := a.2.2
      omega
    · have h1 := congrArg (fun x => x.1) h
      simp only [colGeSplit] at h1
      exact congrArg Sum.inr (Subtype.ext h1)
  · rintro ⟨⟨i, l⟩, hil, hjl⟩
    by_cases e : (l : ℕ) = j
    · have hi : (i : ℕ) < j := by
        have : (i : ℕ) < l := hil
        omega
      refine ⟨Sum.inl ⟨i, hi⟩, ?_⟩
      apply Subtype.ext
      simp only [colGeSplit]
      exact Prod.ext rfl (Fin.ext e.symm)
    · have hl : j + 1 ≤ (l : ℕ) := by
        have : j ≤ (l : ℕ) := hjl
        omega
      exact ⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem natCard_colGe (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  rw [GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d j), GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d (j + 1)),
    natCard_colGe d j hj, pow_add]

end GlobalTheory.CompanionTheory.TyFin.ColStep
