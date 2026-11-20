import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColGeR
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PatternGroupStatement

open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep

/- English proof (translation)
Use `⟨fun i h => lt_irrefl _ h.1, ?_⟩` and prove the remaining obligations. Introduce `a b c hab hbc`. Conclude with `⟨hab.1.trans hbc.1, hbc.2⟩`.
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
Prove the components needed by the constructor for the conclusion. Introduce and unpack `(a | a) (b | b) h`. Establish `h1` using `congrArg (fun x => (x.1.1 : Fin d).1) h`. Simplify using `only [colGeSplit] at h1`. Conclude with `congrArg Sum.inl (Fin.ext h1)`.

Establish `h1` using `congrArg (fun x => (x.1.2 : Fin d).1) h`. Simplify using `only [colGeSplit] at h1`. Use `b.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (fun x => (x.1.2 : Fin d).1) h`.

Simplify using `only [colGeSplit] at h1`. Use `a.2.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h1` using `congrArg (fun x => x.1) h`. Simplify using `only [colGeSplit] at h1`.

Conclude with `congrArg Sum.inr (Subtype.ext h1)`. Introduce and unpack `⟨⟨i, l⟩, hil, hjl⟩`. Distinguish the cases in `e : (l : ℕ) = j`. Establish `hi : (i : ℕ) < j`. Establish `: (i : ℕ) < l` using `hil`.

Use linear arithmetic over natural numbers and integers. Use `⟨Sum.inl ⟨i, hi⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [colGeSplit]`. Conclude with `Prod.ext rfl (Fin.ext e.symm)`.

Establish `hl : j + 1 ≤ (l : ℕ)`. Establish `: j ≤ (l : ℕ)` using `hjl`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨Sum.inr ⟨(i, l), hil, hl⟩, rfl⟩`.
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
Rewrite using `[← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum, Nat.card_eq_fintype_card, Fintype.card_fin]`.
-/
theorem natCard_colGe (d j : ℕ) (hj : j < d) :
    Nat.card {p : Fin d × Fin d // colGe d j p.1 p.2} =
      j + Nat.card {p : Fin d × Fin d // colGe d (j + 1) p.1 p.2} := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (colGeSplit_bijective d j hj)), Nat.card_sum,
    Nat.card_eq_fintype_card, Fintype.card_fin]

/- English proof (translation)
Rewrite using `[GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d j), GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d (j + 1)), natCard_colGe d j hj, pow_add]`.
-/
theorem ncard_patSet_colGe (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (hj : j < d) :
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard := by
  rw [GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d j), GlobalTheory.CompanionTheory.PatGrp.card_patSet (isPat_colGe d (j + 1)),
    natCard_colGe d j hj, pow_add]

end GlobalTheory.CompanionTheory.TyFin.ColStep
