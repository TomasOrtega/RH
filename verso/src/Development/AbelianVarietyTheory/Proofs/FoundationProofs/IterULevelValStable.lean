import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetIPSmulRight
import Development.AbelianVarietyTheory.Definitions.Foundations.RepL
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoeffHeckeUOperatorLowersLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsModularFormCoeffSeqHeckeUAndDepletionStatement
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

/- English proof (translation)
Unfold `ch`. Establish `: ((L : ℤ) : ZMod N) = 0`. Rewrite using `[Int.cast_natCast]`. Conclude with `(ZMod.natCast_eq_zero_iff L N).2 h`. Rewrite using `[Int.cast_add, this, add_zero]`.
-/
lemma ch_periodic_of_dvd {N L : ℕ} (ε : DirichletCharacter ℂ N) (h : N ∣ L) (d : ℤ) :
    ch ε (d + L) = ch ε d := by
  unfold ch
  have : ((L : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff L N).2 h
  rw [Int.cast_add, this, add_zero]

/- English proof (translation)
Introduce `k N l m ε t α B c a hk hl hα ha`. Establish `lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro a ha`.

Simplify using `using ha`. Consider the case `succ m ih`. Introduce `a ha`. Establish `hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a)`. Use `GlobalTheory.T.coeffHeckeUOperator_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_` and prove the remaining obligations.

Conclude with `Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N`. Conclude with `ch_periodic_of_dvd ε (Dvd.intro _ rfl)`. Simplify `ha` using `[pow_succ, mul_assoc]`. Rewrite using `[Function.iterate_succ_apply]`. Conclude with `ih _ hU`.

Establish `hb` using `lev m a ha`. Use `⟨hb, fun hE r hr => ?_⟩` and prove the remaining obligations. Establish `per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d` using `ch_periodic_of_dvd ε (Dvd.intro _ rfl)`. Establish `mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a))`. Introduce `j`.

Proceed by induction on `j with`. Consider the case `zero => simpa using hb`. Consider the case `succ j ih`. Rewrite using `[Function.iterate_succ_apply']`. Conclude with `(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1`.

Establish `lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a)`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Rewrite using `[Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨j, rfl⟩` from `Nat.exists_eq_add_of_le hr`. Unfold `val`. Rewrite using `[add_comm m j, Function.iterate_add_apply, lamj, pow_add]`.

Establish `hj : α ^ j ≠ 0` using `pow_ne_zero _ hα`. Clear the denominators using the available nonvanishing facts.
-/
theorem iterU_level_val_stable : ∀ (k N l m : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c a : ℕ → ℂ),
    1 ≤ k → l.Prime → α ≠ 0 → MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) ∧
      (EigF k N l ε t α B c → ∀ r, m ≤ r → val B c l α r a = val B c l α m a) := by
  intro k N l m ε t α B c a hk hl hα ha
  have lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) := by
    intro m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a) := by
        refine GlobalTheory.T.coeffHeckeUOperator_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_
        · exact Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N
        · exact ch_periodic_of_dvd ε (Dvd.intro _ rfl)
        · simpa [pow_succ, mul_assoc] using ha
      rw [Function.iterate_succ_apply]
      exact ih _ hU
  have hb := lev m a ha
  refine ⟨hb, fun hE r hr => ?_⟩
  have per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d := ch_periodic_of_dvd ε (Dvd.intro _ rfl)
  have mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a)) := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1
  have lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]
      ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold val
  rw [add_comm m j, Function.iterate_add_apply, lamj, pow_add]
  have hj : α ^ j ≠ 0 := pow_ne_zero _ hα
  field_simp

end GlobalTheory
