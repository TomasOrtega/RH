import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.EigenSubEval

variable {C : Type} [Field C] {w : Valuation C ℝ≥0} {v : AddValuation C (WithTop ℝ)}
  {S : Type} [Fintype S] [DecidableEq S]

/- English proof (translation)
Simplify using `only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]`.
-/
theorem evalVec_rsmul (b : S → Int0 v) (N : ℕ) (r : RS b) (z : Fin N → RS b) (s : S) (i : Fin N) :
    evalVec b N (r • z) s i = ((ev b s r : Int0 v) : C) * evalVec b N z s i := by
  simp only [evalVec, Pi.smul_apply, smul_eq_mul, map_mul, Subring.coe_mul]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_eigSub_iff (b : S → Int0 v) (N : ℕ) (τ : S) (z : Fin N → RS b) :
    z ∈ eigSub b τ (Fin N → RS b) ↔ lin b τ • z = 0 := Iff.rfl

/- English proof (translation)
Establish `hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t`. Introduce `s t`. Rewrite using `[ev_lin]`. Both sides reduce to the same expression. Establish `hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0`.

Introduce `s hs h`. Conclude with `hs (ha (Subtype.ext (sub_eq_zero.1 h)))`. Establish `hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W` using `fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔ (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl`. Rewrite using `[hmem]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨x, hx⟩` from `(hrange _).1 h`. Use `⟨x, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_eigSub_iff]`. Apply `hinj` to reduce the goal to its premises.

Use function extensionality and compare the values at `s i`. Rewrite using `[evalVec_rsmul, hev, hx]`. Establish `h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0`. Simplify using `[evalVec]`. Rewrite using `[h0]`.

Distinguish the cases in `e : s = τ`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Simplify using `[e]`. Rewrite using `[comp_coe, hx]`.

Simplify using the standard rewrite rules. Introduce and unpack `⟨z, hz, rfl⟩`. Rewrite `hz` using `[mem_eigSub_iff]`. Establish `key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ)`. Use function extensionality and compare the values at `s i`.

Distinguish the cases in `e : s = τ`. Substitute `e` using the available equality. Simplify using the standard rewrite rules. Establish `h1` using `congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i`. Rewrite `h1` using `[evalVec_rsmul, hev]`.

Establish `h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0`. Simplify using `[evalVec]`. Rewrite `h1` using `[h0]`. Rewrite using `[Pi.single_eq_of_ne e]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (hne s e)`.

Rewrite using `[comp_coe, ← key]`. Conclude with `(hrange _).2 ⟨z, rfl⟩`.
-/
theorem eigenSub_iff_eval (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (τ : S) (ha : Function.Injective a)
    (hinj : Function.Injective (evalVec (liftA hv a) N))
    (hrange : ∀ y, y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N ↔ ∃ x, evalVec (liftA hv a) N x = y)
    (y : Fin N → C) :
    y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C) (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      ∃ z ∈ eigSub (liftA hv a) τ (Fin N → RS (liftA hv a)),
        (fun i => ((comp (liftA hv a) N τ z i : Int0 v) : C)) = y := by
  have hev : ∀ s t, ((ev (liftA hv a) s (lin (liftA hv a) t) : Int0 v) : C) = (a s : C) - a t := by
    intro s t
    rw [ev_lin]; rfl
  have hne : ∀ s, s ≠ τ → (a s : C) - a τ ≠ 0 := by
    intro s hs h
    exact hs (ha (Subtype.ext (sub_eq_zero.1 h)))
  have hmem : y ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.eigenSub (W := fun _ => Fin N → C)
      (GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N) τ ↔
      (Pi.single τ y : S → Fin N → C) ∈ GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.freeLattice a N := Iff.rfl
  rw [hmem]
  constructor
  · intro h
    obtain ⟨x, hx⟩ := (hrange _).1 h
    refine ⟨x, ?_, ?_⟩
    · rw [mem_eigSub_iff]
      apply hinj
      funext s i
      rw [evalVec_rsmul, hev, hx]
      have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
        simp [evalVec]
      rw [h0]
      by_cases e : s = τ
      · subst e; simp
      · simp [e]
    · rw [comp_coe, hx]; simp
  · rintro ⟨z, hz, rfl⟩
    rw [mem_eigSub_iff] at hz
    have key : evalVec (liftA hv a) N z = Pi.single τ (evalVec (liftA hv a) N z τ) := by
      funext s i
      by_cases e : s = τ
      · subst e; simp
      · have h1 := congrFun (congrFun (congrArg (evalVec (liftA hv a) N) hz) s) i
        rw [evalVec_rsmul, hev] at h1
        have h0 : evalVec (liftA hv a) N (0 : Fin N → RS (liftA hv a)) s i = 0 := by
          simp [evalVec]
        rw [h0] at h1
        rw [Pi.single_eq_of_ne e]
        exact (mul_eq_zero.1 h1).resolve_left (hne s e)
    rw [comp_coe, ← key]
    exact (hrange _).2 ⟨z, rfl⟩

end GlobalTheory.EigenSubEval
