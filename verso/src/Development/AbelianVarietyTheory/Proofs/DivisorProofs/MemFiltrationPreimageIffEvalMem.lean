import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.MultiplicationKernelIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAddValuationIntegerRingNormalizedIff
open scoped NNReal
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HerbrandBridge

namespace GlobalTheory.FilPreMem

/- English proof (translation)
Proceed by induction on `f using Polynomial.induction_on with`. Consider the case `C c`. Introduce `y hy`. Use `F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `s i`. Simplify using `only [Polynomial.eval_C]`. Both sides reduce to the same expression. Consider the case `add p q hp hq`. Introduce `y hy`.

Use `F.add_mem (hp y hy) (hq y hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s i`. Simplify using `only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]`. Consider the case `monomial n c h`.

Introduce `y hy`. Use `hF _ (h y hy)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s i`. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul, Subring.coe_pow, pow_succ, liftA]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem poly_mem (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ))
    (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S]
    (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C))
    (hF : ∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) (f : Polynomial (Int0 v)) :
    ∀ y ∈ F, (fun s i => ((f.eval (liftA hv a s) : Int0 v) : C) * y s i) ∈ F := by
  induction f using Polynomial.induction_on with
  | C c =>
    intro y hy
    have := F.smul_mem (⟨(c : C), (hv _).1 c.2⟩ : w.valuationSubring) hy
    convert this using 1
    funext s i
    simp only [Polynomial.eval_C]
    rfl
  | add p q hp hq =>
    intro y hy
    have := F.add_mem (hp y hy) (hq y hy)
    convert this using 1
    funext s i
    simp only [Polynomial.eval_add, Subring.coe_add, Pi.add_apply, add_mul]
  | monomial n c h =>
    intro y hy
    have := hF _ (h y hy)
    convert this using 1
    funext s i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif, Pi.smul_apply, smul_eq_mul, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Subring.coe_mul,
      Subring.coe_pow, pow_succ, liftA]
    ring

/- English proof (translation)
Introduce `C _ w v hv S _ _ a N F hF x`. Set `T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a))` to `{ carrier := {x | evalVec (liftA hv a) N x ∈ F} zero_mem' := by show evalVec (liftA hv a) N 0 ∈ F`. Establish `: evalVec (liftA hv a) N 0 = 0`. Use function extensionality and compare the values at `s i`. Simplify using `[evalVec]`.

Rewrite using `[this]`. Conclude with `F.zero_mem`. Use the proof step `add_mem' := by`. Introduce `x y hx hy`. Use `show evalVec (liftA hv a) N (x + y) ∈ F`.

Rewrite using `[evalVec_add]`. Conclude with `F.add_mem hx hy`. Use the proof step `smul_mem' := by`. Introduce `r x hx`. Use `show evalVec (liftA hv a) N (r • x) ∈ F`.

Proceed by induction on `r using AdjoinRoot.induction_on with`. Consider the case `ih f`. Use `poly_mem C w v hv S a N F hF f _ hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s i`.

Simplify using `[evalVec, ev] }`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `: filPre (liftA hv a) F ≤ T` using `Submodule.span_le.2 (fun y hy => hy)`. Conclude with `this hx`.

Introduce `hx`. Conclude with `Submodule.subset_span hx`.
-/
theorem filPre_mem_iff : ∀ (C : Type) [Field C] (w : Valuation C ℝ≥0) (v : AddValuation C (WithTop ℝ)) (hv : ∀ x, x ∈ Int0 v ↔ x ∈ w.valuationSubring) (S : Type) [Fintype S] [DecidableEq S] (a : S → w.valuationSubring) (N : ℕ) (F : Submodule w.valuationSubring (S → Fin N → C)), (∀ x ∈ F, GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference.unif a x ∈ F) → ∀ x, x ∈ filPre (liftA hv a) F ↔ evalVec (liftA hv a) N x ∈ F := by
  intro C _ w v hv S _ _ a N F hF x
  let T : Submodule (RS (liftA hv a)) (Fin N → RS (liftA hv a)) :=
    { carrier := {x | evalVec (liftA hv a) N x ∈ F}
      zero_mem' := by
        show evalVec (liftA hv a) N 0 ∈ F
        have : evalVec (liftA hv a) N 0 = 0 := by
          funext s i; simp [evalVec]
        rw [this]; exact F.zero_mem
      add_mem' := by
        intro x y hx hy
        show evalVec (liftA hv a) N (x + y) ∈ F
        rw [evalVec_add]; exact F.add_mem hx hy
      smul_mem' := by
        intro r x hx
        show evalVec (liftA hv a) N (r • x) ∈ F
        induction r using AdjoinRoot.induction_on with
        | ih f =>
          have := poly_mem C w v hv S a N F hF f _ hx
          convert this using 1
          funext s i
          simp [evalVec, ev] }
  constructor
  · intro hx
    have : filPre (liftA hv a) F ≤ T := Submodule.span_le.2 (fun y hy => hy)
    exact this hx
  · intro hx
    exact Submodule.subset_span hx

end GlobalTheory.FilPreMem
