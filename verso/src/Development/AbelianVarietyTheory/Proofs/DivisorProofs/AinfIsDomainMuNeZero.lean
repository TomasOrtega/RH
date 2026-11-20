import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SandwichMaps
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ hv ε hprim`. Use `haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p`. Use `⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩` and prove the remaining obligations. Introduce `h`. Unfold `_root_.GlobalTheory.Sandwich.mu at h`.

Establish `h1 : WittVector.teichmuller p ε = 1` using `sub_eq_zero.mp h`. Establish `hε : ε = 1`. Use `congrArg (fun x => WittVector.coeff x 0) h1` as an intermediate fact. Simplify `this` using `[WittVector.teichmuller_coeff_zero]`. Establish `hroot : _root_.GlobalTheory.Sandwich.root ε = 1`.

Unfold `_root_.GlobalTheory.Sandwich.root`. Rewrite using `[hε, map_one]`. Rewrite `hprim` using `[hroot, map_one]`. Conclude with `(Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)`.
-/
theorem _root_.GlobalTheory.ainf_isDomain_and_mu_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p → IsDomain (_root_.GlobalTheory.Sandwich.Ainf p O) ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 := by
  intro p _ C _ _ _ v O _ _ _ _ hv ε hprim
  haveI : IsDomain (PreTilt O p) := PreTilt.isDomain C v O hv p
  refine ⟨by unfold _root_.GlobalTheory.Sandwich.Ainf; infer_instance, ?_⟩
  intro h
  unfold _root_.GlobalTheory.Sandwich.mu at h
  have h1 : WittVector.teichmuller p ε = 1 := sub_eq_zero.mp h
  have hε : ε = 1 := by
    have := congrArg (fun x => WittVector.coeff x 0) h1
    simpa [WittVector.teichmuller_coeff_zero] using this
  have hroot : _root_.GlobalTheory.Sandwich.root ε = 1 := by
    unfold _root_.GlobalTheory.Sandwich.root
    rw [hε, map_one]
  rw [hroot, map_one] at hprim
  exact (Fact.out : p.Prime).one_lt.ne' (IsPrimitiveRoot.one_left_iff.mp hprim)

end GlobalTheory
