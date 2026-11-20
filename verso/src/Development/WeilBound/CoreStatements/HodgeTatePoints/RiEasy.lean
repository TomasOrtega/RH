import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.DualLattices.ImportsAlt

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

noncomputable section

namespace PositivityTheory.HtPt.Ri

section
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C]

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
lemma mem_pInt (p : ℕ) (z : C) : z ∈ pInt (C := C) R p ↔ ∃ r : R, algebraMap R C (r * p) = z := by
  unfold GlobalTheory.CompanionTheory.Ar.GR.pInt
  rw [Submodule.mem_span_singleton]
  simp only [Algebra.smul_def, map_mul, map_natCast]

/- English proof (translation)
Extract witnesses or component facts from the available result. A detailed English derivation is pending.
-/
lemma alg_mem_pInt (p : ℕ) {r : R} (h : r ∈ Ideal.span {(p : R)}) :
    algebraMap R C r ∈ pInt (C := C) R p := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 h
  exact (PositivityTheory.HtPt.Ri.mem_pInt p _).2 ⟨a, rfl⟩

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
lemma add_zero_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) : g 0 ∈ pInt (C := C) R p := by
  have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
    from hg) 0 0
  rw [add_zero, sub_self, zero_sub] at h
  simpa using Submodule.neg_mem _ h

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Apply an available result and prove the equalities needed to match it to the conclusion. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma add_nsmul_mem {p : ℕ} {N : Type} [AddCommGroup N] {g : N → C}
    (hg : g ∈ addFun (C := C) R p N) (y : N) (n : ℕ) :
    g (n • y) - n * g y ∈ pInt (C := C) R p := by
  induction n with
  | zero => simpa using PositivityTheory.HtPt.Ri.add_zero_mem hg
  | succ n ih =>
    have h := (show ∀ x y : N, g (x + y) - g x - g y ∈ GlobalTheory.CompanionTheory.Ar.GR.pInt (C := C) R p
      from hg) (n • y) y
    have hsum := Submodule.add_mem _ h ih
    rw [succ_nsmul]
    convert hsum using 1
    push_cast
    ring

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Take a linear combination of the given relations to obtain the conclusion.
-/
lemma val_add_mem (p : ℕ) [NeZero p] (a b : ZMod p) :
    (((a + b).val : R) - (a.val : R) - (b.val : R)) ∈ Ideal.span {(p : R)} := by
  rw [Ideal.mem_span_singleton']
  refine ⟨-(((a.val + b.val) / p : ℕ) : R), ?_⟩
  have h := Nat.mod_add_div (a.val + b.val) p
  have h' : (((a.val + b.val) % p : ℕ) : R) + (p : R) * (((a.val + b.val) / p : ℕ) : R)
      = (a.val : R) + b.val := by
    rw [← Nat.cast_mul, ← Nat.cast_add, ← Nat.cast_add, h]
  rw [ZMod.val_add]
  linear_combination -h'

end

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem card_addChar (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (N : Type)
    [AddCommGroup N] [Fintype N] : Nat.card (AddChar N C) = Fintype.card N := by
  have hne : Monoid.exponent (Multiplicative N) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  haveI : NeZero (Monoid.exponent (Multiplicative N)) := ⟨hne⟩
  haveI : NeZero (Monoid.exponent (Multiplicative N) : C) := ⟨Nat.cast_ne_zero.2 hne⟩
  rw [Nat.card_congr (AddChar.toMonoidHomEquiv.trans MonoidHom.toHomUnitsMulEquiv.toEquiv),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity, Nat.card_congr Multiplicative.toAdd,
    Nat.card_eq_fintype_card]

end PositivityTheory.HtPt.Ri
