import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassInvolutiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.SegDualPrec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section

variable (hc : ∀ x : IrrGL k, x.IsCusp → (dualCl x).IsCusp)

include hc

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segDual_eq (Δ : Segment k) : segDual Δ =
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) ((hc _ Δ.isCusp_first).nu _) Δ.len Δ.len_pos :=
  dif_pos (hc _ Δ.isCusp_first)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem first_segDual (Δ : Segment k) : (segDual Δ).first = (dualCl Δ.first).nu (1 - (Δ.len : ℂ)) := by
  rw [segDual_eq hc]; rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem len_segDual (Δ : Segment k) : (segDual Δ).len = Δ.len := by
  rw [segDual_eq hc]; rfl

variable (hn : ∀ (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s))

include hn

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Expand and normalize the polynomial expressions, which then agree. Rewrite the conclusion using the stated equalities. Expand and normalize the polynomial expressions, which then agree.
-/
theorem carrier_segDual (Δ : Segment k) : (segDual Δ).carrier = dualCl '' Δ.carrier := by
  ext x
  simp only [Set.mem_image, Segment.mem_carrier, first_segDual hc, len_segDual hc, IrrGL.nu_nu]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨_, ⟨Δ.len - 1 - a, by omega, rfl⟩, ?_⟩
    rw [hn]
    congr 1
    have h1 : a + 1 ≤ Δ.len := ha
    have h2 : ((Δ.len - 1 - a : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - a := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨Δ.len - 1 - b, by omega, ?_⟩
    rw [hn]
    congr 1
    have h1 : b + 1 ≤ Δ.len := hb
    have h2 : ((Δ.len - 1 - b : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - b := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring

variable (hd : ∀ x : IrrGL k, dualCl (dualCl x) = x)

include hd

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualCl_injective : Function.Injective (dualCl : IrrGL k → IrrGL k) :=
  Function.LeftInverse.injective hd

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem segDual_segDual (Δ : Segment k) : segDual (segDual Δ) = Δ := by
  refine Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])
  rw [first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem linked_segDual {Δ Δ' : Segment k} (h : Δ.Linked Δ') : (segDual Δ).Linked (segDual Δ') := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hi := dualCl_injective hc hn hd
  refine ⟨⟨segDual Γ, ?_⟩, ?_, ?_⟩
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, carrier_segDual hc hn, hΓ, Set.image_union]
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h1
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h2

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations. Both sides reduce to the same expression.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Move the embeddings inside the algebraic operations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem precedes_segDual {Δ Δ' : Segment k} (h : Δ'.Precedes Δ) : (segDual Δ).Precedes (segDual Δ') := by
  obtain ⟨hl, j, hj, hf⟩ := h
  refine ⟨linked_segDual hc hn hd hl.symm, ?_⟩
  have hlen : Δ'.len < j + Δ.len := by
    by_contra hle
    refine hl.2.2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
    rw [hf, IrrGL.nu_nu]
    push_cast
    rfl
  refine ⟨j + Δ.len - Δ'.len, by omega, ?_⟩
  rw [first_segDual hc, first_segDual hc, hf, hn, IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  rw [Nat.cast_sub hlen.le]
  push_cast
  ring

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.
-/
theorem segDual_precedes_iff (Δ Δ' : Segment k) : (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  refine ⟨fun h => ?_, precedes_segDual hc hn hd⟩
  have := precedes_segDual hc hn hd h
  rwa [segDual_segDual hc hn hd, segDual_segDual hc hn hd] at this

end

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem segDual_precedes : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k),
    (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := fun hA Δ Δ' =>
  segDual_precedes_iff (fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1) (GlobalTheory.T.dual_class_twist_neg hA) (GlobalTheory.T.dual_class_involutive hA) Δ Δ'

end GlobalTheory.CompanionTheory.SegDualPrec
