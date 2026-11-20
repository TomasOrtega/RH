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
The claim follows from `dif_pos (hc _ Δ.isCusp_first)`.
-/
theorem segDual_eq (Δ : Segment k) : segDual Δ =
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) ((hc _ Δ.isCusp_first).nu _) Δ.len Δ.len_pos :=
  dif_pos (hc _ Δ.isCusp_first)

/- English proof (translation)
Rewrite using `[segDual_eq hc]`. Both sides reduce to the same expression.
-/
theorem first_segDual (Δ : Segment k) : (segDual Δ).first = (dualCl Δ.first).nu (1 - (Δ.len : ℂ)) := by
  rw [segDual_eq hc]; rfl

/- English proof (translation)
Rewrite using `[segDual_eq hc]`. Both sides reduce to the same expression.
-/
theorem len_segDual (Δ : Segment k) : (segDual Δ).len = Δ.len := by
  rw [segDual_eq hc]; rfl

variable (hn : ∀ (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s))

include hn

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [Set.mem_image, Segment.mem_carrier, first_segDual hc, len_segDual hc, IrrGL.nu_nu]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, rfl⟩`. Use `⟨_, ⟨Δ.len - 1 - a, by omega, rfl⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hn]`. Use `congr 1`. Establish `h1 : a + 1 ≤ Δ.len` using `ha`. Establish `h2 : ((Δ.len - 1 - a : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - a`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨_, ⟨b, hb, rfl⟩, rfl⟩`.

Use `⟨Δ.len - 1 - b, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hn]`. Use `congr 1`. Establish `h1 : b + 1 ≤ Δ.len` using `hb`. Establish `h2 : ((Δ.len - 1 - b : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - b`.

Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h2]`. Expand and normalize the polynomial expressions, which then agree.
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
The claim follows from `Function.LeftInverse.injective hd`.
-/
theorem dualCl_injective : Function.Injective (dualCl : IrrGL k → IrrGL k) :=
  Function.LeftInverse.injective hd

/- English proof (translation)
Use `Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])` and prove the remaining obligations. Rewrite using `[first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]`. Simplify using the standard rewrite rules.
-/
theorem segDual_segDual (Δ : Segment k) : segDual (segDual Δ) = Δ := by
  refine Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])
  rw [first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]
  simp

/- English proof (translation)
Take `⟨⟨Γ, hΓ⟩, h1, h2⟩` from `h`. Establish `hi` using `dualCl_injective hc hn hd`. Use `⟨⟨segDual Γ, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[carrier_segDual hc hn, carrier_segDual hc hn, carrier_segDual hc hn, hΓ, Set.image_union]`. Rewrite using `[carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]`.

Conclude with `h1`. Rewrite using `[carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]`. Conclude with `h2`.
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
Take `⟨hl, j, hj, hf⟩` from `h`. Use `⟨linked_segDual hc hn hd hl.symm, ?_⟩` and prove the remaining obligations. Establish `hlen : Δ'.len < j + Δ.len`. Assume the negation of the conclusion as `hle`. Use `hl.2.2 fun x hx => ?_` and prove the remaining obligations.

Take `⟨a, ha, rfl⟩` from `Segment.mem_carrier.1 hx`. Use `Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[hf, IrrGL.nu_nu]`. Use `push_cast`. Both sides reduce to the same expression.

Use `⟨j + Δ.len - Δ'.len, by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[first_segDual hc, first_segDual hc, hf, hn, IrrGL.nu_nu, IrrGL.nu_nu]`. Use `congr 1`. Rewrite using `[Nat.cast_sub hlen.le]`. Use `push_cast`.

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
Use `⟨fun h => ?_, precedes_segDual hc hn hd⟩` and prove the remaining obligations. Use `precedes_segDual hc hn hd h` as an intermediate fact. Rewrite `this` using `[segDual_segDual hc hn hd, segDual_segDual hc hn hd]`. Then use the resulting hypothesis.
-/
theorem segDual_precedes_iff (Δ Δ' : Segment k) : (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  refine ⟨fun h => ?_, precedes_segDual hc hn hd⟩
  have := precedes_segDual hc hn hd h
  rwa [segDual_segDual hc hn hd, segDual_segDual hc hn hd] at this

end

/- English proof (translation)
Introduce `hA Δ Δ'` and use `segDual_precedes_iff (fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1) (GlobalTheory.T.dual_class_twist_neg hA) (GlobalTheory.T.dual_class_involutive hA) Δ Δ'`.
-/
theorem segDual_precedes : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k),
    (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := fun hA Δ Δ' =>
  segDual_precedes_iff (fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1) (GlobalTheory.T.dual_class_twist_neg hA) (GlobalTheory.T.dual_class_involutive hA) Δ Δ'

end GlobalTheory.CompanionTheory.SegDualPrec
