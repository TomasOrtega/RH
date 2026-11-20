import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.ExistsComplOfAdmissible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.SumOfOfFn
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FZfirst

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

/- English proof (translation)
Establish `hn : l * 1 = n` using `h.deg_eq`. Rewrite `hn` using `[mul_one]`. Substitute `hn hc` using the available equality. Take `⟨φ⟩` from `IsZSeg.equiv_detRep h`. Conclude with `h.of_equiv φ.symm`.
-/
private theorem isZSeg_detRep {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {V : Type} [AddCommGroup V] [Module ℂ V] {n l : ℕ} {χ ψ : kˣ →* ℂˣ}
    {hχ : IsSmoothChar χ} {hl : 0 < l} {π : Representation ℂ (GL (Fin n) k) V}
    (h : IsZSeg (Segment.ofChar χ hχ l hl) π) (hc : χ * absPow k (((l : ℂ) - 1) / 2) = ψ) :
    IsZSeg (Segment.ofChar χ hχ l hl) (detRep (Fin l) ψ) := by
  have hn : l * 1 = n := h.deg_eq
  rw [mul_one] at hn
  subst hn hc
  obtain ⟨φ⟩ := IsZSeg.equiv_detRep h
  exact h.of_equiv φ.symm

/- English proof (translation)
Introduce `hG hBZ hZ k _ _ _ _ r t V _ _ σ χ s₁ i₁ u₁ hχ hu`. Establish `s₂ : IsSmooth (detRep (Fin t) χ)` using `(isSmooth_ofChar_iff _).2 hχ.detChar`. Establish `i₂ : (detRep (Fin t) χ).IsIrreducible` using `isIrreducible_ofChar _`. Establish `u₂ : IsUnitarisable (detRep (Fin t) χ)` using `(isUnitarisable_ofChar_iff _).2 fun _ => hu _`. Establish `hd : ∑ a, (![IrrGL.of σ s₁ i₁, IrrGL.of (detRep (Fin t) χ) s₂ i₂] a).1 = r + t` using `Fin.sum_univ_two _`.

Take `⟨φ⟩` from `nonempty_prod₂_equiv_prodIrr σ s₁ i₁ (detRep (Fin t) χ) s₂ i₂ hd`. Establish `φ₁` using `IrrGL.equivOf σ s₁ i₁`. Establish `φ₂` using `IrrGL.equivOf (detRep (Fin t) χ) s₂ i₂`. Establish `v₁` using `GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₁ u₁`. Establish `v₂` using `GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₂ u₂`.

Use `GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm ?_` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos t with rfl | ht` into its components or cases. Use `UpperTheory.Lit.Mix.ss hBZ k _ _ _ hd v₁ v₂ (UpperTheory.Lit.Mix.cellone hG hBZ k _ _ _ hd fun q hq h0 _ _ _ => ?_)` and prove the remaining obligations. Establish `h1 : (q 0).1 + (q 1).1 = 0` using `(Fin.sum_univ_two fun a => (q a).1).symm.trans hq`. Use linear arithmetic over natural numbers and integers.

Establish `hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2))` using `hχ.mul (isSmoothChar_absPow _)`. Establish `hc : χ * absPow k (-((t : ℂ) - 1) / 2) * absPow k (((t : ℂ) - 1) / 2) = χ`. Rewrite using `[mul_assoc, ← absPow_add, show -((t : ℂ) - 1) / 2 + ((t : ℂ) - 1) / 2 = 0 by ring, absPow_zero, mul_one]`. Take `⟨z, hz⟩` from `(UpperTheory.Lit.Full.zfirst hG hBZ hZ k (Segment.ofChar _ hχ' t ht)).1`. Conclude with `UpperTheory.Lit.Full.topZ hG hBZ hZ k _ _ _ _ hd v₁ v₂ ((isZSeg_detRep hz hc).of_equiv φ₂)`.
-/
theorem UpperTheory.Lit.Full.top :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.ZelevinskyPolynomialRing → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ), IsSmooth σ → σ.IsIrreducible → IsUnitarisable σ → IsSmoothChar χ → IsUnitaryChar χ → (prod₂ σ (detRep (Fin t) χ)).IsIrreducible := by
  intro hG hBZ hZ k _ _ _ _ r t V _ _ σ χ s₁ i₁ u₁ hχ hu
  have s₂ : IsSmooth (detRep (Fin t) χ) := (isSmooth_ofChar_iff _).2 hχ.detChar
  have i₂ : (detRep (Fin t) χ).IsIrreducible := isIrreducible_ofChar _
  have u₂ : IsUnitarisable (detRep (Fin t) χ) := (isUnitarisable_ofChar_iff _).2 fun _ => hu _
  have hd : ∑ a, (![IrrGL.of σ s₁ i₁, IrrGL.of (detRep (Fin t) χ) s₂ i₂] a).1 = r + t := Fin.sum_univ_two _
  obtain ⟨φ⟩ := nonempty_prod₂_equiv_prodIrr σ s₁ i₁ (detRep (Fin t) χ) s₂ i₂ hd
  have φ₁ := IrrGL.equivOf σ s₁ i₁
  have φ₂ := IrrGL.equivOf (detRep (Fin t) χ) s₂ i₂
  have v₁ := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₁ u₁
  have v₂ := GlobalTheory.GenericUnitary.isUnitarisable_of_equiv φ₂ u₂
  refine GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · refine UpperTheory.Lit.Mix.ss hBZ k _ _ _ hd v₁ v₂
      (UpperTheory.Lit.Mix.cellone hG hBZ k _ _ _ hd fun q hq h0 _ _ _ => ?_)
    have h1 : (q 0).1 + (q 1).1 = 0 := (Fin.sum_univ_two fun a => (q a).1).symm.trans hq
    omega
  · have hχ' : IsSmoothChar (χ * absPow k (-((t : ℂ) - 1) / 2)) := hχ.mul (isSmoothChar_absPow _)
    have hc : χ * absPow k (-((t : ℂ) - 1) / 2) * absPow k (((t : ℂ) - 1) / 2) = χ := by
      rw [mul_assoc, ← absPow_add, show -((t : ℂ) - 1) / 2 + ((t : ℂ) - 1) / 2 = 0 by ring, absPow_zero, mul_one]
    obtain ⟨z, hz⟩ := (UpperTheory.Lit.Full.zfirst hG hBZ hZ k (Segment.ofChar _ hχ' t ht)).1
    exact UpperTheory.Lit.Full.topZ hG hBZ hZ k _ _ _ _ hd v₁ v₂ ((isZSeg_detRep hz hc).of_equiv φ₂)
