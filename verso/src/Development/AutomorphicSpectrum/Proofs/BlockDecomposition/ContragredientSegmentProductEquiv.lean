import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContragredientProductIrreducible
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassCuspidal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNeg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

namespace GlobalTheory.CompanionTheory.SegIncDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Substitute `e` using the available equality. Take `rfl : x = y` from `funext fun a => by simpa using hxy a`. Conclude with `⟨hd, ⟨Representation.Equiv.refl _⟩⟩`.
-/
theorem exists_equiv_prodIrr_of_cast {h h' N : ℕ} (e : h = h') (x : Fin h → IrrGL k) (y : Fin h' → IrrGL k)
    (hxy : ∀ a, x a = y (Fin.cast e a)) (hd : ∑ a, (x a).1 = N) :
    ∃ hd' : ∑ a, (y a).1 = N, Nonempty ((prodIrr x hd).Equiv (prodIrr y hd')) := by
  subst e
  obtain rfl : x = y := funext fun a => by simpa using hxy a
  exact ⟨hd, ⟨Representation.Equiv.refl _⟩⟩

/- English proof (translation)
The claim follows from `H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩`.
-/
theorem nonempty_contra_trans {h h' N : ℕ} {x y : Fin h → IrrGL k} {z : Fin h' → IrrGL k} {hd : ∑ a, (x a).1 = N}
    {hy : ∑ a, (y a).1 = N} {hz : ∑ a, (z a).1 = N} (H₁ : Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr y hy)))
    (H₂ : Nonempty ((prodIrr y hy).Equiv (prodIrr z hz))) :
    Nonempty ((contra (prodIrr x hd)).Equiv (prodIrr z hz)) :=
  H₁.elim fun φ => H₂.elim fun ψ => ⟨φ.trans ψ⟩

/- English proof (translation)
Establish `hc : ∀ x : IrrGL k, x.IsCusp → (dualCl x).IsCusp` using `fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1`. Establish `hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1)`. Establish `h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a` using `rfl`. Rewrite using `[Fin.val_rev, h0]`. Use linear arithmetic over natural numbers and integers.

Establish `ha : (a : ℕ) + 1 ≤ Δ.len` using `a.2`. Express the relevant statement in the definitionally equal form `dualCl (Δ.first.nu ((a : ℕ) : ℂ)) = (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)`. Rewrite using `[GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem dualCl_term (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) (hl : Δ.len = (segDual Δ).len)
    (a : Fin Δ.len) : dualCl (Δ.term a) = dec (segDual Δ) (Fin.cast hl a) := by
  have hc : ∀ x : IrrGL k, x.IsCusp → (dualCl x).IsCusp := fun x hx =>
    (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1
  have hv : ((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) = Δ.len - (a + 1) := by
    have h0 : ((Fin.cast hl a : Fin (segDual Δ).len) : ℕ) = a := rfl
    rw [Fin.val_rev, h0]; omega
  have ha : (a : ℕ) + 1 ≤ Δ.len := a.2
  change dualCl (Δ.first.nu ((a : ℕ) : ℂ)) =
    (segDual Δ).first.nu (((Fin.rev (Fin.cast hl a) : Fin (segDual Δ).len) : ℕ) : ℂ)
  rw [GlobalTheory.CompanionTheory.ZcDual.dualCl_nu hA, GlobalTheory.CompanionTheory.SegDualPrec.first_segDual hc, IrrGL.nu_nu, hv, Nat.cast_sub ha]
  congr 1
  push_cast
  ring

/- English proof (translation)
Introduce `k _ _ _ _ hA Δ N hd`. Establish `hl : Δ.len = (segDual Δ).len` using `(GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm`. Establish `H` using `@GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd`. Take `⟨hd₁, H₁⟩` from `H`. Establish `H'` using `exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ)) (dualCl_term hA Δ hl) hd₁`.

Take `⟨hd₂, H₂⟩` from `H'`. Conclude with `⟨hd₂, nonempty_contra_trans H₁ H₂⟩`.
-/
theorem contra_prodIrr_term : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (Δ.term a).1 = N), ∃ hd' : ∑ a, (dec (segDual Δ) a).1 = N,
      Nonempty ((contra (prodIrr Δ.term hd)).Equiv (prodIrr (dec (segDual Δ)) hd')) := by
  intro k _ _ _ _ hA Δ N hd
  have hl : Δ.len = (segDual Δ).len :=
    (GlobalTheory.CompanionTheory.SegDualPrec.len_segDual (fun x hx => (GlobalTheory.CompanionTheory.DualCusp.dualCl_isCusp hA x hx).1) Δ).symm
  have H := @GlobalTheory.CompanionTheory.ContraProd.contra_prodIrr k _ _ _ _ hA Δ.len N Δ.term hd
  obtain ⟨hd₁, H₁⟩ := H
  have H' := exists_equiv_prodIrr_of_cast hl (fun a => dualCl (Δ.term a)) (dec (segDual Δ))
    (dualCl_term hA Δ hl) hd₁
  obtain ⟨hd₂, H₂⟩ := H'
  exact ⟨hd₂, nonempty_contra_trans H₁ H₂⟩

end GlobalTheory.CompanionTheory.SegIncDual

end
