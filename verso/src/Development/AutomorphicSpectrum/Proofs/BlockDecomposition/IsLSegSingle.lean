import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.SatakeSocle.SocleOne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.LocGL

/- English proof (translation)
Establish `hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL k) = fun _ => ρ`. Use function extensionality and compare the values at `a`. Establish `ha : (a : ℕ) = 0`. Establish `h1 : (a : ℕ) < 1` using `a.isLt`. Use linear arithmetic over natural numbers and integers.

Use `show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ`. Rewrite using `[ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos, IrrGL.nu_zero]`. Establish `key : ∀ x : Fin 1 → IrrGL k, x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1, IsCosocle ρ.rep (prodIrr x hd)`. Introduce `x hx hd`. Substitute `hx` using the available equality.

Take `⟨φ⟩` from `nonempty_equiv_prodIrr_one ρ hd`. Conclude with `(isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ`. Establish `hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1`. Rewrite using `[hterm]`. Simplify using the standard rewrite rules.

Conclude with `⟨hd, key _ hterm hd⟩`.
-/
theorem isLSeg_single (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (ρ : IrrGL k) (hρ : ρ.IsCusp) : IsLSeg (Segment.single ρ hρ) ρ.rep := by
  have hterm : ((Segment.single ρ hρ).term : Fin 1 → IrrGL k) = fun _ => ρ := by
    funext a
    have ha : (a : ℕ) = 0 := by
      have h1 : (a : ℕ) < 1 := a.isLt
      omega
    show (Segment.single ρ hρ).first.nu ((a : ℕ) : ℂ) = ρ
    rw [ha, Nat.cast_zero, show (Segment.single ρ hρ).first = ρ from Segment.first_ofFirst ρ hρ 1 one_pos,
      IrrGL.nu_zero]
  have key : ∀ x : Fin 1 → IrrGL k, x = (fun _ => ρ) → ∀ hd : ∑ a, (x a).1 = ρ.1,
      IsCosocle ρ.rep (prodIrr x hd) := by
    intro x hx hd
    subst hx
    obtain ⟨φ⟩ := nonempty_equiv_prodIrr_one ρ hd
    exact (isCosocle_self ρ.2.rep.irr).of_equiv (Representation.Equiv.refl _) φ
  have hd : ∑ a : Fin 1, ((Segment.single ρ hρ).term a).1 = ρ.1 := by
    rw [hterm]
    simp
  exact ⟨hd, key _ hterm hd⟩

end GlobalTheory.CompanionTheory.LocGL
