import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bdy
open Finset Polynomial
open Formalism.REAL (GlRel KHighest IsWeight qdet Tm qminor)
open CompanionTheory.D.LK (Pos Cn ann cre lift bd cpt allT wt ev)
open CompanionTheory.RgExh CompanionTheory.RgExh.U
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec
open GlobalTheory.CompanionTheory.RgCOBlock

namespace GlobalTheory.CompanionTheory.RgCOBlock.SumSz

/- English proof (translation)
Introduce `n M lev h`. Establish `key` using `Finset.card_eq_sum_card_fiberwise (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M))) (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))`. Rewrite `key` using `[Finset.card_univ, Fintype.card_fin]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm` and prove the remaining obligations. Unfold `sz`.

Use `congr 1`. Use extensionality with `a`. Simplify using `[Fin.ext_iff]`.
-/
theorem sum_sz_eq_card : ∀ (n M : ℕ) (lev : Fin n → ℕ), (∀ a, lev a < M) → ∑ i, sz lev M i = n := by
  intro n M lev h
  have key := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (Fin n))) (t := (univ : Finset (Fin M)))
    (f := fun a => (⟨lev a, h a⟩ : Fin M)) (fun a _ => Finset.mem_coe.2 (mem_univ _))
  rw [Finset.card_univ, Fintype.card_fin] at key
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) key.symm
  unfold sz
  congr 1
  ext a
  simp [Fin.ext_iff]

end GlobalTheory.CompanionTheory.RgCOBlock.SumSz
