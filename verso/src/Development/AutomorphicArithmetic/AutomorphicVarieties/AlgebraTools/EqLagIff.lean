import Mathlib

noncomputable section

open Polynomial

namespace UpperTheory.V.AlgebraTools

def lag {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) : E :=
  Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j)) •
    aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j)))

/- English proof (translation)
Establish `hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j))`. Use `Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_` and prove the remaining obligations. Introduce `j hj`. Conclude with `h j (Finset.ne_of_mem_erase hj)`. Take `⟨v, hv⟩` from `hu`.

Unfold `lag`. Rewrite using `[← hv, Ring.inverse_unit, ← Units.smul_def, ← Units.smul_def]`. Conclude with `eq_inv_smul_iff`.
-/
theorem eq_lag_iff {R E ι : Type*} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (P : E) (i : ι) (h : ∀ j, j ≠ i → IsUnit (a i - a j)) (f : E) :
    f = lag a P i ↔ (∏ j ∈ Finset.univ.erase i, (a i - a j)) • f =
      aeval P (∏ j ∈ Finset.univ.erase i, (X - C (a j))) := by
  have hu : IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := by
    refine Finset.prod_induction _ IsUnit (fun x y hx hy => hx.mul hy) isUnit_one ?_
    intro j hj
    exact h j (Finset.ne_of_mem_erase hj)
  obtain ⟨v, hv⟩ := hu
  unfold lag
  rw [← hv, Ring.inverse_unit, ← Units.smul_def, ← Units.smul_def]
  exact eq_inv_smul_iff

/- English proof (translation)
Establish `: (Finset.univ : Finset Unit).erase () = ∅` using `rfl`. Simplify using `[lag, this]`.
-/
example (R : Type) [CommRing R] (a : Unit → R) (P : R) : lag a P () = 1 := by
  have : (Finset.univ : Finset Unit).erase () = ∅ := rfl
  simp [lag, this]

def pat {ι : Type*} (R : Type*) [CommRing R] (p : ι → ι → Prop) : Submodule R (Matrix ι ι R) where
  carrier := {X | ∀ i j, ¬ p i j → X i j = 0}
  add_mem' := fun hX hY i j h => by simp [hX i j h, hY i j h]
  zero_mem' := fun _ _ _ => rfl
  smul_mem' := fun c X hX i j h => by simp [hX i j h]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_pat {ι R : Type*} [CommRing R] {p : ι → ι → Prop} {X : Matrix ι ι R} :
    X ∈ pat R p ↔ ∀ i j, ¬ p i j → X i j = 0 := Iff.rfl

/- English proof (translation)
Use extensionality with `X`. Simplify using `[mem_pat]`.
-/
example {ι R : Type} [CommRing R] : pat R (fun _ _ : ι => True) = ⊤ := by
  ext X; simp [mem_pat]

end UpperTheory.V.AlgebraTools
