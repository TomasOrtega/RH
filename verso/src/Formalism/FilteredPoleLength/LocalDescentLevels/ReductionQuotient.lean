import Formalism.FilteredPoleLength.ReducedBasisBounds.ReductionQuotient
import Formalism.LogFactorialIndices.LogProductFormula

noncomputable section

namespace Formalism.LatticeBaseChangeAlt

open Module

namespace BasisReduction

open Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

abbrev q (A B : Submodule O X) : ℕ∞ := Module.length O (↥A ⧸ B.comap A.subtype)

/- English proof (translation)
Establish `e : B.comap A.subtype = B'.comap A.subtype`. Use extensionality with `x`. Simplify using `only [Submodule.mem_comap, Submodule.coe_subtype]`. Prove the components needed by the constructor for the conclusion. Introduce `hx`.

Establish `: (x : X) ∈ A ⊓ B'` using `h ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩`. Conclude with `this.2`. Introduce `hx`. Establish `: (x : X) ∈ A ⊓ B` using `h.symm ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩`. Conclude with `this.2`.

Unfold `q`. Rewrite using `[e]`.
-/
theorem q_congr (A : Submodule O X) {B B' : Submodule O X} (h : A ⊓ B = A ⊓ B') :
    q A B = q A B' := by
  have e : B.comap A.subtype = B'.comap A.subtype := by
    ext x
    simp only [Submodule.mem_comap, Submodule.coe_subtype]
    constructor
    · intro hx
      have : (x : X) ∈ A ⊓ B' := h ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
    · intro hx
      have : (x : X) ∈ A ⊓ B := h.symm ▸ Submodule.mem_inf.mpr ⟨x.2, hx⟩
      exact this.2
  unfold q
  rw [e]

/- English proof (translation)
Rewrite using `[add_comm]`. Conclude with `length_chain' hAB hBC`.
-/
theorem q_chain {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    q C A = q C B + q B A := by
  rw [add_comm]
  exact length_chain' hAB hBC

/- English proof (translation)
Establish `h` using `(LinearMap.quotientInfEquivSupQuotient A B).length_eq`. Establish `h2 : q A (A ⊓ B) = q A B` using `q_congr A (by simp)`. Conclude with `h.symm.trans h2`.
-/
theorem q_sup (A B : Submodule O X) : q (A ⊔ B) B = q A B := by
  have h := (LinearMap.quotientInfEquivSupQuotient A B).length_eq
  have h2 : q A (A ⊓ B) = q A B := q_congr A (by simp)
  exact h.symm.trans h2

/- English proof (translation)
The claim follows from `qlen_eq_zero h`.
-/
theorem q_zero {A B : Submodule O X} (h : A ≤ B) : q A B = 0 := qlen_eq_zero h

/- English proof (translation)
Apply `Module.length_le_of_injective (Submodule.mapQ (p.comap f) p f le_rfl)` to reduce the goal to its premises. Introduce `x y hxy`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Simplify using `only [Submodule.mapQ_apply] at hxy`.

Rewrite `hxy`, the goal using `[Submodule.Quotient.eq]`. Simplify using `using hxy`.
-/
theorem len_comap_le {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    (f : M →ₗ[O] M') (p : Submodule O M') :
    Module.length O (M ⧸ p.comap f) ≤ Module.length O (M' ⧸ p) := by
  apply Module.length_le_of_injective (Submodule.mapQ (p.comap f) p f le_rfl)
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simpa using hxy

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Conclude with `len_comap_le _ _`. Establish `h` using `len_comap_le (Submodule.topEquiv (R := O) (M := X)).symm.toLinearMap (N.comap (⊤ : Submodule O X).subtype)`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Use `congr 2`.
-/
theorem q_top (N : Submodule O X) : q ⊤ N = Module.length O (X ⧸ N) := by
  apply le_antisymm
  · exact len_comap_le _ _
  · have h := len_comap_le (Submodule.topEquiv (R := O) (M := X)).symm.toLinearMap
      (N.comap (⊤ : Submodule O X).subtype)
    refine le_trans (le_of_eq ?_) h
    congr 2

end BasisReduction

open BasisReduction

/- English proof (translation)
Introduce `O A _ _ _ n F h0 hn hF N`. Establish `key : ∀ k, Module.length O (A ⧸ N) = ∑ j ∈ Finset.range k, q (F j) (F (j + 1) ⊔ (N ⊓ F j)) + q (F k) N`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [h0, q_top]`.

Consider the case `succ k ih`. Rewrite using `[ih, Finset.sum_range_succ, add_assoc]`. Use `congr 1`. Establish `hB : F (k + 1) ⊔ (N ⊓ F k) ≤ F k` using `sup_le (hF k) inf_le_right`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[q_congr (F (k + 1)) (B := N ⊓ F k) (B' := N)]`. Rewrite using `[inf_comm N, ← inf_assoc, inf_eq_left.mpr (hF k)]`. Rewrite using `[key n, hn, q_zero bot_le, add_zero]`.
-/
theorem filteredLength : FilteredLength := by
  intro O A _ _ _ n F h0 hn hF N
  have key : ∀ k, Module.length O (A ⧸ N) =
      ∑ j ∈ Finset.range k, q (F j) (F (j + 1) ⊔ (N ⊓ F j)) + q (F k) N := by
    intro k
    induction k with
    | zero => simp [h0, q_top]
    | succ k ih =>
      rw [ih, Finset.sum_range_succ, add_assoc]
      congr 1
      have hB : F (k + 1) ⊔ (N ⊓ F k) ≤ F k := sup_le (hF k) inf_le_right
      calc q (F k) N = q (F k) (N ⊓ F k) := q_congr _ (by rw [inf_comm N, ← inf_assoc, inf_idem])
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1) ⊔ (N ⊓ F k)) (N ⊓ F k) :=
            q_chain le_sup_right hB
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) (N ⊓ F k) := by rw [q_sup]
        _ = q (F k) (F (k + 1) ⊔ (N ⊓ F k)) + q (F (k + 1)) N := by
            rw [q_congr (F (k + 1)) (B := N ⊓ F k) (B' := N)]
            rw [inf_comm N, ← inf_assoc, inf_eq_left.mpr (hF k)]
  rw [key n, hn, q_zero bot_le, add_zero]

end Formalism.LatticeBaseChangeAlt
