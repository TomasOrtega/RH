import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.KernelL2RowsColumns

open PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.KerLinear

/- English proof (translation)
Introduce `hb X ι _ φ c hφ`. Prove the components needed by the constructor for the conclusion. Use `⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩` and prove the remaining obligations. Establish `key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i)`. Introduce `s`.

Proceed by induction on `s using Finset.cons_induction with`. Consider the case `empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))`. Consider the case `cons a s ha ih`. Establish `h1 : HasCompactSupport (fun y => φ a y * c a)` using `(hφ a).2.mul_right`. Establish `h2` using `h1.add ih`.

Establish `h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) = (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i`. Use function extensionality and compare the values at `y`. Simplify using `[Finset.sum_cons]`. Rewrite using `[h3]`. Conclude with `h2`.

Conclude with `key Finset.univ`. Introduce `x y`. Establish `hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite` using `fun i => (hb X (φ i) (hφ i)).1 x y`. Establish `hfin' : ∀ i ∈ (Finset.univ : Finset ι), (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite` using `fun i _ => (hfin i).subset (Function.support_mul_subset_left _ _)`. Unfold `ker`.

Rewrite using `[finsum_sum_comm _ _ hfin']`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[finsum_mul]`.
-/
theorem kerLin_of_kerBasic : KerBasic → KerLin := by
  intro hb X ι _ φ c hφ
  constructor
  · refine ⟨continuous_finsetSum _ fun i _ => (hφ i).1.mul continuous_const, ?_⟩
    have key : ∀ s : Finset ι, HasCompactSupport (fun y => ∑ i ∈ s, φ i y * c i) := by
      intro s
      induction s using Finset.cons_induction with
      | empty => exact (HasCompactSupport.zero : HasCompactSupport (0 : X.G → ℂ))
      | cons a s ha ih =>
        have h1 : HasCompactSupport (fun y => φ a y * c a) :=
          (hφ a).2.mul_right
        have h2 := h1.add ih
        have h3 : (fun y => ∑ i ∈ Finset.cons a s ha, φ i y * c i) =
            (fun y => φ a y * c a) + fun y => ∑ i ∈ s, φ i y * c i := by
          funext y
          simp [Finset.sum_cons]
        rw [h3]
        exact h2
    exact key Finset.univ
  · intro x y
    have hfin : ∀ i, (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y)).Finite :=
      fun i => (hb X (φ i) (hφ i)).1 x y
    have hfin' : ∀ i ∈ (Finset.univ : Finset ι),
        (Function.support fun γ : X.Γ => φ i (x⁻¹ * (γ : X.G) * y) * c i).Finite := fun i _ =>
      (hfin i).subset (Function.support_mul_subset_left _ _)
    unfold ker
    rw [finsum_sum_comm _ _ hfin']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [finsum_mul]

end GlobalTheory.CompanionTheory.KerLinear
