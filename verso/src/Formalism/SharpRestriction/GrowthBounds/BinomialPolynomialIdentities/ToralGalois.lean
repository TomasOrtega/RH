import Formalism.SharpRestriction.GrowthBounds.StatementOfDegreeAndBound

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

/- English proof (translation)
Establish `hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu` using `by rw [htop]; trivial`. Use `Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_` and prove the remaining obligations. Introduce `nu y hy`. Distinguish the cases in `h : nu = mu`. Substitute `h` using the available equality.

Rewrite using `[he.1 y hy]`. Conclude with `hy`. Rewrite using `[he.2 nu h y hy]`. Conclude with `zero_mem _`. Rewrite using `[map_zero]`.

Conclude with `zero_mem _`. Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
theorem weight_projector_mem_weight_space {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)
    (htop : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤) (mu : Fin n → ℤ) (e : Module.End K V) (he : IsWtProj E mu e)
    (x : V) : e x ∈ weightSp E mu := by
  have hx : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [htop]; trivial
  refine Submodule.iSup_induction (fun nu => weightSp E nu) (motive := fun y => e y ∈ weightSp E mu) hx ?_ ?_ ?_
  · intro nu y hy
    by_cases h : nu = mu
    · subst h
      rw [he.1 y hy]
      exact hy
    · rw [he.2 nu h y hy]
      exact zero_mem _
  · rw [map_zero]
    exact zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

/- English proof (translation)
Introduce `p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj`. Establish `hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La`. Introduce `u hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem u hu => exact hlat.1 u hu`.

Consider the case `one => exact fun x hx => hx`. Consider the case `mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, y, hy, -, rfl⟩`.

Conclude with `hstab u hu y hy`. Introduce `y hy u hu e he`. Conclude with `⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩`.
-/
theorem adm_eleven (D : Formalism.BasicNotions.D7) : GradedLatticeStable D := by
  intro p _ O _ _ _ _ _S n V _ _ _ _ E mu La hrep _hdom _hiso hlat hproj

  have hstab : ∀ u ∈ UZmon E, ∀ x ∈ La, u x ∈ La := by
    intro u hu
    induction hu using Submonoid.closure_induction with
    | mem u hu => exact hlat.1 u hu
    | one => exact fun x hx => hx
    | mul u v _ _ hu hv => exact fun x hx => hu _ (hv x hx)
  refine ⟨?_, ?_⟩
  · rw [Submodule.span_le]
    rintro x ⟨u, hu, y, hy, -, rfl⟩
    exact hstab u hu y hy
  · intro y hy u hu e he
    exact ⟨hproj _ (hstab u hu y hy) mu e he, weight_projector_mem_weight_space E hrep.2.2 mu e he _⟩

end Formalism.MainNotions.G.ColumnFamilies
