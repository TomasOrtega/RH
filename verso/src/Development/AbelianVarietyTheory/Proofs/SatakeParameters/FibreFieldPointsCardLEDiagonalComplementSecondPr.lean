import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

/- English proof (translation)
Introduce `K _ y s hs hinj`. Use `set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f with ht`. Establish `hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y` using `fun j => by`. Simplify `hs j` using `[diagComplHom]`. Establish `htf : ∀ j, t j ≫ f = y ≫ f` using `fun j => by`.

Simplify using `only [ht, Category.assoc, pullback.condition]`. Rewrite using `[← hsnd j]`. Simplify using `only [Category.assoc]`. Establish `hne : ∀ j, t j ≠ y`. Introduce `j hj`.

Establish `heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `[← hj, ht]`. Simplify using `[hsnd j]`. Take `⟨x⟩ : Nonempty (Spec (CommRingCat.of K))` from `inferInstance`.

Establish `h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f`. Rewrite using `[← SetLike.mem_coe, ← Scheme.Opens.range_ι]`. Conclude with `⟨_, rfl⟩`. Rewrite `h1` using `[heq]`. Conclude with `h1 ⟨_, rfl⟩`.

Apply `h K (y ≫ f) (Fin.cons y t)` to reduce the goal to its premises. Introduce `j`. Consider the cases of `j using Fin.cases with`. Consider the case `zero => simp`. Consider the case `succ j => simpa using htf j`.

Introduce `i j hij`. Apply the tactic sequence `cases i using Fin.cases <;> cases j using Fin.cases`. Both sides reduce to the same expression. Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij.symm (hne _)`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ] at hij`. Conclude with `absurd hij (hne _)`. Name the introduced variables `i j`. Simplify using `only [Fin.cons_succ] at hij`. Use `congr 1`.

Apply `hinj` to reduce the goal to its premises. Rewrite using `[← cancel_mono (diagCompl f).ι]`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify `hij` using `[ht]`. Simplify using `[hsnd i, hsnd j]`.
-/
theorem fibrePointsLE_diagComplHom {Z X : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (n : ℕ)
    (h : FibrePointsLE f (n + 1)) : FibrePointsLE (diagComplHom f) n := by
  intro K _ y s hs hinj
  set t : Fin (n + 1) → (Spec (CommRingCat.of K) ⟶ Z) := fun j => s j ≫ (diagCompl f).ι ≫ pullback.fst f f
    with ht
  have hsnd : ∀ j, s j ≫ (diagCompl f).ι ≫ pullback.snd f f = y := fun j => by
    simpa [diagComplHom] using hs j
  have htf : ∀ j, t j ≫ f = y ≫ f := fun j => by
    simp only [ht, Category.assoc, pullback.condition]
    rw [← hsnd j]
    simp only [Category.assoc]
  have hne : ∀ j, t j ≠ y := by
    intro j hj
    have heq : s j ≫ (diagCompl f).ι = y ≫ pullback.diagonal f := by
      apply pullback.hom_ext
      · simp [← hj, ht]
      · simp [hsnd j]
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
    have h1 : (s j ≫ (diagCompl f).ι).base x ∈ diagCompl f := by
      rw [← SetLike.mem_coe, ← Scheme.Opens.range_ι]
      exact ⟨_, rfl⟩
    rw [heq] at h1
    exact h1 ⟨_, rfl⟩
  apply h K (y ≫ f) (Fin.cons y t)
  · intro j
    cases j using Fin.cases with
    | zero => simp
    | succ j => simpa using htf j
  · intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · rfl
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij.symm (hne _)
    · simp only [Fin.cons_zero, Fin.cons_succ] at hij; exact absurd hij (hne _)
    · rename_i i j
      simp only [Fin.cons_succ] at hij
      congr 1
      apply hinj
      rw [← cancel_mono (diagCompl f).ι]
      apply pullback.hom_ext
      · simpa [ht] using hij
      · simp [hsnd i, hsnd j]

end GlobalTheory.EtC.Tr
