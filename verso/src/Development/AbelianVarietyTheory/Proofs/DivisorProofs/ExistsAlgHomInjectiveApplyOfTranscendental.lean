import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsAlgHomOfIsTranscendenceBasis
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Set `e` to `Equiv.optionSubtypeNe i₀`. Establish `key : ∀ y : ι → A, y ∘ e = fun o => o.elim (y i₀) (fun b => y b.1)`. Apply the tactic sequence `intro y; funext o; cases o <;> rfl`. Rewrite `hx` using `[← algebraicIndependent_equiv e, key]`. Rewrite using `[← algebraicIndependent_equiv e, key]`.

Take `⟨h1, h2⟩` from `AlgebraicIndependent.option_iff.1 hx`. Establish `hrest : (fun b : {b // b ≠ i₀} => Function.update x i₀ (x i₀ ^ n) b.1) = fun b => x b.1`. Use function extensionality and compare the values at `b`. Conclude with `Function.update_of_ne b.2 _ _`. Rewrite using `[hrest, Function.update_self]`.

Conclude with `AlgebraicIndependent.option_iff.2 ⟨h1, h2.pow hn⟩`.
-/
theorem algebraicIndependent_update_pow {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A]
    [DecidableEq ι] {x : ι → A} (hx : AlgebraicIndependent R x) (i₀ : ι) {n : ℕ} (hn : 0 < n) :
    AlgebraicIndependent R (Function.update x i₀ (x i₀ ^ n)) := by
  let e := Equiv.optionSubtypeNe i₀
  have key : ∀ y : ι → A, y ∘ e = fun o => o.elim (y i₀) (fun b => y b.1) := by
    intro y; funext o; cases o <;> rfl
  rw [← algebraicIndependent_equiv e, key] at hx
  rw [← algebraicIndependent_equiv e, key]
  obtain ⟨h1, h2⟩ := AlgebraicIndependent.option_iff.1 hx
  have hrest : (fun b : {b // b ≠ i₀} => Function.update x i₀ (x i₀ ^ n) b.1) =
      fun b => x b.1 := by
    funext b; exact Function.update_of_ne b.2 _ _
  rw [hrest, Function.update_self]
  exact AlgebraicIndependent.option_iff.2 ⟨h1, h2.pow hn⟩

end GlobalTheory
