import ReciprocityTheory.DualLattices.UnramifiedCokernelLowerBoundOf
import ReciprocityTheory.DualLattices.IsLocalOfIntegers

noncomputable section

namespace ReciprocityTheory.PGsh.Up

/- English proof (translation)
Introduce `C _ v R _ _ hv M _ _ x d c hx hy hc`. Take `⟨y, hy⟩` from `hy`. Establish `h` using `prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)`. Simplify `h` using `[Finset.prod_const, Finset.card_univ, Fintype.card_fin]`.
-/
theorem killedGen : KilledGenStatement := by
  intro C _ v R _ _ hv M _ _ x d c hx hy hc
  obtain ⟨y, hy⟩ := hy
  have h := prod_le_of_gen hv hx y hy (fun _ => c) (fun i => ⟨0, by simp [hc]⟩)
  simpa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h

end ReciprocityTheory.PGsh.Up
