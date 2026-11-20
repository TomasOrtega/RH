import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `Y V hV κ _`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `f g hfg`. Unfold `ptOf at hfg`. Establish `h` using `Spec.map_injective ((cancel_mono hV.fromSpec).mp hfg)`.

Conclude with `congrArg CommRingCat.Hom.hom h`. Introduce `φ f m`. Proceed by induction on `m with`. Consider the case `zero => rfl`. Consider the case `succ m ih`.

Rewrite using `[Function.iterate_succ_apply', ih, pow_succ']`. Unfold `twist ptOf`. Rewrite using `[← Spec.map_comp_assoc]`. Both sides reduce to the same expression. Introduce `Z r W hW h B _ ρ z`.

Unfold `ptOf`. Rewrite using `[Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r hV hW h, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.crystallineComparison.ptChart_of :
    PtChart := by
  intro Y V hV κ _
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    unfold ptOf at hfg
    have h := Spec.map_injective ((cancel_mono hV.fromSpec).mp hfg)
    exact congrArg CommRingCat.Hom.hom h
  · intro φ f m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [Function.iterate_succ_apply', ih, pow_succ']
      unfold twist ptOf
      rw [← Spec.map_comp_assoc]
      rfl
  · intro Z r W hW h B _ ρ z
    unfold ptOf
    rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec r hV hW h, ← Spec.map_comp_assoc,
      ← Spec.map_comp_assoc]
    rfl
