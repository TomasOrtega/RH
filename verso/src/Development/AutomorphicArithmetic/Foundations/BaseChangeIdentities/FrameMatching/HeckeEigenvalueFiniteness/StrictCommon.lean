import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.FinStrictHolds

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.HeckeLevelFrameExistence.CF

open PositivityTheory.Rg.BcB.F.FX PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS PositivityTheory.Rg.BcB.CG

/- English proof (translation)
Take `⟨a1, c1, m1⟩` from `h1`. Take `⟨a2, c2, m2⟩` from `h2`. Use `⟨?_, c1.trans c2.symm, fun i => ?_⟩` and prove the remaining obligations. Use `Tw.FiniteStrictOrder.forall₂_ofFn SIso (c1.trans c2.symm) _ _ fun i => ?_` and prove the remaining obligations. Establish `hi : i.val < R.c` using `c1 ▸ i.isLt`.

Establish `e1` using `(List.forall₂_iff_get.1 a1).2 i.val (by simp [parts]) (by simpa [parts] using hi)`. Establish `e2` using `(List.forall₂_iff_get.1 a2).2 i.val (by simpa [parts, c2] using hi) (by simpa [parts] using hi)`. Simplify using `only [parts, List.get_ofFn] at e1 e2`. Conclude with `Tw.FiniteStrictOrder.siso_trans (Q.discrete _).stable e1 e2`. Rewrite using `[m1 i, m2]`.

Both sides reduce to the same expression.
-/
theorem strict_common {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {P Q R : Pre E n} (h1 : Strict P R)
    (h2 : Strict Q R) : Strict P Q := by
  obtain ⟨a1, c1, m1⟩ := h1
  obtain ⟨a2, c2, m2⟩ := h2
  refine ⟨?_, c1.trans c2.symm, fun i => ?_⟩
  · refine Tw.FiniteStrictOrder.forall₂_ofFn SIso (c1.trans c2.symm) _ _ fun i => ?_
    have hi : i.val < R.c := c1 ▸ i.isLt
    have e1 := (List.forall₂_iff_get.1 a1).2 i.val (by simp [parts]) (by simpa [parts] using hi)
    have e2 := (List.forall₂_iff_get.1 a2).2 i.val (by simpa [parts, c2] using hi) (by simpa [parts] using hi)
    simp only [parts, List.get_ofFn] at e1 e2
    exact Tw.FiniteStrictOrder.siso_trans (Q.discrete _).stable e1 e2
  · rw [m1 i, m2]
    rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨List.forall₂_same.2 fun _ _ => ⟨rfl, LinearEquiv.refl ℂ _, fun _ _ _ h => h⟩, rfl, fun _ => rfl⟩`.
-/
theorem strict_refl {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} (P : Pre E n) : Strict P P :=
  ⟨List.forall₂_same.2 fun _ _ => ⟨rfl, LinearEquiv.refl ℂ _, fun _ _ _ h => h⟩, rfl, fun _ => rfl⟩

/- English proof (translation)
Introduce `_ _ _ _ _ _ P' _` and use `⟨fun h => strict_common (strict_refl P') h, fun h h' => strict_common h (strict_common (strict_refl _) h')⟩`.
-/
theorem strictEqv : StrictEqv := fun _ _ _ _ _ _ P' _ =>
  ⟨fun h => strict_common (strict_refl P') h, fun h h' => strict_common h (strict_common (strict_refl _) h')⟩

end UpperTheory.HeckeLevelFrameExistence.CF

end
