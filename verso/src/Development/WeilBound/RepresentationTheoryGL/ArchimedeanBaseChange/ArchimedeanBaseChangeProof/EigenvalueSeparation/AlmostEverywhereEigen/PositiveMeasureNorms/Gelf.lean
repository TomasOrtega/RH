import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2
namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Introduce `K _ _ _ B _ _ _ _ R`. Set `A0 : StarSubalgebra ℂ (K →L[ℂ] K)` to `R.range`. Establish `hc : ∀ x y : A0, x * y = y * x`. Introduce and unpack `⟨x, b, rfl⟩ ⟨y, c, rfl⟩`. Apply `Subtype.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `R b * R c = R c * R b`. Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Set `A : StarSubalgebra ℂ (K →L[ℂ] K)` to `A0.topologicalClosure`. Establish `: IsClosed (A : Set (K →L[ℂ] K))` using `A0.isClosed_topologicalClosure`. Set `cr : CommRing A` to `A0.commRingTopologicalClosure hc`.

Set `_ : CommCStarAlgebra A` to `{ (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }`. Set `G` to `gelfandStarTransform A`. Establish `hmem : ∀ b, R b ∈ A` using `fun b => A0.le_topologicalClosure ⟨b, rfl⟩`. Use `⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance, A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩` and prove the remaining obligations. Introduce `f`.

Apply the tactic sequence `have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _`. Rewrite `h1` using `[G.apply_symm_apply]`. Rewrite using `[h1]`. Both sides reduce to the same expression. Introduce `b`.

Express the relevant statement in the definitionally equal form `((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b`. Rewrite using `[G.symm_apply_apply]`.
-/
theorem gelf : Gelf := by
  intro K _ _ _ B _ _ _ _ R
  let A0 : StarSubalgebra ℂ (K →L[ℂ] K) := R.range
  have hc : ∀ x y : A0, x * y = y * x := by
    rintro ⟨x, b, rfl⟩ ⟨y, c, rfl⟩
    apply Subtype.ext
    change R b * R c = R c * R b
    rw [← map_mul, ← map_mul, mul_comm]
  let A : StarSubalgebra ℂ (K →L[ℂ] K) := A0.topologicalClosure
  have : IsClosed (A : Set (K →L[ℂ] K)) := A0.isClosed_topologicalClosure
  let cr : CommRing A := A0.commRingTopologicalClosure hc
  let _ : CommCStarAlgebra A :=
    { (inferInstance : CStarAlgebra A) with mul_comm := cr.mul_comm }
  let G := gelfandStarTransform A
  have hmem : ∀ b, R b ∈ A := fun b => A0.le_topologicalClosure ⟨b, rfl⟩
  refine ⟨WeakDual.characterSpace ℂ A, inferInstance, inferInstance, inferInstance,
    A.subtype.comp G.symm.toStarAlgHom, G.toStarAlgHom.comp (R.codRestrict A hmem), ?_, ?_⟩
  · intro f
    have h1 : ‖G (G.symm f)‖ = ‖G.symm f‖ := (gelfandTransform_isometry A).norm_map_of_map_zero (map_zero _) _
    rw [G.apply_symm_apply] at h1
    rw [h1]
    rfl
  · intro b
    change ((G.symm (G ⟨R b, hmem b⟩) : A) : K →L[ℂ] K) = R b
    rw [G.symm_apply_apply]

end PositivityTheory.Rg.BcB.E2.P
