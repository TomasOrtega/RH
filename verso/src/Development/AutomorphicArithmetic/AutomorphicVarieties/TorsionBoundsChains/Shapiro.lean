import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.IndPerm

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Introduce `G X _ _ _ x n`. Take `⟨e⟩` from `indPerm G X x`. Set `i1` to `(groupHomology.functor ℤ G n).mapIso e.symm`. Set `i2` to `groupHomology.indIso (MulAction.stabilizer G x) (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) n`. Conclude with `⟨(i1 ≪≫ i2).toLinearEquiv.toAddEquiv⟩`.
-/
theorem UpperTheory.V.KH.shapiro :
    ∀ (G X : Type) [Group G] [MulAction G X] [MulAction.IsPretransitive G X] (x : X) (n : ℕ),
      Nonempty (groupHomology (permRep G X) n ≃+ HZ (MulAction.stabilizer G x) n) := by
  intro G X _ _ _ x n
  classical
  obtain ⟨e⟩ := indPerm G X x
  let i1 := (groupHomology.functor ℤ G n).mapIso e.symm
  let i2 := groupHomology.indIso (MulAction.stabilizer G x) (Rep.trivial ℤ (MulAction.stabilizer G x) ℤ) n
  exact ⟨(i1 ≪≫ i2).toLinearEquiv.toAddEquiv⟩
