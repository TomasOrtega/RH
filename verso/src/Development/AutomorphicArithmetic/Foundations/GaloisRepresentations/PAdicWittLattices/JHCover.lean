import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle

open CategoryTheory AlgebraicGeometry

namespace UpperTheory.Gal.G3

/- English proof (translation)
Introduce `k _ X s _`. Use `haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩`. Use `haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s`. Set `C` to `X.affineCover.finiteSubcover`. Set `e` to `Fintype.equivFin C.I₀`.

Use `⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]`. Conclude with `C.iSup_opensRange`. Introduce `S hS`. Establish `h` using `IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange) (fun i _ => isAffineOpen_opensRange _)`.

Simplify `h` using `only [Finset.mem_coe]`.
-/
theorem jHCover : PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC.P_cover := by
  intro k _ X s _
  haveI : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from s]; infer_instance⟩
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  let C := X.affineCover.finiteSubcover
  let e := Fintype.equivFin C.I₀
  refine ⟨Fintype.card C.I₀, fun i => (C.f (e.symm i)).opensRange, ?_, ?_⟩
  · rw [e.symm.surjective.iSup_comp (fun j => (C.f j).opensRange)]
    exact C.iSup_opensRange
  · intro S hS
    have h := IsAffineOpen.biInf (X := X) (S : Set (Fin (Fintype.card C.I₀))) S.finite_toSet
      (Finset.coe_nonempty.mpr hS) (U := fun i => (C.f (e.symm i)).opensRange)
      (fun i _ => isAffineOpen_opensRange _)
    simpa only [Finset.mem_coe] using h

end UpperTheory.Gal.G3
