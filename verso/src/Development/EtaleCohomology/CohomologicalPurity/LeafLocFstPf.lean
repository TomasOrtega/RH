import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc))

/- English proof (translation)
Introduce `hE H d P V q hq i`. Use `P.cl` as an intermediate fact. Take `⟨⟨z, hpb⟩, -⟩` from `hZ P.X P.Z P.ι V (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) (eta H P V)`. Establish `hpb'` using `hpb.map sch`. Use `H.hens Γ(P.X, V.1) (P.ι.ker.ideal V)` as an intermediate fact.

Establish `hu : IsUnit (q : H.obj Γ(P.X, V.1) (P.ι.ker.ideal V))`. Simplify using `using hq.map ((eta H P V).comp (P.X.presheaf.map (homOfLE le_top).op).hom)`. Establish `e : pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι) = hpb'.isoPullback.inv ≫ sch.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((P.ι.ker.ideal V).map (eta H P V)))))` using `hpb'.isoPullback_inv_fst.symm`. Rewrite using `[e]`. Conclude with `eqv_comp (eqv_iso _ _) (hE q _ _ hu i)`.
-/
theorem LeafLocFst_of (hZ : LeafZ) : LeafLocFst := by
  intro hE H d P V q hq i
  have := P.cl
  obtain ⟨⟨z, hpb⟩, -⟩ := hZ P.X P.Z P.ι V (H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) (eta H P V)
  have hpb' := hpb.map sch
  have := H.hens Γ(P.X, V.1) (P.ι.ker.ideal V)
  have hu : IsUnit (q : H.obj Γ(P.X, V.1) (P.ι.ker.ideal V)) := by
    simpa using hq.map ((eta H P V).comp (P.X.presheaf.map (homOfLE le_top).op).hom)
  have e : pullback.fst (sch.map (hensTo H P V)) (sch.map P.ι) = hpb'.isoPullback.inv ≫
      sch.map (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((P.ι.ker.ideal V).map (eta H P V))))) :=
    hpb'.isoPullback_inv_fst.symm
  rw [e]
  exact eqv_comp (eqv_iso _ _) (hE q _ _ hu i)

end LateralTheory.CohomologicalPurity.TubeCut
