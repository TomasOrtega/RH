import Development.EtaleCohomology.CohomologicalPurity.LeafTubeCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.TubeCut

instance schPresPb : PreservesLimitsOfShape WalkingCospan sch :=
  inferInstanceAs (PreservesLimitsOfShape WalkingCospan (yoneda ⋙ disc))

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
