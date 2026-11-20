import Development.EtaleCohomology.EtaleSheaves.ChernClassEvaluation

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.ChernCocycleEdgeCoboundary

open LateralTheory.E.ChernClassRootLocalization in

/- English proof (translation)
Establish `h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0` using `HomologicalComplex.d_comp_d _ _ _ _`. Express the relevant statement in the definitionally equal form `((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem sec_dd (q : ℕ) {V : Scheme.{0}} (y : Sec ((res _ (tw q 1)).X 0) V) :
    Sec.map ((res _ (tw q 1)).d 1 2) (Sec.map ((res _ (tw q 1)).d 0 1) y) = 0 := by
  have h : (res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2 = 0 := HomologicalComplex.d_comp_d _ _ _ _
  change ((((res _ (tw q 1)).d 0 1 ≫ (res _ (tw q 1)).d 1 2).hom.app (op V)).hom y) = 0
  rw [h]
  rfl

/- English proof (translation)
Introduce `q _ E L hi α hα U x`. Establish `key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' = Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x')`. Introduce `V x'`. Use `(LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2 0 1 2 (by simp) (by simp) x'` as an intermediate fact. Rewrite using `[this]`.

Simplify using `[hα.1]`. Apply `LateralTheory.E.ChernClassRootLocalization.sec_sep` to reduce the goal to its premises. Use `LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_` and prove the remaining obligations. Take `⟨v, hv⟩` from `hv`. Rewrite using `[← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]`.

Conclude with `(map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm`.
-/
theorem etale_kummer_chern_cochain_coboundary_vanishes_on_edges_of_local_roots (hr : LateralTheory.E.ChernClassRootLocalization.LeafRootLoc) : LateralTheory.E.ChernClassExistence.EtaleKummerChernCochainCoboundaryVanishesOnEdges := by
  intro q _ E L hi α hα U x
  have key : ∀ (V : Scheme.{0}) (x' : Sx E 1 V), ev (δ 2 3 α) 1 2 (by simp) V x' =
      Sec.map ((res _ (tw q 1)).d 1 2) (ev α 1 1 (by simp) V x') := by
    intro V x'
    have := (LateralTheory.E.ChernClassEvaluation.evDelta_pf (ZMod q) (I := res _ (tw q 1)) (n := 2) (m := 3) (by norm_num) α V).2
      0 1 2 (by simp) (by simp) x'
    rw [this]
    simp [hα.1]
  apply LateralTheory.E.ChernClassRootLocalization.sec_sep
  refine LateralTheory.EtaleFoundations.FirstChernUniqueness.loc_imp (LateralTheory.EtaleFoundations.FirstChernUniqueness.root_line hr q L hi U x) fun V g hv => ?_
  obtain ⟨v, hv⟩ := hv
  rw [← LateralTheory.E.ChernClassRootLocalization.ev_res, key, hα.2.1 V _ v hv, sec_dd]
  exact (map_zero ((res _ (tw q 1)).X 2 |>.obj.map g.op).hom).symm

end LateralTheory.E.ChernCocycleEdgeCoboundary
