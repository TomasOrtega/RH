import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.QuasiIsoChainsOfCechConditionOfLocallySurjective
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataExistsUniqueSimplexOfVertices
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataCechExistsUniqueSimplexOfVertices
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataIsLocallySurjectiveEtale
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataBundleIsLocallySurjectiveEtale
import Development.AutomorphicArithmetic.WhittakerHecke.FirstChernClassProjBundleLineOfTwistEquiv

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `hIn q _ T W r d P hq L ε hL x hx`. Use `haveI := P.smc`. Use `haveI := P.suc`. Use `haveI := P.sme`. Use `haveI := P.sue`.

Establish `hS` using `UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective (ZMod q) P.S P.Q P.pS (UpperTheory.projBundleData_existsUnique_simplex_of_vertices P) (UpperTheory.projBundleData_isLocallySurjective_etale P)`. Establish `hE` using `UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective (ZMod q) (cech P.e) P.Q (P.bunF ≫ P.pS) (UpperTheory.projBundleData_cech_existsUnique_simplex_of_vertices P) (UpperTheory.projBundleData_bundle_isLocallySurjective_etale P)`. Rewrite `hE` using `[Functor.map_comp]`. Establish `hF : QuasiIso ((chains (ZMod q)).map P.bunF)` using `(quasiIso_iff_comp_right _ ((chains (ZMod q)).map P.pS)).1 hE`. Use `UpperTheory.firstChernClass_projBundle_line_of_twist_equiv hIn q r d (cechAug P.c) (cechAug P.e) P.bunV P.bunF (fun i => hIn.a2 _ P.c _) (fun i => hIn.a2 _ P.e _) (fun i n => hIn.a1 _ ((chains (ZMod q)).map P.bunF) _ n) ?_ hq L ε ?_ x hx` and prove the remaining obligations.

Rewrite using `[← Category.assoc, P.bunF_fst, P.ρmap_aug]`. Introduce `U y`. Take `⟨s, h, e⟩` from `pts_spec P.e y`. Establish `h2 : ∀ t : Fin 2, pts P.e y t ≫ P.e = s` using `h`. Rewrite using `[e, P.lineUnit_bunF s _ h2]`.

Conclude with `hL U s _ h2`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.pBOf : UpperTheory.Gal.KunnethLefschetz.G.PBOf := by
  intro hIn q _ T W r d P hq L ε hL x hx
  haveI := P.smc
  haveI := P.suc
  haveI := P.sme
  haveI := P.sue
  have hS := UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective (ZMod q) P.S P.Q P.pS (UpperTheory.projBundleData_existsUnique_simplex_of_vertices P) (UpperTheory.projBundleData_isLocallySurjective_etale P)
  have hE := UpperTheory.quasiIso_chains_of_cech_condition_of_locallySurjective (ZMod q) (cech P.e) P.Q (P.bunF ≫ P.pS) (UpperTheory.projBundleData_cech_existsUnique_simplex_of_vertices P) (UpperTheory.projBundleData_bundle_isLocallySurjective_etale P)
  rw [Functor.map_comp] at hE
  have hF : QuasiIso ((chains (ZMod q)).map P.bunF) := (quasiIso_iff_comp_right _ ((chains (ZMod q)).map P.pS)).1 hE
  refine UpperTheory.firstChernClass_projBundle_line_of_twist_equiv hIn q r d (cechAug P.c) (cechAug P.e) P.bunV P.bunF (fun i => hIn.a2 _ P.c _) (fun i => hIn.a2 _ P.e _)
    (fun i n => hIn.a1 _ ((chains (ZMod q)).map P.bunF) _ n) ?_ hq L ε ?_ x hx
  · rw [← Category.assoc, P.bunF_fst, P.ρmap_aug]
  · intro U y
    obtain ⟨s, h, e⟩ := pts_spec P.e y
    have h2 : ∀ t : Fin 2, pts P.e y t ≫ P.e = s := h
    rw [e, P.lineUnit_bunF s _ h2]
    exact hL U s _ h2
