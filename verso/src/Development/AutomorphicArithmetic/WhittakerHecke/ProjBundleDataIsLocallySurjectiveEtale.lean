import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataExistsSimplexOfRel

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `T W r d P`. Apply `Presheaf.isLocallySurjective_of_surjective` to reduce the goal to its premises. Introduce `U s`. Take `⟨p, hp⟩` from `Quotient.exists_rep (s : _root_.Quotient (P.relS (unop U)))`. Take `⟨z, hz⟩` from `UpperTheory.projBundleData_exists_simplex_of_rel P 0 (unop U) (fun _ => p) (fun _ _ => P.rel_refl _ p)`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Rewrite using `[← hp]`. Express the relevant statement in the definitionally equal form `Quotient.mk _ (P.sv z 0) = Quotient.mk _ p`. Rewrite using `[hz]`.
-/
theorem UpperTheory.projBundleData_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (P.pS.app (op ⦋0⦌)) := by
  intro T W r d P
  apply Presheaf.isLocallySurjective_of_surjective
  intro U s
  obtain ⟨p, hp⟩ := Quotient.exists_rep (s : _root_.Quotient (P.relS (unop U)))
  obtain ⟨z, hz⟩ := UpperTheory.projBundleData_exists_simplex_of_rel P 0 (unop U) (fun _ => p) (fun _ _ => P.rel_refl _ p)
  refine ⟨z, ?_⟩
  rw [← hp]
  change Quotient.mk _ (P.sv z 0) = Quotient.mk _ p
  rw [hz]
