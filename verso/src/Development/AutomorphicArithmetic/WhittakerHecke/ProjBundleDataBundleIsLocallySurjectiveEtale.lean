import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Take `⟨O, a, h, u, hx, hv⟩` from `P.onto p.1 p.2 x`. Use `⟨O, hx, cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl), ?_⟩` and prove the remaining obligations. Establish `key : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0})) (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl)) = Quotient.mk (P.relS (O : Scheme.{0})) (a ≫ P.ρ, P.v a)`. Express the relevant statement in the definitionally equal form `Quotient.mk _ (P.sv (Sx.map P.bunF (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl))) 0) = _`. Rewrite using `[P.sv_bunF, pts_cechPt]`.

Rewrite using `[key]`. Conclude with `Quotient.sound ⟨h, u, hv⟩`.
-/
private theorem exists_local_lift {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {U : Scheme.{0}}
    (p : P.PA.obj (op U)) (x : U) :
    ∃ O : U.Opens, x ∈ O ∧ ∃ t : Sx (cech P.e) 0 (O : Scheme.{0}),
      ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0})) t =
        Quotient.mk (P.relS (O : Scheme.{0})) (P.PA.map O.ι.op p) := by
  obtain ⟨O, a, h, u, hx, hv⟩ := P.onto p.1 p.2 x
  refine ⟨O, hx, cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl), ?_⟩
  have key : ((P.bunF ≫ P.pS).app (op ⦋0⦌)).app (op (O : Scheme.{0}))
      (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl)) =
      Quotient.mk (P.relS (O : Scheme.{0})) (a ≫ P.ρ, P.v a) := by
    change Quotient.mk _ (P.sv (Sx.map P.bunF (cechPt P.e 0 (a ≫ P.e) (fun _ => a) (fun _ => rfl))) 0) = _
    rw [P.sv_bunF, pts_cechPt]
  rw [key]
  exact Quotient.sound ⟨h, u, hv⟩

/- English proof (translation)
Introduce `T W r d P`. Prove the components needed by the constructor for the conclusion. Introduce `U s`. Take `⟨p, rfl⟩` from `Quotient.exists_rep s`. Use `choose O hO t ht using fun x => exists_local_lift P p x`.

Establish `hc : TopologicalSpace.IsOpenCover O`. Rewrite using `[TopologicalSpace.IsOpenCover, eq_top_iff]`. Introduce `x _`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨x, hO x⟩`. Apply `Scheme.zariskiTopology_le_etaleTopology` to reduce the goal to its premises.

Use `GrothendieckTopology.superset_covering _ ?_ (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hc))` and prove the remaining obligations. Rewrite using `[Sieve.ofArrows, Sieve.generate_le_iff]`. Introduce and unpack `_ _ ⟨x⟩`. Conclude with `⟨t x, ht x⟩`.
-/
theorem UpperTheory.projBundleData_bundle_isLocallySurjective_etale :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d),
        Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} ((P.bunF ≫ P.pS).app (op ⦋0⦌)) := by
  intro T W r d P
  constructor
  intro U s
  obtain ⟨p, rfl⟩ := Quotient.exists_rep s
  choose O hO t ht using fun x => exists_local_lift P p x
  have hc : TopologicalSpace.IsOpenCover O := by
    rw [TopologicalSpace.IsOpenCover, eq_top_iff]
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨x, hO x⟩
  apply Scheme.zariskiTopology_le_etaleTopology
  refine GrothendieckTopology.superset_covering _ ?_
    (Scheme.Cover.mem_grothendieckTopology (U.openCoverOfIsOpenCover O hc))
  rw [Sieve.ofArrows, Sieve.generate_le_iff]
  rintro _ _ ⟨x⟩
  exact ⟨t x, ht x⟩
