import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.ProjectiveBaseChange.AdicTopOf
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChange
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowProduct

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace CrystallineSemistableComparison ReciprocityTheory.ChartRestriction.G.Geo.Tor UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

/- English proof (translation)
Unfold `UpperTheory.Gal.KunnethLefschetz.ProjBC`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `R R' _ _ φ X p hp`. Take `⟨N, i, hi, rfl⟩` from `hp`. Use `letI : Algebra R R' := φ.toAlgebra`.

Set `s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)` to `Spec.map (CommRingCat.ofHom (algebraMap R R'))`. Set `b` to `GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N`. Establish `H` using `GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange R R' N`. Set `ι : pullback (i ≫ b) s ⟶ GroundTheory.Arith.SchemeCoh.projectiveSpace R' N` to `H.lift (pullback.fst (i ≫ b) s ≫ i) (pullback.snd (i ≫ b) s) (by rw [Category.assoc]; exact pullback.condition)`. Establish `hι₁ : ι ≫ _ = pullback.fst (i ≫ b) s ≫ i` using `H.lift_fst _ _ _`.

Establish `hι₂ : ι ≫ _ = pullback.snd (i ≫ b) s` using `H.lift_snd _ _ _`. Establish `hsq : IsPullback ι (pullback.fst (i ≫ b) s) (GroundTheory.Arith.SchemeCoh.ProjSpace.baseChangeMap R R' N) i`. Use `IsPullback.of_right (h₂₂ := b) (v₁₃ := s) ?_ hι₁ H.flip` and prove the remaining obligations. Rewrite using `[hι₂]`. Conclude with `(IsPullback.of_hasPullback (i ≫ b) s).flip`.

Conclude with `⟨N, ι, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hi, hι₂⟩`. Introduce `R _ X p hp`. Take `⟨N, i, hi, rfl⟩` from `hp`. Establish `: IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)` using `inferInstance`. Express the relevant statement in the definitionally equal form `IsProper (i ≫ GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)`.

Use `infer_instance`.
-/
theorem UpperTheory.Gal.KunnethLefschetz.projBC_holds :
    UpperTheory.Gal.KunnethLefschetz.ProjBC := by
  unfold UpperTheory.Gal.KunnethLefschetz.ProjBC
  refine ⟨?_, ?_⟩
  · intro R R' _ _ φ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    letI : Algebra R R' := φ.toAlgebra
    let s : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (algebraMap R R'))
    let b := GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N
    have H := GroundTheory.Arith.SchemeCoh.ProjSpace.isPullback_baseChange R R' N
    let ι : pullback (i ≫ b) s ⟶ GroundTheory.Arith.SchemeCoh.projectiveSpace R' N :=
      H.lift (pullback.fst (i ≫ b) s ≫ i) (pullback.snd (i ≫ b) s) (by rw [Category.assoc]; exact pullback.condition)
    have hι₁ : ι ≫ _ = pullback.fst (i ≫ b) s ≫ i := H.lift_fst _ _ _
    have hι₂ : ι ≫ _ = pullback.snd (i ≫ b) s := H.lift_snd _ _ _
    have hsq : IsPullback ι (pullback.fst (i ≫ b) s) (GroundTheory.Arith.SchemeCoh.ProjSpace.baseChangeMap R R' N) i := by
      refine IsPullback.of_right (h₂₂ := b) (v₁₃ := s) ?_ hι₁ H.flip
      rw [hι₂]
      exact (IsPullback.of_hasPullback (i ≫ b) s).flip
    exact ⟨N, ι, MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsq.flip hi, hι₂⟩
  · intro R _ X p hp
    obtain ⟨N, i, hi, rfl⟩ := hp
    have : IsProper (GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N) := inferInstance
    change IsProper (i ≫ GroundTheory.Arith.SchemeCoh.ProjSpace.toSpecBase R N)
    infer_instance
