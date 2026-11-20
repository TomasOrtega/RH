import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.FinCover
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.AppLEFromOfGlobalSectionsChartHom
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.SegreGlue
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowSegre

open CategoryTheory Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

/- English proof (translation)
Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem exists_closed_prod {R : Type} [CommRing R] {X Y : Scheme.{0}} (N M : ℕ)
    (i : X ⟶ projectiveSpace R N) (j : Y ⟶ projectiveSpace R M)
    [IsClosedImmersion i] [IsClosedImmersion j] :
    ∃ h : pullback (i ≫ toSpecBase R N) (j ≫ toSpecBase R M) ⟶
        projectiveSpace R (N * M + N + M),
      IsClosedImmersion h ∧
        h ≫ toSpecBase R (N * M + N + M) =
          pullback.fst (i ≫ toSpecBase R N) (j ≫ toSpecBase R M) ≫ i ≫ toSpecBase R N := by
  haveI : MorphismProperty.IsStableUnderComposition
      (@IsClosedImmersion : MorphismProperty Scheme.{0}) :=
    ⟨fun f g hf hg => by
      haveI := hf
      haveI := hg
      exact IsClosedImmersion.comp f g⟩
  have hmap : IsClosedImmersion (pullback.map (i ≫ toSpecBase R N) (j ≫ toSpecBase R M)
      (toSpecBase R N) (toSpecBase R M) i j (𝟙 _)
      ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl)) :=
    MorphismProperty.pullback_map (P := (@IsClosedImmersion : MorphismProperty Scheme.{0}))
      inferInstance inferInstance rfl rfl
  refine ⟨pullback.map (i ≫ toSpecBase R N) (j ≫ toSpecBase R M)
      (toSpecBase R N) (toSpecBase R M) i j (𝟙 _)
      ((Category.comp_id _).trans rfl) ((Category.comp_id _).trans rfl) ≫ segre R N M,
    inferInstance, ?_⟩
  rw [Category.assoc, segre_toSpecBase, pullback.lift_fst_assoc, Category.assoc]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.projProd :
    UpperTheory.Gal.KunnethLefschetz.G.ProjProd := by
  intro R _ X Y p q hp
  obtain ⟨N, i, hi, rfl⟩ := hp
  have hprop : IsProper (PSpace.str R N) :=
    inferInstanceAs (IsProper (toSpecBase R N))
  refine ⟨?_, fun j hj => ⟨N, j ≫ i, inferInstance, by simp⟩, inferInstance⟩
  rintro ⟨M, j, hj, rfl⟩
  obtain ⟨h, hc, he⟩ := exists_closed_prod (R := R) N M i j
  exact ⟨_, h, hc, he⟩
