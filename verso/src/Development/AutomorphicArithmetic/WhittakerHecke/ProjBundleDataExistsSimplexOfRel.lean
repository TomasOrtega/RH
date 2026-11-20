import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsUniqueSimplexPullbackOfMapEq

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `T W r d P n U t ht`. Use `choose h u hu using ht`. Set `F : ComposableArrows (Um d Γ(U, ⊤)) n` to `{ obj := fun i => (t i).2 map := fun {i j} _ => ⟨(P.g (t i).1 (t j).1 (h i j), u i j), hu i j⟩ map_id := by`. Introduce `i`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Prod.ext` to reduce the goal to its premises. Conclude with `P.g_self _ _`. Use `show u i i = 1`. Apply `Um.unit_unique (t i).2` to reduce the goal to its premises. Establish `e` using `hu i i`.

Rewrite `e` using `[P.g_self]`. Rewrite using `[Units.val_one, one_smul, ← e]`. Simplify using the standard rewrite rules. Use `map_comp := by`. Introduce `i j k _ _`.

Apply `Subtype.ext` to reduce the goal to its premises. Apply `Prod.ext` to reduce the goal to its premises. Use `show P.g (t i).1 (t k).1 (h i k) = P.g (t j).1 (t k).1 (h j k) * P.g (t i).1 (t j).1 (h i j)`. Conclude with `(P.g_coc _ _ _ (h i j) (h j k)).symm`. Use `show u i k = u j k * u i j`.

Apply `Um.unit_unique (t k).2` to reduce the goal to its premises. Rewrite using `[← hu i k, ← P.g_coc _ _ _ (h i j) (h j k), Units.val_mul, ← Matrix.mulVec_mulVec, hu i j, Matrix.mulVec_smul, hu j k, smul_smul, Units.val_mul, mul_comm] }`. Set `x : Sx (cech P.c) n U` to `cechPt P.c n ((t 0).1 ≫ P.c) (fun i => (t i).1) (fun i => h i 0)`. Establish `hx : pts P.c x = fun i => (t i).1` using `pts_cechPt _ _ _ _`. Establish `key : Sx.map P.bunV x = Sx.map (PGL.pr d) F` using `by show (P.gFun (pts P.c x) (pts_eq P.c x) : ComposableArrows (SingleObj (GL (Fin d) Γ(U, ⊤))) n) = F ⋙ Um.toGL d Γ(U, ⊤) fapply CategoryTheory.Functor.ext`.

Introduce `i`. Both sides reduce to the same expression. Introduce `i j f`. Simplify using `only [eqToHom_refl, Category.id_comp, Category.comp_id]`. Use `show P.g (pts P.c x i) (pts P.c x j) _ = P.g (t i).1 (t j).1 (h i j)`.

Conclude with `P.g_congr (congrFun hx i) (congrFun hx j) _ _`. Take `⟨z, ⟨hz1, hz2⟩, -⟩` from `UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U x F key`. Use `⟨z, fun i => ?_⟩` and prove the remaining obligations. Use `show (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i, (Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i) = t i`. Rewrite using `[hz1, hz2, hx]`.

Both sides reduce to the same expression.
-/
theorem UpperTheory.projBundleData_exists_simplex_of_rel :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → P.PA.obj (op U)),
        (∀ i j, P.rel U (t i) (t j)) → ∃ z : Sx P.S n U, ∀ i, P.sv z i = t i := by
  intro T W r d P n U t ht
  choose h u hu using ht
  let F : ComposableArrows (Um d Γ(U, ⊤)) n :=
    { obj := fun i => (t i).2
      map := fun {i j} _ => ⟨(P.g (t i).1 (t j).1 (h i j), u i j), hu i j⟩
      map_id := by
        intro i
        apply Subtype.ext
        apply Prod.ext
        · exact P.g_self _ _
        · show u i i = 1
          apply Um.unit_unique (t i).2
          have e := hu i i
          rw [P.g_self] at e
          rw [Units.val_one, one_smul, ← e]
          simp
      map_comp := by
        intro i j k _ _
        apply Subtype.ext
        apply Prod.ext
        · show P.g (t i).1 (t k).1 (h i k) = P.g (t j).1 (t k).1 (h j k) * P.g (t i).1 (t j).1 (h i j)
          exact (P.g_coc _ _ _ (h i j) (h j k)).symm
        · show u i k = u j k * u i j
          apply Um.unit_unique (t k).2
          rw [← hu i k, ← P.g_coc _ _ _ (h i j) (h j k), Units.val_mul, ← Matrix.mulVec_mulVec,
            hu i j, Matrix.mulVec_smul, hu j k, smul_smul, Units.val_mul, mul_comm] }
  let x : Sx (cech P.c) n U := cechPt P.c n ((t 0).1 ≫ P.c) (fun i => (t i).1) (fun i => h i 0)
  have hx : pts P.c x = fun i => (t i).1 := pts_cechPt _ _ _ _
  have key : Sx.map P.bunV x = Sx.map (PGL.pr d) F := by
    show (P.gFun (pts P.c x) (pts_eq P.c x) : ComposableArrows (SingleObj (GL (Fin d) Γ(U, ⊤))) n) =
      F ⋙ Um.toGL d Γ(U, ⊤)
    fapply CategoryTheory.Functor.ext
    · intro i
      rfl
    · intro i j f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      show P.g (pts P.c x i) (pts P.c x j) _ = P.g (t i).1 (t j).1 (h i j)
      exact P.g_congr (congrFun hx i) (congrFun hx j) _ _
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U x F key
  refine ⟨z, fun i => ?_⟩
  show (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i,
    (Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i) = t i
  rw [hz1, hz2, hx]
  rfl
