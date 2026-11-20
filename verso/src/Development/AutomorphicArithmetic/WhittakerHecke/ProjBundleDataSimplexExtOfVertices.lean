import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.ExistsUniqueSimplexPullbackOfMapEq
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Substitute `hv hw` using the available equality. Use `heq_of_eq (Subtype.ext (Prod.ext h (Um.unit_unique w ?_)))` and prove the remaining obligations. Rewrite using `[← p.2, ← p'.2, h]`.
-/
private theorem arrow_heq {A : Type} [CommRing A] {N : ℕ} {v v' w w' : Um N A} (hv : v = v') (hw : w = w')
    (p : v ⟶ w) (p' : v' ⟶ w') (h : p.1.1 = p'.1.1) : HEq p p' := by
  subst hv hw
  refine heq_of_eq (Subtype.ext (Prod.ext h (Um.unit_unique w ?_)))
  rw [← p.2, ← p'.2, h]

/- English proof (translation)
The claim follows from `(congrArg (fun F : Fin (n + 1) ⥤ SingleObj (GL (Fin d) Γ(U, ⊤)) => (show GL (Fin d) Γ(U, ⊤) from F.map (homOfLE hij))) (P.S_comm z)).symm`.
-/
private theorem arrow_mat {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {n : ℕ} {U : Scheme.{0}}
    (z : Sx P.S n U) {i j : Fin (n + 1)} (hij : i ≤ j) :
    ((show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).map (homOfLE hij)).1.1 =
      P.g (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i)
        (pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) j) (pts_eq P.c _ i j) :=
  (congrArg (fun F : Fin (n + 1) ⥤ SingleObj (GL (Fin d) Γ(U, ⊤)) =>
    (show GL (Fin d) Γ(U, ⊤) from F.map (homOfLE hij))) (P.S_comm z)).symm

/- English proof (translation)
Introduce `T W r d P n U z z' h`. Establish `hp : ∀ i, pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i = pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z') i` using `fun i => congrArg Prod.fst (h i)`. Establish `hf : Sx.map (pullback.fst P.bunV (PGL.pr d)) z = Sx.map (pullback.fst P.bunV (PGL.pr d)) z'` using `pts_inj P.c (funext hp)`. Establish `hobj : ∀ i, (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i = (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z').obj i` using `fun i => congrArg Prod.snd (h i)`. Establish `hg : (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z) = (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z')`.

Use `CategoryTheory.Functor.hext hobj (fun i j a => ?_)` and prove the remaining obligations. Establish `hij : i ≤ j` using `leOfHom a`. Take `rfl : a = homOfLE hij` from `Subsingleton.elim _ _`. Use `arrow_heq (hobj i) (hobj j) _ _ ?_` and prove the remaining obligations. Rewrite using `[arrow_mat P z, arrow_mat P z']`.

Conclude with `P.g_congr (hp i) (hp j) _ _`. Conclude with `(UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U _ _ (P.S_comm z)).unique ⟨rfl, rfl⟩ ⟨hf.symm, hg.symm⟩`.
-/
theorem UpperTheory.projBundleData_simplex_ext_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) {n : ℕ} {U : Scheme.{0}} (z z' : Sx P.S n U),
        (∀ i, P.sv z i = P.sv z' i) → z = z' := by
  intro T W r d P n U z z' h
  have hp : ∀ i, pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z) i =
      pts P.c (Sx.map (pullback.fst P.bunV (PGL.pr d)) z') i := fun i => congrArg Prod.fst (h i)
  have hf : Sx.map (pullback.fst P.bunV (PGL.pr d)) z = Sx.map (pullback.fst P.bunV (PGL.pr d)) z' :=
    pts_inj P.c (funext hp)
  have hobj : ∀ i, (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z).obj i =
      (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z').obj i :=
    fun i => congrArg Prod.snd (h i)
  have hg : (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z) =
      (show Fin (n + 1) ⥤ Um d Γ(U, ⊤) from Sx.map (pullback.snd P.bunV (PGL.pr d)) z') := by
    refine CategoryTheory.Functor.hext hobj (fun i j a => ?_)
    have hij : i ≤ j := leOfHom a
    obtain rfl : a = homOfLE hij := Subsingleton.elim _ _
    refine arrow_heq (hobj i) (hobj j) _ _ ?_
    rw [arrow_mat P z, arrow_mat P z']
    exact P.g_congr (hp i) (hp j) _ _
  exact (UpperTheory.existsUnique_simplex_pullback_of_map_eq P.bunV (PGL.pr d) n U _ _ (P.S_comm z)).unique ⟨rfl, rfl⟩ ⟨hf.symm, hg.symm⟩
