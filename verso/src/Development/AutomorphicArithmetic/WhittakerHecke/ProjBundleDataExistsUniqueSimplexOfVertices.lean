import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.LineUnitBunF
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataSimplexExtOfVertices
import Development.AutomorphicArithmetic.WhittakerHecke.ProjBundleDataExistsSimplexOfRel

set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC CrystallineSemistableComparison CrystallineSemistableComparison.Onto Simplicial UpperTheory.Gal.KunnethLefschetz UpperTheory.Gal.KunnethLefschetz.G

/- English proof (translation)
Introduce `T W r d P n U t h`. Establish `hrel : ∀ i j, P.rel U (P.sv (t i) 0) (P.sv (t j) 0)`. Introduce `i j`. Establish `hq : (Quotient.mk (P.relS U) (P.sv (t i) 0)) = Quotient.mk (P.relS U) (P.sv (t j) 0)` using `h i j`. Conclude with `Quotient.exact hq`.

Take `⟨z, hz⟩` from `UpperTheory.projBundleData_exists_simplex_of_rel P n U (fun i => P.sv (t i) 0) hrel`. Establish `key : ∀ (y : Sx P.S n U) (i : Fin (n + 1)), P.sv (Sx.along y (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) 0 = P.sv y i`. Introduce `y i`. Rewrite using `[PBData.sv_along]`. Simplify using the standard rewrite rules.

Use `⟨z, fun i => ?_, fun z' hz' => ?_⟩` and prove the remaining obligations. Apply `UpperTheory.projBundleData_simplex_ext_of_vertices P` to reduce the goal to its premises. Introduce `k`. Establish `hk : k = 0` using `Fin.fin_one_eq_zero k`. Rewrite using `[hk, key, hz]`.

Apply `UpperTheory.projBundleData_simplex_ext_of_vertices P` to reduce the goal to its premises. Introduce `i`. Rewrite using `[← key, hz' i, hz]`.
-/
theorem UpperTheory.projBundleData_existsUnique_simplex_of_vertices :
    ∀ {T W : Scheme.{0}} {r : T ⟶ W} {d : ℕ} (P : PBData r d) (n : ℕ) (U : Scheme.{0}) (t : Fin (n + 1) → Sx P.S 0 U),
        (∀ i j, (P.pS.app (op ⦋0⦌)).app (op U) (t i) = (P.pS.app (op ⦋0⦌)).app (op U) (t j)) →
        ∃! z : Sx P.S n U, ∀ i, Sx.along z (SimplexCategory.const ⦋0⦌ ⦋n⦌ i) = t i := by
  intro T W r d P n U t h
  have hrel : ∀ i j, P.rel U (P.sv (t i) 0) (P.sv (t j) 0) := by
    intro i j
    have hq : (Quotient.mk (P.relS U) (P.sv (t i) 0)) = Quotient.mk (P.relS U) (P.sv (t j) 0) := h i j
    exact Quotient.exact hq
  obtain ⟨z, hz⟩ := UpperTheory.projBundleData_exists_simplex_of_rel P n U (fun i => P.sv (t i) 0) hrel
  have key : ∀ (y : Sx P.S n U) (i : Fin (n + 1)),
      P.sv (Sx.along y (SimplexCategory.const ⦋0⦌ ⦋n⦌ i)) 0 = P.sv y i := by
    intro y i
    rw [PBData.sv_along]
    simp
  refine ⟨z, fun i => ?_, fun z' hz' => ?_⟩
  · apply UpperTheory.projBundleData_simplex_ext_of_vertices P
    intro k
    have hk : k = 0 := Fin.fin_one_eq_zero k
    rw [hk, key, hz]
  · apply UpperTheory.projBundleData_simplex_ext_of_vertices P
    intro i
    rw [← key, hz' i, hz]
