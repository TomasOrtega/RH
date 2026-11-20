import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrAdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.PrVr
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

/- English proof (translation)
Introduce `l _ S μ hμ hB`. Take `⟨Y, -, -, hY⟩` from `hB`. Take `⟨-, p2, p3, p4, -⟩` from `prAdd l S`. Establish `hμ' : ∀ (b : S.Bh) y, μ (b • y) = S.rF b * μ y` using `hμ`. Establish `hinv : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1`.

Introduce `g`. Simplify using `only [Ctx.ρ, NP.ρX, mat]`. Rewrite using `[← Matrix.map_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hN : ∀ y : S.U.N, S.pr0 (y : S.U.AA) = 0 ∧ S.pr1 (y : S.U.AA) = y`. Introduce `y`.

Simplify using `using p2 0 y`. Establish `h0 : S.pr0 0 = 0 ∧ S.pr1 0 = 0` using `hN 0`. Establish `key : ∀ Z ∈ Submodule.span S.Bh (Set.range S.U.vr), Z.map (fun a => μ (S.pr1 a)) = Z.map (fun a => S.rF (S.pr0 a)) * Y - Y * Z.map (fun a => S.rF (S.pr0 a))`. Introduce `Z hZ`. Proceed by induction on `hZ using Submodule.span_induction with`.

Consider the case `mem Z hZ`. Take `⟨g, rfl⟩` from `hZ`. Establish `e0 : (S.U.vr g).map (fun a => S.rF (S.pr0 a)) = S.ρ S.F g`. Use extensionality with `i j`. Conclude with `(prVr l S g i j).1`.

Establish `e1 : (S.U.vr g).map (fun a => μ (S.pr1 a)) * S.ρ S.F g⁻¹ = S.ρ S.F g * Y * S.ρ S.F g⁻¹ - Y` using `congrFun hY g`. Establish `e2` using `congrArg (· * S.ρ S.F g) e1`. Simplify using `only [Matrix.mul_assoc, Matrix.sub_mul, hinv, Matrix.mul_one] at e2`. Rewrite using `[e0, e2]`. Consider the case `zero`.

Establish `a0 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => S.rF (S.pr0 a)) = 0`. Use extensionality with `i j`. Simplify using `[h0.1]`. Establish `a1 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => μ (S.pr1 a)) = 0`. Use extensionality with `i j`.

Simplify using `[h0.2]`. Rewrite using `[a0, a1]`. Simplify using the standard rewrite rules. Consider the case `add Z Z' _ _ h h'`. Establish `a0 : (Z + Z').map (fun a => S.rF (S.pr0 a)) = Z.map (fun a => S.rF (S.pr0 a)) + Z'.map (fun a => S.rF (S.pr0 a))`.

Use extensionality with `i j`. Simplify using `[(p3 _ _).1]`. Establish `a1 : (Z + Z').map (fun a => μ (S.pr1 a)) = Z.map (fun a => μ (S.pr1 a)) + Z'.map (fun a => μ (S.pr1 a))`. Use extensionality with `i j`. Simplify using `[(p3 _ _).2]`.

Rewrite using `[a0, a1, h, h', Matrix.add_mul, Matrix.mul_add]`. Normalize the expressions using the abelian group laws. Consider the case `smul b Z _ h`. Establish `a0 : (b • Z).map (fun a => S.rF (S.pr0 a)) = S.rF b • Z.map (fun a => S.rF (S.pr0 a))`. Use extensionality with `i j`.

Simplify using `[(p4 _ _).1]`. Establish `a1 : (b • Z).map (fun a => μ (S.pr1 a)) = S.rF b • Z.map (fun a => μ (S.pr1 a))`. Use extensionality with `i j`. Simplify using `[(p4 _ _).2, hμ']`. Rewrite using `[a0, a1, h, Matrix.smul_mul, Matrix.mul_smul, smul_sub]`.

Use extensionality with `y`. Break down `S.x.a_le.eq_or_lt with ha | ha` into its components or cases. Establish `hy : y = 0`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(S.U.typeI ha).le y.2`.

Rewrite using `[hy, map_zero, map_zero]`. Establish `hp` using `S.x.a_pos`. Set `i : Fin S.n` to `⟨0, by omega⟩`. Set `j : Fin S.n` to `⟨S.x.a, ha⟩`. Establish `hm : Matrix.single i j (y : S.U.AA) ∈ Submodule.span S.Bh (Set.range S.U.vr)`.

Rewrite using `[S.U.span]`. Introduce `i' j'`. Distinguish the cases in `e : i = i' ∧ j = j'`. Take `⟨rfl, rfl⟩` from `e`. Use `⟨fun e => ?_, fun _ => by simp⟩` and prove the remaining obligations.

Conclude with `absurd (e.1 (by simp only [i]; omega)) (by simp [j])`. Rewrite using `[Matrix.single_apply_of_ne _ _ _ _ _ e]`. Conclude with `⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩`. Establish `a0 : (Matrix.single i j (y : S.U.AA)).map (fun a => S.rF (S.pr0 a)) = 0`. Use extensionality with `i' j'`.

Distinguish the cases in `e : i = i' ∧ j = j'`. Take `⟨rfl, rfl⟩` from `e`. Simplify using `[(hN y).1]`. Simplify using `[Matrix.single_apply_of_ne _ _ _ _ _ e, h0.1]`. Establish `k` using `key _ hm`.

Rewrite `k` using `[a0]`. Establish `k'` using `congrFun (congrFun k i) j`. Simplify `k'` using `[(hN y).2]`.
-/
theorem UpperTheory.V.Pa.laInj :
    ∀ (l : ℕ) [Fact l.Prime] (S : Ctx l), ∀ μ ∈ S.La, S.laC μ ∈ BdM S.h S.x S.F → μ = 0 := by
  intro l _ S μ hμ hB
  obtain ⟨Y, -, -, hY⟩ := hB
  obtain ⟨-, p2, p3, p4, -⟩ := prAdd l S
  have hμ' : ∀ (b : S.Bh) y, μ (b • y) = S.rF b * μ y := hμ
  have hinv : ∀ g, S.ρ S.F g⁻¹ * S.ρ S.F g = 1 := by
    intro g
    simp only [Ctx.ρ, NP.ρX, mat]
    rw [← Matrix.map_mul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hN : ∀ y : S.U.N, S.pr0 (y : S.U.AA) = 0 ∧ S.pr1 (y : S.U.AA) = y := by
    intro y
    simpa using p2 0 y
  have h0 : S.pr0 0 = 0 ∧ S.pr1 0 = 0 := hN 0
  have key : ∀ Z ∈ Submodule.span S.Bh (Set.range S.U.vr),
      Z.map (fun a => μ (S.pr1 a)) =
        Z.map (fun a => S.rF (S.pr0 a)) * Y - Y * Z.map (fun a => S.rF (S.pr0 a)) := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ =>
      obtain ⟨g, rfl⟩ := hZ
      have e0 : (S.U.vr g).map (fun a => S.rF (S.pr0 a)) = S.ρ S.F g := by
        ext i j; exact (prVr l S g i j).1
      have e1 : (S.U.vr g).map (fun a => μ (S.pr1 a)) * S.ρ S.F g⁻¹ =
          S.ρ S.F g * Y * S.ρ S.F g⁻¹ - Y := congrFun hY g
      have e2 := congrArg (· * S.ρ S.F g) e1
      simp only [Matrix.mul_assoc, Matrix.sub_mul, hinv, Matrix.mul_one] at e2
      rw [e0, e2]
    | zero =>
      have a0 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => S.rF (S.pr0 a)) = 0 := by
        ext i j; simp [h0.1]
      have a1 : (0 : Matrix (Fin S.n) (Fin S.n) S.U.AA).map (fun a => μ (S.pr1 a)) = 0 := by
        ext i j; simp [h0.2]
      rw [a0, a1]; simp
    | add Z Z' _ _ h h' =>
      have a0 : (Z + Z').map (fun a => S.rF (S.pr0 a)) =
          Z.map (fun a => S.rF (S.pr0 a)) + Z'.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p3 _ _).1]
      have a1 : (Z + Z').map (fun a => μ (S.pr1 a)) =
          Z.map (fun a => μ (S.pr1 a)) + Z'.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p3 _ _).2]
      rw [a0, a1, h, h', Matrix.add_mul, Matrix.mul_add]; abel
    | smul b Z _ h =>
      have a0 : (b • Z).map (fun a => S.rF (S.pr0 a)) = S.rF b • Z.map (fun a => S.rF (S.pr0 a)) := by
        ext i j; simp [(p4 _ _).1]
      have a1 : (b • Z).map (fun a => μ (S.pr1 a)) = S.rF b • Z.map (fun a => μ (S.pr1 a)) := by
        ext i j; simp [(p4 _ _).2, hμ']
      rw [a0, a1, h, Matrix.smul_mul, Matrix.mul_smul, smul_sub]
  ext y
  rcases S.x.a_le.eq_or_lt with ha | ha
  · have hy : y = 0 := by
      apply Subtype.ext
      exact (S.U.typeI ha).le y.2
    rw [hy, map_zero, map_zero]
  · have hp := S.x.a_pos
    let i : Fin S.n := ⟨0, by omega⟩
    let j : Fin S.n := ⟨S.x.a, ha⟩
    have hm : Matrix.single i j (y : S.U.AA) ∈ Submodule.span S.Bh (Set.range S.U.vr) := by
      rw [S.U.span]
      intro i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        refine ⟨fun e => ?_, fun _ => by simp⟩
        exact absurd (e.1 (by simp only [i]; omega)) (by simp [j])
      · rw [Matrix.single_apply_of_ne _ _ _ _ _ e]
        exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
    have a0 : (Matrix.single i j (y : S.U.AA)).map (fun a => S.rF (S.pr0 a)) = 0 := by
      ext i' j'
      by_cases e : i = i' ∧ j = j'
      · obtain ⟨rfl, rfl⟩ := e
        simp [(hN y).1]
      · simp [Matrix.single_apply_of_ne _ _ _ _ _ e, h0.1]
    have k := key _ hm
    rw [a0] at k
    have k' := congrFun (congrFun k i) j
    simpa [(hN y).2] using k'
