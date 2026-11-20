import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

/- English proof (translation)
Introduce `l _ K d M A hA h k`. Establish `hphi : ∀ c : ↥(K0 K), (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) = algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c)` using `fun c => by`. Rewrite using `[← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨1, by simp, by simp⟩`.

Consider the case `succ k ih`. Take `⟨F, hF, e⟩` from `ih`. Use `⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Use `hA.mul ?_` and prove the remaining obligations.

Use `hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))` as an intermediate fact. Rewrite `this` using `[RingHom.map_det]`. Conclude with `this`. Rewrite using `[Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]`. Use `congr 2`.

Use extensionality with `i j`. Conclude with `hphi _`.
-/
theorem UpperTheory.frobenius_iterate_matrix_form :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {d : ℕ} (M : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ k : ℕ, ∃ F : Matrix (Fin d) (Fin d) ↥(K0 K), IsUnit F.det ∧ M.map (((PP l).φB)^[k]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) := by
  intro l _ K d M A hA h k
  have hphi : ∀ c : ↥(K0 K), (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c) := fun c => by
    rw [← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨F, hF, e⟩ := ih
    refine ⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩
    · rw [Matrix.det_mul]
      refine hA.mul ?_
      have := hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))
      rw [RingHom.map_det] at this
      exact this
    · rw [Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact hphi _
