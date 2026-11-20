import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.ThK.OneParamLie

/- English proof (translation)
Use `letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)`. Use `letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)`. Establish `h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (NormedSpace.exp ((0:ℝ) • Z) * Z) 0` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0`. Establish `h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z.conjTranspose)) (NormedSpace.exp ((0:ℝ) • Z.conjTranspose) * Z.conjTranspose) 0` using `hasDerivAt_exp_smul_const (𝕂 := ℝ) Z.conjTranspose 0`.

Establish `h3` using `(h2.mul_const A).mul h1`. Establish `h4 : ((fun t : ℝ => NormedSpace.exp (t • Z.conjTranspose) * A) * fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A`. Use function extensionality and compare the values at `t`. Use `h t` as an intermediate fact. Rewrite `this` using `[← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial]`.

Conclude with `this`. Rewrite `h3` using `[h4]`. Establish `h5` using `h3.unique (hasDerivAt_const (0:ℝ) A)`. Simplify `h5` using `[NormedSpace.exp_zero]`.
-/
theorem lie_of_exp_preserves {n : ℕ} (Z A : Matrix (Fin n) (Fin n) ℂ)
    (h : ∀ t : ℝ, (NormedSpace.exp (t • Z)).conjTranspose * A * NormedSpace.exp (t • Z) = A) :
    Z.conjTranspose * A + A * Z = 0 := by
  letI := Matrix.linftyOpNormedRing (n := Fin n) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℝ) (α := ℂ)
  letI := Matrix.linftyOpNormedAlgebra (n := Fin n) (R := ℚ) (α := ℂ)
  have h1 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z)) (NormedSpace.exp ((0:ℝ) • Z) * Z) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Z 0
  have h2 : HasDerivAt (fun t : ℝ => NormedSpace.exp (t • Z.conjTranspose))
      (NormedSpace.exp ((0:ℝ) • Z.conjTranspose) * Z.conjTranspose) 0 :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) Z.conjTranspose 0
  have h3 := (h2.mul_const A).mul h1
  have h4 : ((fun t : ℝ => NormedSpace.exp (t • Z.conjTranspose) * A) *
      fun t : ℝ => NormedSpace.exp (t • Z)) = fun _ => A := by
    funext t
    have := h t
    rw [← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, star_trivial] at this
    exact this
  rw [h4] at h3
  have h5 := h3.unique (hasDerivAt_const (0:ℝ) A)
  simpa [NormedSpace.exp_zero] using h5

/- English proof (translation)
Establish `hg : Formalism.UG.cT (sigR w.Completion σ) (matHom w.Completion σ J g).1 * JR w.Completion J * (matHom w.Completion σ J g).1 = JR w.Completion J` using `g.2`. Establish `hJ : (JR w.Completion J).map (infEmb τ) = J.map τ.1`. Use extensionality with `i j`. Simplify using `only [JR, Matrix.map_apply]`. Express the relevant statement in the definitionally equal form `infEmb τ ((1 : w.Completion) ⊗ₜ[F] J i j) = _`.

Rewrite using `[infEmb_tmul, map_one, one_mul]`. Establish `hc : (Formalism.UG.cT (sigR w.Completion σ) (matHom w.Completion σ J g).1).map (infEmb τ) = ((matHom w.Completion σ J g).1.map (infEmb τ)).conjTranspose`. Use extensionality with `i j`. Simplify using `only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]`. Rewrite using `[← infEmb_sigR hσ]`.

Both sides reduce to the same expression. Establish `h` using `congrArg (fun M => M.map (infEmb τ)) hg`. Simplify using `only [Matrix.map_mul] at h`. Rewrite `h` using `[hJ, hc]`. Rewrite using `[GlobalTheory.Orb.archMat_apply]`.

Conclude with `h`.
-/
theorem archMat_preserves {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {w : InfinitePlace F}
    (τ : EmbOver E w) (g : GArch σ J w) :
    (GlobalTheory.Orb.archMat σ J τ g).conjTranspose * J.map τ.1 * GlobalTheory.Orb.archMat σ J τ g = J.map τ.1 := by
  have hg : Formalism.UG.cT (sigR w.Completion σ) (matHom w.Completion σ J g).1 * JR w.Completion J *
      (matHom w.Completion σ J g).1 = JR w.Completion J := g.2
  have hJ : (JR w.Completion J).map (infEmb τ) = J.map τ.1 := by
    ext i j
    simp only [JR, Matrix.map_apply]
    change infEmb τ ((1 : w.Completion) ⊗ₜ[F] J i j) = _
    rw [infEmb_tmul, map_one, one_mul]
  have hc : (Formalism.UG.cT (sigR w.Completion σ) (matHom w.Completion σ J g).1).map (infEmb τ) =
      ((matHom w.Completion σ J g).1.map (infEmb τ)).conjTranspose := by
    ext i j
    simp only [Formalism.UG.cT, Matrix.map_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply]
    rw [← infEmb_sigR hσ]
    rfl
  have h := congrArg (fun M => M.map (infEmb τ)) hg
  simp only [Matrix.map_mul] at h
  rw [hJ, hc] at h
  rw [GlobalTheory.Orb.archMat_apply]
  exact h

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ n J w τ Z y hy`. Use `lie_of_exp_preserves Z _ fun t => ?_` and prove the remaining obligations. Rewrite using `[← hy t]`. Conclude with `archMat_preserves hσ J τ (y t)`.
-/
theorem lie_of_archMat_eq_exp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (w : InfinitePlace F) (τ : EmbOver E w)
    (Z : Matrix (Fin n) (Fin n) ℂ) (y : ℝ → GArch σ J w),
    (∀ t : ℝ, GlobalTheory.Orb.archMat σ J τ (y t) = NormedSpace.exp (t • Z)) →
    Z.conjTranspose * J.map τ.1 + J.map τ.1 * Z = 0 := by
  intro F E _ _ _ _ _ σ hσ n J w τ Z y hy
  refine lie_of_exp_preserves Z _ fun t => ?_
  rw [← hy t]
  exact archMat_preserves hσ J τ (y t)

end GlobalTheory.ThK.OneParamLie
