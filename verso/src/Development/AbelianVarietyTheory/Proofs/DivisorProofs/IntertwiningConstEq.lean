import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.EisRes.CReduce

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP`. Take `⟨hCM, -, hJ, -, hW, -, hI⟩` from `hS`. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_sigma hCM`. Establish `h1 : h 1 = 1`. Establish `e` using `hI.2 1 1 (by simp) 1 (one_mem _)`.

Rewrite `e` using `[mul_one, map_one]`. Simplify using `using e`. Use `set xv : Fin n → E := fun i => X i 0 with hxv`. Use `set yv : Fin n → E := fun i => Y i 0 with hyv`. Establish `gram : ∀ (A B : Matrix (Fin n) (Fin (r + 1)) E), (Formalism.UG.cT (σ : E →+* E) A * J * B) 0 0 = Formalism.UG.hform (σ : E →+* E) J (fun i => A i 0) (fun i => B i 0)`.

Introduce `A B`. Simplify using `only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Establish `hxx : Formalism.UG.hform (σ : E →+* E) J xv xv = 0` using `by rw [← gram, hW.xx]; rfl`. Establish `hyy : Formalism.UG.hform (σ : E →+* E) J yv yv = 0` using `by rw [← gram, hW.yy]; rfl`.

Establish `hxy : Formalism.UG.hform (σ : E →+* E) J xv yv = 1` using `by rw [← gram, hW.xy]; rfl`. Take `⟨g, hg, hgy⟩` from `GlobalTheory.WittTransitivity.exists_reflection (σ : E →+* E) J hσ hJ.1 (isUnit_iff_ne_zero.2 hJ.2) yv xv (by rw [hyy, hxx]) (by rw [hyy, hxy, zero_sub]; exact isUnit_one.neg)`. Establish `hmem : Formalism.UG.bc (inclR (AF F)) g ∈ HR (AF F) σ J`. Establish `hx' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J` using `hg`. Establish `hs : ∀ y : E, sigR (AF F) σ (inclR (AF F) y) = inclR (AF F) (σ y)`.

Introduce `y`. Use `show sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] y) = (1 : AF F) ⊗ₜ[F] σ y`. Simplify using `[sigR]`. Establish `hc : Formalism.UG.cT (sigR (AF F) σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (AF F))) = (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (AF F))`. Use extensionality with `i j`.

Simplify using `only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]`. Conclude with `hs _`. Use `show Formalism.UG.cT (sigR (AF F) σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (AF F))) * J.map (inclR (AF F)) * (g : Matrix (Fin n) (Fin n) E).map (inclR (AF F)) = J.map (inclR (AF F))`. Rewrite using `[hc, ← Matrix.map_mul, ← Matrix.map_mul, hx']`. Set `w : GAd σ J` to `⟨Formalism.UG.bc (inclR (AF F)) g, hmem⟩`.

Establish `hwrat : w ∈ ratPts σ J` using `Subgroup.mem_subgroupOf.2 ⟨g, hg, rfl⟩`. Establish `hgY : (g : Matrix (Fin n) (Fin n) E) * col0 Y = col0 X`. Use extensionality with `i j`. Establish `e` using `congrFun hgy i`. Simplify using `only [Matrix.mulVec, dotProduct, hyv, hxv] at e`.

Simplify using `only [col0, Matrix.mul_apply, Matrix.submatrix_apply, id]`. Conclude with `e`. Establish `hwY : (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X)` using `by show (g : Matrix (Fin n) (Fin n) E).map (inclR (AF F)) * (col0 Y).map (inclR (AF F)) = (col0 X).map (inclR (AF F))`. Rewrite using `[← Matrix.map_mul, hgY]`. Establish `hC : GlobalTheory.UAut.IsIsoCols σ J (col0 X)`.

Establish `e : col0 X = X.submatrix id (Fin.castLE (show 1 ≤ r + 1 by omega))`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim j 0]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ _`. Use `haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC`. Take `⟨μ, 𝓕, hμ, h𝓕, h1𝓕⟩` from `GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad hCM hJ hC)`. Use `⟨w, hwrat, hwY, μ, 𝓕, hμ, h𝓕, h1𝓕, fun s hs => ?_⟩` and prove the remaining obligations. Establish `e` using `(hP.2.1 w hwrat hwY μ 𝓕 hμ h𝓕 h1𝓕 s hs 1).2`.

Simplify using `only [mul_one, h1, Complex.ofReal_one, Complex.one_cpow] at e`. Conclude with `e.symm`.
-/
theorem intertwiningConst_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ) (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
    HidaSetting σ J X Y L a h → EisensteinHyp σ J (col0 X) (col0 Y) h Eis c →
    ∃ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) ∧
      ∃ (μ : Measure (unipRad σ J (col0 X))) (𝓕 : Set (unipRad σ J (col0 X))), μ.IsHaarMeasure ∧
        IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J (col0 X))) 𝓕 μ ∧ μ 𝓕 = 1 ∧
        ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re →
          c s = ∫ u : unipRad σ J (col0 X), (h (w * u) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ := by
  intro F E _ _ _ _ _ σ n J r X Y L a h Eis c hS hP
  obtain ⟨hCM, -, hJ, -, hW, -, hI⟩ := hS
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM

  have h1 : h 1 = 1 := by
    have e := hI.2 1 1 (by simp) 1 (one_mem _)
    rw [mul_one, map_one] at e
    simpa using e

  set xv : Fin n → E := fun i => X i 0 with hxv
  set yv : Fin n → E := fun i => Y i 0 with hyv
  have gram : ∀ (A B : Matrix (Fin n) (Fin (r + 1)) E),
      (Formalism.UG.cT (σ : E →+* E) A * J * B) 0 0 = Formalism.UG.hform (σ : E →+* E) J (fun i => A i 0) (fun i => B i 0) := by
    intro A B
    simp only [Formalism.UG.hform, Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hxx : Formalism.UG.hform (σ : E →+* E) J xv xv = 0 := by rw [← gram, hW.xx]; rfl
  have hyy : Formalism.UG.hform (σ : E →+* E) J yv yv = 0 := by rw [← gram, hW.yy]; rfl
  have hxy : Formalism.UG.hform (σ : E →+* E) J xv yv = 1 := by rw [← gram, hW.xy]; rfl
  obtain ⟨g, hg, hgy⟩ := GlobalTheory.WittTransitivity.exists_reflection (σ : E →+* E) J hσ hJ.1
    (isUnit_iff_ne_zero.2 hJ.2) yv xv (by rw [hyy, hxx]) (by rw [hyy, hxy, zero_sub]; exact isUnit_one.neg)
  have hmem : Formalism.UG.bc (inclR (AF F)) g ∈ HR (AF F) σ J := by
    have hx' : Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E) * J * (g : Matrix (Fin n) (Fin n) E) = J := hg
    have hs : ∀ y : E, sigR (AF F) σ (inclR (AF F) y) = inclR (AF F) (σ y) := by
      intro y
      show sigR (AF F) σ ((1 : AF F) ⊗ₜ[F] y) = (1 : AF F) ⊗ₜ[F] σ y
      simp [sigR]
    have hc : Formalism.UG.cT (sigR (AF F) σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (AF F))) =
        (Formalism.UG.cT (σ : E →+* E) (g : Matrix (Fin n) (Fin n) E)).map (inclR (AF F)) := by
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact hs _
    show Formalism.UG.cT (sigR (AF F) σ) ((g : Matrix (Fin n) (Fin n) E).map (inclR (AF F))) *
        J.map (inclR (AF F)) * (g : Matrix (Fin n) (Fin n) E).map (inclR (AF F)) = J.map (inclR (AF F))
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hx']
  let w : GAd σ J := ⟨Formalism.UG.bc (inclR (AF F)) g, hmem⟩
  have hwrat : w ∈ ratPts σ J := Subgroup.mem_subgroupOf.2 ⟨g, hg, rfl⟩
  have hgY : (g : Matrix (Fin n) (Fin n) E) * col0 Y = col0 X := by
    ext i j
    have e := congrFun hgy i
    simp only [Matrix.mulVec, dotProduct, hyv, hxv] at e
    simp only [col0, Matrix.mul_apply, Matrix.submatrix_apply, id]
    exact e
  have hwY : (matHom _ σ J w).1 * adMat F (col0 Y) = adMat F (col0 X) := by
    show (g : Matrix (Fin n) (Fin n) E).map (inclR (AF F)) * (col0 Y).map (inclR (AF F)) = (col0 X).map (inclR (AF F))
    rw [← Matrix.map_mul, hgY]

  have hC : GlobalTheory.UAut.IsIsoCols σ J (col0 X) := by
    have e : col0 X = X.submatrix id (Fin.castLE (show 1 ≤ r + 1 by omega)) := by
      ext i j
      rw [Subsingleton.elim j 0]
      rfl
    rw [e]
    exact GlobalTheory.UAut.isIsoCols_of_isWittFrame hW hσ hJ _
  haveI := GlobalTheory.UAut.locallyCompact_unipRad hCM hJ hC
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1𝓕⟩ := GlobalTheory.UAut.exists_mass_one (GlobalTheory.UAut.cocompact_unipRad hCM hJ hC)
  refine ⟨w, hwrat, hwY, μ, 𝓕, hμ, h𝓕, h1𝓕, fun s hs => ?_⟩
  have e := (hP.2.1 w hwrat hwY μ 𝓕 hμ h𝓕 h1𝓕 s hs 1).2
  simp only [mul_one, h1, Complex.ofReal_one, Complex.one_cpow] at e
  exact e.symm

end GlobalTheory.EisRes.CReduce
