import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

namespace GlobalTheory.CompanionTheory.RapidDecay

/- English proof (translation)
Establish `e : diagonal d * single i i (1 : ℂ) = d i • single i i (1 : ℂ)`. Use extensionality with `a b`. Distinguish the cases in `h : i = a`. Substitute `h` using the available equality. Simplify using `[Matrix.diagonal_mul, Matrix.single_apply]`.

Simplify using `[Matrix.diagonal_mul, Matrix.single_apply, h]`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.mul_assoc P, e, Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem mul_frameLine {n r : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    (Q : Matrix (Fin r) (Fin n) ℂ) {d : Fin r → ℂ} (hA : A * P = P * diagonal d) (i : Fin r) :
    A * (P * single i i (1 : ℂ) * Q) = d i • (P * single i i (1 : ℂ) * Q) := by
  have e : diagonal d * single i i (1 : ℂ) = d i • single i i (1 : ℂ) := by
    ext a b
    by_cases h : i = a
    · subst h
      simp [Matrix.diagonal_mul, Matrix.single_apply]
    · simp [Matrix.diagonal_mul, Matrix.single_apply, h]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.mul_assoc P, e, Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Use `congr 2`. Use extensionality with `a b`. Distinguish the cases in `h : a = i ∧ b = i`. Take `⟨rfl, rfl⟩` from `h`.

Simplify using the standard rewrite rules. Simplify using `[Matrix.single_apply, show ¬(i = a ∧ i = b) from fun q => h ⟨q.1.symm, q.2.symm⟩]`.
-/
theorem map_frameLine {E : Type} [Field E] {n r : ℕ} (f : E →+* ℂ) (P : Matrix (Fin n) (Fin r) E)
    (Q : Matrix (Fin r) (Fin n) E) (i : Fin r) :
    (P * single i i (1 : E) * Q).map f = P.map f * single i i (1 : ℂ) * Q.map f := by
  rw [Matrix.map_mul, Matrix.map_mul]
  congr 2
  ext a b
  by_cases h : a = i ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · simp [Matrix.single_apply, show ¬(i = a ∧ i = b) from fun q => h ⟨q.1.symm, q.2.symm⟩]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW t a ha _ w τ β`. Take `⟨h1, h2, h3⟩` from `ha.2 w τ`. Establish `yx : cT (σ : E →+* E) Y * J * X = 1`. Use `congrArg (cT (σ : E →+* E)) hW.xy` as an intermediate fact. Rewrite `this` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from Matrix.ext fun i j => sigma_sigma h _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis.

Break down `β with _ | i | i` into its components or cases. Establish `hV : (cT (σ : E →+* E) X * J) * frameIdem (σ : E →+* E) J X Y none = 0`. Simplify using `only [frameIdem, Matrix.mul_sub, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]`. Simplify using the standard rewrite rules.

Establish `hU : (cT (σ : E →+* E) Y * J) * frameIdem (σ : E →+* E) J X Y none = 0`. Simplify using `only [frameIdem, Matrix.mul_sub, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx]`. Simplify using the standard rewrite rules. Establish `col : ∀ (M : Matrix (Fin r) (Fin n) E), M * frameIdem (σ : E →+* E) J X Y none = 0 → ∀ j, M *ᵥ (fun k => frameIdem (σ : E →+* E) J X Y none k j) = 0` using `fun M hM j => by`.

Use function extensionality and compare the values at `i`. Conclude with `congrFun (congrFun hM i) j`. Establish `key : archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y none).map τ.1 = (frameIdem (σ : E →+* E) J X Y none).map τ.1`. Use extensionality with `i j`. Conclude with `congrFun (h3 _ (col _ hV j) (col _ hU j)) i`.

Simplify `key` using `[frameWt]`. Simplify using `only [frameIdem, frameWt]`. Rewrite using `[map_frameLine]`. Conclude with `mul_frameLine _ h1 i`. Simplify using `only [frameIdem, frameWt]`.

Rewrite using `[map_frameLine, Complex.ofReal_inv]`. Conclude with `mul_frameLine _ h2 i`.
-/
theorem torus_mul_frameIdem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (t : Fin r → ℝ) (a : GAd σ J), IsTorusElt σ J X Y t a → (∀ i, 0 < t i) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (β : FrameIx r), archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = ((frameWt t β : ℝ) : ℂ) • (frameIdem (σ : E →+* E) J X Y β).map τ.1 := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW t a ha _ w τ β
  obtain ⟨h1, h2, h3⟩ := ha.2 w τ
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, show cT (σ : E →+* E) (cT (σ : E →+* E) X) = X from
      Matrix.ext fun i j => sigma_sigma h _, GlobalTheory.UAut.cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  rcases β with _ | i | i
  · have hV : (cT (σ : E →+* E) X * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.xx, hW.xy]
      simp
    have hU : (cT (σ : E →+* E) Y * J) * frameIdem (σ : E →+* E) J X Y none = 0 := by
      simp only [frameIdem, Matrix.mul_sub, Matrix.mul_one]
      rw [← Matrix.mul_assoc _ X, ← Matrix.mul_assoc _ Y, hW.yy, yx]
      simp
    have col : ∀ (M : Matrix (Fin r) (Fin n) E), M * frameIdem (σ : E →+* E) J X Y none = 0 → ∀ j,
        M *ᵥ (fun k => frameIdem (σ : E →+* E) J X Y none k j) = 0 := fun M hM j => by
      funext i
      exact congrFun (congrFun hM i) j
    have key : archMat σ J τ (projArch σ J w a) * (frameIdem (σ : E →+* E) J X Y none).map τ.1 =
        (frameIdem (σ : E →+* E) J X Y none).map τ.1 := by
      ext i j
      exact congrFun (h3 _ (col _ hV j) (col _ hU j)) i
    simpa [frameWt] using key
  · simp only [frameIdem, frameWt]
    rw [map_frameLine]
    exact mul_frameLine _ h1 i
  · simp only [frameIdem, frameWt]
    rw [map_frameLine, Complex.ofReal_inv]
    exact mul_frameLine _ h2 i

end GlobalTheory.CompanionTheory.RapidDecay

end
