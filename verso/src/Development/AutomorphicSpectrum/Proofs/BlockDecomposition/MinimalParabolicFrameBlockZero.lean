import Mathlib
import Development.WeilBound.ThetaLifts.Reductions.SiegelCore
import Development.WeilBound.ThetaLifts.Reductions.SiegelPar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GoodConstOfAniso
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumFrameIdem

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RapidDecay

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]`. Apply the tactic sequence `rcases eq_or_ne m a with rfl | ha <;> rcases eq_or_ne i b with rfl | hb <;>`. Simplify using `[*, Finset.sum_ite_eq, Finset.sum_ite_eq']`.
-/
theorem single_mul_mul_single_eq_zero {R : Type} [CommRing R] {r : ℕ} {B : Matrix (Fin r) (Fin r) R}
    {m i : Fin r} (h : B m i = 0) :
    (single m m (1 : R) : Matrix (Fin r) (Fin r) R) * B * single i i (1 : R) = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  rcases eq_or_ne m a with rfl | ha <;> rcases eq_or_ne i b with rfl | hb <;>
    simp [*, Finset.sum_ite_eq, Finset.sum_ite_eq']

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [Matrix.map_apply, Matrix.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem map_single_one_eq {E : Type} [Field E] {r : ℕ} (f : E →+* ℂ) (i : Fin r) :
    (single i i (1 : E) : Matrix (Fin r) (Fin r) E).map f = single i i (1 : ℂ) := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = A * P * B * single i i (1 : ℂ) * Q := by`. Rewrite using `[hG]`. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = 0 := by rw [h, Matrix.zero_mul]`.
-/
theorem mul_mul_frameLine {n r : ℕ} {A G : Matrix (Fin n) (Fin n) ℂ} {P : Matrix (Fin n) (Fin r) ℂ}
    {B : Matrix (Fin r) (Fin r) ℂ} (hG : G * P = P * B) (Q : Matrix (Fin r) (Fin n) ℂ) (i : Fin r)
    (h : A * P * B * single i i (1 : ℂ) = 0) :
    A * G * (P * single i i (1 : ℂ) * Q) = 0 := by
  calc A * G * (P * single i i (1 : ℂ) * Q) = A * (G * P) * single i i (1 : ℂ) * Q := by
        simp only [Matrix.mul_assoc]
    _ = A * P * B * single i i (1 : ℂ) * Q := by
        rw [hG]; simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.zero_mul]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ r X Y hW g hg w τ s α β hα hβ`. Take `⟨-, -, -, hστ⟩` from `hCM`. Establish `hσσ : ∀ x, σ (σ x) = x` using `fun x => τ.1.injective (by rw [hστ, hστ, star_star])`. Establish `cT_mul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E), cT (σ : E →+* E) (A * B) = cT (σ : E →+* E) B * cT (σ : E →+* E) A`. Introduce `a b c A B`.

Simplify using `[Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]`. Establish `cT_cT : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A`. Introduce `a b A`. Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hσσ]`.

Establish `cT_J : cT (σ : E →+* E) J = J`. Use extensionality with `i j`. Simplify `hJ.1 i j` using `[Formalism.UG.cT]`. Establish `cT_one : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1`. Use extensionality with `i j`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `[Formalism.UG.cT]`. Simplify using `[Formalism.UG.cT, Matrix.one_apply, hij, Ne.symm hij]`. Establish `hyx : cT (σ : E →+* E) Y * (J * X) = 1`.

Establish `h` using `congrArg (cT (σ : E →+* E)) hW.xy`. Rewrite `h` using `[cT_mul, cT_mul, cT_cT, cT_J, cT_one]`. Conclude with `h`. Establish `hxx : cT (σ : E →+* E) X * (J * X) = 0`. Rewrite using `[← Matrix.mul_assoc]`.

Conclude with `hW.xx`. Take `⟨B, hBt, hB⟩` from `hg`. Set `φ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E →+* ℂ` to `(GlobalTheory.AdelicU.infEmb τ).comp (GlobalTheory.AdelicU.compInf F E w)`. Establish `hφ : ∀ x : E, φ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) = τ.1 x`. Introduce `x`.

Simplify using `[φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]`. Establish `hAd : (GlobalTheory.SiegelSet.adMat F X).map φ = X.map τ.1`. Use extensionality with `i j`. Simplify using `only [GlobalTheory.SiegelSet.adMat, Matrix.map_apply]`. Conclude with `hφ (X i j)`.

Establish `hA : archMat σ J τ (projArch σ J w g) = ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map φ`. Use extensionality with `i j`. Simplify using `[GlobalTheory.Orb.archMat, GlobalTheory.AdelicU.matHom_projArch, Formalism.UG.bc, φ]`. Establish `hG : archMat σ J τ (projArch σ J w g) * X.map τ.1 = X.map τ.1 * B.map φ`. Rewrite using `[hA, ← hAd, ← Matrix.map_mul, hB, Matrix.map_mul]`.

Break down `β with _ | (i | i)` into its components or cases. Express the relevant statement in the definitionally equal form `1 = 2 at hβ`. Conclude with `absurd hβ (by decide)`. Distinguish the cases in `hi : i ≤ s`. Establish `hframe : (frameIdem (σ : E →+* E) J X Y (some (Sum.inl i))).map τ.1 = X.map τ.1 * single i i (1 : ℂ) * (cT (σ : E →+* E) Y * J).map τ.1`.

Express the relevant statement in the definitionally equal form `(X * single i i (1 : E) * (cT (σ : E →+* E) Y * J)).map τ.1 = _`. Simplify using `only [Matrix.map_mul, map_single_one_eq]`. Rewrite using `[hframe]`. Apply `mul_mul_frameLine hG` to reduce the goal to its premises. Rewrite using `[← Matrix.map_mul]`.

Break down `α with _ | (j | j)` into its components or cases. Establish `h0 : frameIdem (σ : E →+* E) J X Y none * X = 0`. Express the relevant statement in the definitionally equal form `(1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) * X = 0`. Simplify using `only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx, Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]`. Rewrite using `[h0]`.

Simplify using the standard rewrite rules. Establish `hj : ¬ j ≤ s`. Introduce `h`. Express the relevant statement in the definitionally equal form `(if j ≤ s then 2 else 1) < 2 at hα`. Rewrite `hα` using `[if_pos h]`.

Conclude with `absurd hα (by decide)`. Establish `hij : i < j` using `lt_of_le_of_lt hi (not_le.mp hj)`. Establish `hBji : (B.map φ) j i = 0`. Simplify using `[Matrix.map_apply, hBt hij]`. Establish `h1 : frameIdem (σ : E →+* E) J X Y (some (Sum.inl j)) * X = X * single j j (1 : E)`.

Express the relevant statement in the definitionally equal form `X * single j j (1 : E) * (cT (σ : E →+* E) Y * J) * X = _`. Simplify using `only [Matrix.mul_assoc, hyx, Matrix.mul_one]`. Rewrite using `[h1, Matrix.map_mul, map_single_one_eq, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (single j j (1 : ℂ)), single_mul_mul_single_eq_zero hBji, Matrix.mul_zero]`. Establish `h2 : frameIdem (σ : E →+* E) J X Y (some (Sum.inr j)) * X = 0`. Express the relevant statement in the definitionally equal form `Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) * X = 0`.

Simplify using `only [Matrix.mul_assoc, hxx, Matrix.mul_zero]`. Rewrite using `[h2]`. Simplify using the standard rewrite rules. Express the relevant statement in the definitionally equal form `(if i ≤ s then 2 else 1) = 2 at hβ`. Rewrite `hβ` using `[if_neg hi]`.

Conclude with `absurd hβ (by decide)`. Express the relevant statement in the definitionally equal form `(if i ≤ s then 0 else 1) = 2 at hβ`. Distinguish the cases in `hi : i ≤ s`. Rewrite `hβ` using `[if_pos hi]`. Conclude with `absurd hβ (by decide)`.

Rewrite `hβ` using `[if_neg hi]`. Conclude with `absurd hβ (by decide)`.
-/
theorem minPar_frame_block_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ g ∈ minPar σ J X, ∀ (w : InfinitePlace F) (τ : EmbOver E w) (s : Fin r) (α β : FrameIx r), frameLev s α < 2 → frameLev s β = 2 → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * archMat σ J τ (projArch σ J w g) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y hW g hg w τ s α β hα hβ
  obtain ⟨-, -, -, hστ⟩ := hCM
  have hσσ : ∀ x, σ (σ x) = x := fun x => τ.1.injective (by rw [hστ, hστ, star_star])
  have cT_mul : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) E) (B : Matrix (Fin b) (Fin c) E),
      cT (σ : E →+* E) (A * B) = cT (σ : E →+* E) B * cT (σ : E →+* E) A := by
    intro a b c A B
    simp [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]
  have cT_cT : ∀ {a b : ℕ} (A : Matrix (Fin a) (Fin b) E), cT (σ : E →+* E) (cT (σ : E →+* E) A) = A := by
    intro a b A
    ext i j
    simp [Formalism.UG.cT, hσσ]
  have cT_J : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [Formalism.UG.cT] using hJ.1 i j
  have cT_one : cT (σ : E →+* E) (1 : Matrix (Fin r) (Fin r) E) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [Formalism.UG.cT]
    · simp [Formalism.UG.cT, Matrix.one_apply, hij, Ne.symm hij]
  have hyx : cT (σ : E →+* E) Y * (J * X) = 1 := by
    have h := congrArg (cT (σ : E →+* E)) hW.xy
    rw [cT_mul, cT_mul, cT_cT, cT_J, cT_one] at h
    exact h
  have hxx : cT (σ : E →+* E) X * (J * X) = 0 := by
    rw [← Matrix.mul_assoc]
    exact hW.xx
  obtain ⟨B, hBt, hB⟩ := hg
  let φ : TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) E →+* ℂ :=
    (GlobalTheory.AdelicU.infEmb τ).comp (GlobalTheory.AdelicU.compInf F E w)
  have hφ : ∀ x : E, φ (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) x) = τ.1 x := by
    intro x
    simp [φ, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compInf, GlobalTheory.AdelicU.infEmb]
  have hAd : (GlobalTheory.SiegelSet.adMat F X).map φ = X.map τ.1 := by
    ext i j
    simp only [GlobalTheory.SiegelSet.adMat, Matrix.map_apply]
    exact hφ (X i j)
  have hA : archMat σ J τ (projArch σ J w g) =
      ((GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) σ J g : GL (Fin n) _) : Matrix (Fin n) (Fin n) _).map φ := by
    ext i j
    simp [GlobalTheory.Orb.archMat, GlobalTheory.AdelicU.matHom_projArch, Formalism.UG.bc, φ]
  have hG : archMat σ J τ (projArch σ J w g) * X.map τ.1 = X.map τ.1 * B.map φ := by
    rw [hA, ← hAd, ← Matrix.map_mul, hB, Matrix.map_mul]
  rcases β with _ | (i | i)
  · change 1 = 2 at hβ
    exact absurd hβ (by decide)
  · by_cases hi : i ≤ s
    · have hframe : (frameIdem (σ : E →+* E) J X Y (some (Sum.inl i))).map τ.1 =
          X.map τ.1 * single i i (1 : ℂ) * (cT (σ : E →+* E) Y * J).map τ.1 := by
        change (X * single i i (1 : E) * (cT (σ : E →+* E) Y * J)).map τ.1 = _
        simp only [Matrix.map_mul, map_single_one_eq]
      rw [hframe]
      apply mul_mul_frameLine hG
      rw [← Matrix.map_mul]
      rcases α with _ | (j | j)
      · have h0 : frameIdem (σ : E →+* E) J X Y none * X = 0 := by
          change (1 - X * (cT (σ : E →+* E) Y * J) - Y * (cT (σ : E →+* E) X * J)) * X = 0
          simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hyx, hxx,
            Matrix.mul_one, Matrix.mul_zero, sub_self, sub_zero]
        rw [h0]
        simp
      · have hj : ¬ j ≤ s := by
          intro h
          change (if j ≤ s then 2 else 1) < 2 at hα
          rw [if_pos h] at hα
          exact absurd hα (by decide)
        have hij : i < j := lt_of_le_of_lt hi (not_le.mp hj)
        have hBji : (B.map φ) j i = 0 := by
          simp [Matrix.map_apply, hBt hij]
        have h1 : frameIdem (σ : E →+* E) J X Y (some (Sum.inl j)) * X = X * single j j (1 : E) := by
          change X * single j j (1 : E) * (cT (σ : E →+* E) Y * J) * X = _
          simp only [Matrix.mul_assoc, hyx, Matrix.mul_one]
        rw [h1, Matrix.map_mul, map_single_one_eq, Matrix.mul_assoc, Matrix.mul_assoc,
          ← Matrix.mul_assoc (single j j (1 : ℂ)), single_mul_mul_single_eq_zero hBji, Matrix.mul_zero]
      · have h2 : frameIdem (σ : E →+* E) J X Y (some (Sum.inr j)) * X = 0 := by
          change Y * single j j (1 : E) * (cT (σ : E →+* E) X * J) * X = 0
          simp only [Matrix.mul_assoc, hxx, Matrix.mul_zero]
        rw [h2]
        simp
    · change (if i ≤ s then 2 else 1) = 2 at hβ
      rw [if_neg hi] at hβ
      exact absurd hβ (by decide)
  · change (if i ≤ s then 0 else 1) = 2 at hβ
    by_cases hi : i ≤ s
    · rw [if_pos hi] at hβ
      exact absurd hβ (by decide)
    · rw [if_neg hi] at hβ
      exact absurd hβ (by decide)

end GlobalTheory.CompanionTheory.RapidDecay

end
