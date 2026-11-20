import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut

/- English proof (translation)
Use `⟨L * z * C, fun i j hij => ?_, ?_⟩` and prove the remaining obligations. Use `hz _ _ (hd i j hij)` as an intermediate fact. Rewrite `this` using `[he, he]`. Conclude with `(sandwich_eq_zero hL z j i).1 this`. Establish `h2 : (1 - C * L) * C = 0`.

Rewrite using `[Matrix.sub_mul, Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.one_mul, sub_self]`. Establish `h3 : ∀ j, (1 - C * L) * (z * ε (e j)) = 0` using `fun j => by`. Rewrite using `[← Matrix.one_mul (z * ε (e j)), ← h1, Finset.sum_mul, h1, Finset.mul_sum]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : w a = w (e j)`.

Take `⟨i, rfl⟩` from `hw a j h`. Rewrite using `[← Matrix.mul_assoc, he i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]`. Simplify using the standard rewrite rules. Rewrite using `[← Matrix.mul_assoc (ε a), hz _ _ h, Matrix.mul_zero]`. Establish `h4 : ∑ j, ε (e j) = C * L`.

Simplify using `only [he]`. Rewrite using `[← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]`. Establish `h5 : (1 - C * L) * (z * (C * L)) = 0` using `by conv_lhs => rw [← h4, Finset.mul_sum, Finset.mul_sum, h4]`. Conclude with `Finset.sum_eq_zero fun j _ => h3 j`. Establish `h6` using `congrArg (· * C) h5`.

Simplify using `only [Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.zero_mul] at h6`. Rewrite `h6` using `[Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]`. Rewrite using `[h6]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem exists_blockTriangular_of_keeps_weights {A ι : Type} [CommRing A] [Fintype ι] {n r : ℕ}
    {ε : ι → Matrix (Fin n) (Fin n) A} {w : ι → ℤ} (h1 : ∑ a, ε a = 1) {C : Matrix (Fin n) (Fin r) A}
    {L : Matrix (Fin r) (Fin n) A} (hL : L * C = 1) (e : Fin r → ι) (he : ∀ j, ε (e j) = C * single j j (1 : A) * L)
    {d : Fin r → ℕ} (hw : ∀ a j, w a = w (e j) → ∃ i, a = e i) (hd : ∀ i j, d j < d i → w (e i) ≠ w (e j))
    {z : Matrix (Fin n) (Fin n) A} (hz : ∀ a b, w a ≠ w b → ε a * z * ε b = 0) :
    ∃ B : Matrix (Fin r) (Fin r) A, B.BlockTriangular d ∧ z * C = C * B := by
  refine ⟨L * z * C, fun i j hij => ?_, ?_⟩
  · have := hz _ _ (hd i j hij)
    rw [he, he] at this
    exact (sandwich_eq_zero hL z j i).1 this
  · have h2 : (1 - C * L) * C = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 : ∀ j, (1 - C * L) * (z * ε (e j)) = 0 := fun j => by
      rw [← Matrix.one_mul (z * ε (e j)), ← h1, Finset.sum_mul, h1, Finset.mul_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases h : w a = w (e j)
      · obtain ⟨i, rfl⟩ := hw a j h
        rw [← Matrix.mul_assoc, he i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
        simp
      · rw [← Matrix.mul_assoc (ε a), hz _ _ h, Matrix.mul_zero]
    have h4 : ∑ j, ε (e j) = C * L := by
      simp only [he]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    have h5 : (1 - C * L) * (z * (C * L)) = 0 := by
      conv_lhs => rw [← h4, Finset.mul_sum, Finset.mul_sum, h4]
      exact Finset.sum_eq_zero fun j _ => h3 j
    have h6 := congrArg (· * C) h5
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.zero_mul] at h6
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h6
    rw [h6]
    simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM n J hJ r X Y d M hd _ _ xy g hg hg'`. Establish `hσ : ∀ x, σ (σ x) = x` using `sigma_sigma hCM`. Establish `cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A` using `fun A => Matrix.ext fun i j => hσ _`. Establish `yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1`. Use `congrArg (Formalism.UG.cT (σ : E →+* E)) xy` as an intermediate fact.

Rewrite `this` using `[Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc]`. Then use the resulting hypothesis. Use `set φ := inclR (F := F) (E := E) (AF F)`. Establish `m1 : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → L.map φ * C.map φ = 1` using `fun h => by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `h1 : ∑ a, fam (adjA σ J) (idemA (F` using `F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) a = 1 := by`. Rewrite using `[Fintype.sum_option]`.

Conclude with `sub_add_cancel _ _`. Establish `cs : ∀ j : Fin r, Formalism.UG.cT (σ : E →+* E) (single j j (1 : E)) = single j j (1 : E)` using `fun j => by`. Rewrite using `[Formalism.UG.cT, Matrix.map_single, transpose_single, map_one]`. Establish `eY : ∀ j, fam (adjA σ J) (idemA (F` using `F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) (some (.inr j)) = Y.map φ * single j j (1 : AF F ⊗[F] E) * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun j => by`. Rewrite using `[← idemA_eq]`.

Express the relevant statement in the definitionally equal form `adjA σ J (idemA X _ j) = _`. Rewrite using `[idemA, idemA, adjA_map, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, cs]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]`. Establish `kX : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * X.map φ = X.map φ * B` using `fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 yx) (fun j => some (.inl j)) (fun j => idemA_eq _ _ j) (by`.

Introduce and unpack `(_ | i | i) j h`. Use `hd j` as an intermediate fact. Simplify using `[wt] at h`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨i, rfl⟩`.

Use `hd j` as an intermediate fact. Use `hd i` as an intermediate fact. Simplify using `[wt] at h`. Use the proof step `omega)`. Use the proof step `(fun i j h => by simp [wt]; omega) hz`.

Establish `kY : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * Y.map φ = Y.map φ * B` using `fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 xy) (fun j => some (.inr j)) eY (by`. Introduce and unpack `(_ | i | i) j h`. Use `hd j` as an intermediate fact. Simplify using `[wt] at h`. Use linear arithmetic over natural numbers and integers.

Use `hd j` as an intermediate fact. Use `hd i` as an intermediate fact. Simplify using `[wt] at h`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨i, rfl⟩)`.

Use the proof step `(fun i j h => by simp [wt]; omega) hz`. Conclude with `⟨⟨kX hg, kX hg'⟩, kY hg, kY hg'⟩`.
-/
theorem mem_leviFlag_of_keeps_weights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ g : GAd σ J, (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g⁻¹).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → g ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y d M hd _ _ xy g hg hg'
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  set φ := inclR (F := F) (E := E) (AF F)
  have m1 : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → L.map φ * C.map φ = 1 :=
    fun h => by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ∑ a, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) a = 1 := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _
  have cs : ∀ j : Fin r, Formalism.UG.cT (σ : E →+* E) (single j j (1 : E)) = single j j (1 : E) := fun j => by
    rw [Formalism.UG.cT, Matrix.map_single, transpose_single, map_one]
  have eY : ∀ j, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) (some (.inr j)) =
      Y.map φ * single j j (1 : AF F ⊗[F] E) * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun j => by
    rw [← idemA_eq]
    change adjA σ J (idemA X _ j) = _
    rw [idemA, idemA, adjA_map, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, cs]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
  have kX : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * X.map φ = X.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 yx) (fun j => some (.inl j))
      (fun j => idemA_eq _ _ j)
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · exact ⟨i, rfl⟩
        · have := hd j; have := hd i; simp [wt] at h; omega)
      (fun i j h => by simp [wt]; omega) hz
  have kY : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * Y.map φ = Y.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 xy) (fun j => some (.inr j)) eY
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · have := hd j; have := hd i; simp [wt] at h; omega
        · exact ⟨i, rfl⟩)
      (fun i j h => by simp [wt]; omega) hz
  exact ⟨⟨kX hg, kX hg'⟩, kY hg, kY hg'⟩

end GlobalTheory.UAut
