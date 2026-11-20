import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.KernelsMatrix
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.AssemblyAnalytic
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Assembly
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFundamentalDomainMeanNormSqThetaChar
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsUnitOfLagrangian
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.CoordSiegel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaHolomorphic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

namespace GlobalTheory.CompanionTheory.NForm

open Matrix

/- English proof (translation)
Simplify using `only [mulVec_single_one, hermForm]`. Simplify using `[Matrix.mul_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, col_apply]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.
-/
private theorem hermForm_cols {g : ℕ} (N P Q : Matrix (Fin g) (Fin g) ℂ) (i j : Fin g) :
    hermForm N (P *ᵥ Pi.single i 1) (Q *ᵥ Pi.single j 1) =
      (Pᵀ * N * Q.map (starRingEnd ℂ)) i j := by
  simp only [mulVec_single_one, hermForm]
  simp [Matrix.mul_apply, dotProduct, mulVec, Finset.sum_mul, Finset.mul_sum, mul_assoc, col_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem re_of_real_add {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) (i j : Fin g) :
    ((B.map (fun x : ℝ => (x : ℂ)) + Complex.I • C.map (fun x : ℝ => (x : ℂ))) i j).re = B i j := by
  simp

/- English proof (translation)
Establish `: (periodMatrix X Y).map Complex.im = Y` using `by ext i j; simp [periodMatrix]`. Rewrite using `[GlobalTheory.CanTh.imInv, this]`.
-/
private theorem imInv_periodMatrix {g : ℕ} (X Y : Matrix (Fin g) (Fin g) ℝ) :
    GlobalTheory.CanTh.imInv (periodMatrix X Y) = Y⁻¹.map (fun x : ℝ => (x : ℂ)) := by
  have : (periodMatrix X Y).map Complex.im = Y := by ext i j; simp [periodMatrix]
  rw [GlobalTheory.CanTh.imInv, this]

/- English proof (translation)
The claim follows from `Matrix.map_mul (f := Complex.ofRealHom)`.
-/
private theorem map_ofReal_mul {g : ℕ} (B C : Matrix (Fin g) (Fin g) ℝ) :
    (B * C).map (fun x : ℝ => (x : ℂ)) =
      B.map (fun x : ℝ => (x : ℂ)) * C.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

/- English proof (translation)
Establish `hYs : Yᵀ = Y`. Use extensionality with `i j`. Simplify using `using hY.isHermitian.apply i j`. Establish `hXs : Xᵀ = X` using `hX`. Establish `hu : IsUnit Y.det` using `(Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit`.

Establish `hYY : Y * Y⁻¹ * Y = Y` using `by rw [mul_nonsing_inv _ hu, Matrix.one_mul]`. Use `set c : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℂ := fun B => B.map (fun x : ℝ => (x : ℂ)) with hc`. Establish `hτ : periodMatrix X Y = c X + Complex.I • c Y` using `rfl`. Establish `hτt : (periodMatrix X Y)ᵀ = c X + Complex.I • c Y`. Rewrite using `[hτ, transpose_add, transpose_smul]`.

Establish `: ∀ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ = B → (c B)ᵀ = c B` using `fun B hB => by`. Rewrite using `[hc]`. Simplify using `only`. Rewrite using `[← transpose_map, hB]`. Rewrite using `[this X hXs, this Y hYs]`.

Establish `hτc : (periodMatrix X Y).map (starRingEnd ℂ) = c X - Complex.I • c Y`. Use extensionality with `i j`. Simplify using `[periodMatrix, hc, Complex.ext_iff]`. Establish `h1c : (1 : Matrix (Fin g) (Fin g) ℂ).map (starRingEnd ℂ) = 1`. Apply the tactic sequence `ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]`.

Establish `mm : ∀ B C, c (B * C) = c B * c C` using `map_ofReal_mul`. Use extensionality with `α β`. Apply the tactic sequence `rcases α with i | i <;> rcases β with j | j <;>`. Simplify using `only [of_apply, Sum.elim_inl, Sum.elim_inr, hermForm_cols, imInv_periodMatrix, siegelGram, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_one, h1c, hτt, hτc, Matrix.one_mul, Matrix.mul_one]`. Simplify using the standard rewrite rules.

Establish `: (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) = c (Y⁻¹ * X) + Complex.I • c (-(Y⁻¹ * Y))`. Establish `hneg : ∀ B, c (-B) = -c B` using `fun B => by ext i j; simp [hc]`. Express the relevant statement in the definitionally equal form `c Y⁻¹ * _ = _`. Rewrite using `[hneg, mm, mm, Matrix.mul_sub, Matrix.mul_smul, smul_neg, sub_eq_add_neg]`. Rewrite using `[this]`.

Conclude with `re_of_real_add _ _ i j`. Establish `: (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) = c (X * Y⁻¹) + Complex.I • c (Y * Y⁻¹)`. Simplify using `[hc, Matrix.add_mul, map_ofReal_mul]`. Rewrite using `[this]`. Conclude with `re_of_real_add _ _ i j`.

Establish `: (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) = c (Y + X * Y⁻¹ * X) + Complex.I • c (Y * Y⁻¹ * X - X * Y⁻¹ * Y)`. Establish `e1 : c (Y + X * Y⁻¹ * X) = c (Y * Y⁻¹ * Y) + c (X * Y⁻¹ * X)`. Rewrite using `[hYY]`. Use extensionality with `i j`. Simplify using `[hc]`.

Establish `e2 : c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) = c (Y * Y⁻¹ * X) - c (X * Y⁻¹ * Y)`. Use extensionality with `i j`. Simplify using `[hc]`. Rewrite using `[e1, e2]`. Simplify using `only [mm]`.

Express the relevant statement in the definitionally equal form `_ = _ + _`. Establish `hI : ∀ N : Matrix (Fin g) (Fin g) ℂ, Complex.I • (Complex.I • N) = -N` using `fun N => by`. Rewrite using `[smul_smul, Complex.I_mul_I]`. Simplify using the standard rewrite rules. Simplify using `only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, hI]`.

Normalize the expressions using the abelian group laws. Rewrite using `[this]`. Use `re_of_real_add (Y + X * Y⁻¹ * X) (Y * Y⁻¹ * X - X * Y⁻¹ * Y) i j` as an intermediate fact. Simplify `this` using `[hc]`.
-/
theorem gram_eq_siegelGram {g : ℕ} {X Y : Matrix (Fin g) (Fin g) ℝ} (hX : X.IsSymm) (hY : Y.PosDef) :
    (Matrix.of fun α β : Fin g ⊕ Fin g =>
      (hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y))
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) α)
        (Sum.elim (fun i => (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1)
          (fun i => periodMatrix X Y *ᵥ Pi.single i 1) β)).re) = siegelGram X Y := by
  have hYs : Yᵀ = Y := by
    ext i j
    simpa using hY.isHermitian.apply i j
  have hXs : Xᵀ = X := hX
  have hu : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det _).1 hY.isUnit
  have hYY : Y * Y⁻¹ * Y = Y := by rw [mul_nonsing_inv _ hu, Matrix.one_mul]
  set c : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℂ := fun B => B.map (fun x : ℝ => (x : ℂ)) with hc
  have hτ : periodMatrix X Y = c X + Complex.I • c Y := rfl
  have hτt : (periodMatrix X Y)ᵀ = c X + Complex.I • c Y := by
    rw [hτ, transpose_add, transpose_smul]
    have : ∀ B : Matrix (Fin g) (Fin g) ℝ, Bᵀ = B → (c B)ᵀ = c B := fun B hB => by
      rw [hc]; simp only; rw [← transpose_map, hB]
    rw [this X hXs, this Y hYs]
  have hτc : (periodMatrix X Y).map (starRingEnd ℂ) = c X - Complex.I • c Y := by
    ext i j; simp [periodMatrix, hc, Complex.ext_iff]
  have h1c : (1 : Matrix (Fin g) (Fin g) ℂ).map (starRingEnd ℂ) = 1 := by
    ext i j; by_cases h : i = j <;> simp [Matrix.one_apply, h]
  have mm : ∀ B C, c (B * C) = c B * c C := map_ofReal_mul
  ext α β
  rcases α with i | i <;> rcases β with j | j <;>
    simp only [of_apply, Sum.elim_inl, Sum.elim_inr, hermForm_cols, imInv_periodMatrix, siegelGram,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂, transpose_one, h1c, hτt, hτc,
      Matrix.one_mul, Matrix.mul_one]
  · simp
  · have : (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y⁻¹ * X) + Complex.I • c (-(Y⁻¹ * Y)) := by
      have hneg : ∀ B, c (-B) = -c B := fun B => by ext i j; simp [hc]
      change c Y⁻¹ * _ = _
      rw [hneg, mm, mm, Matrix.mul_sub, Matrix.mul_smul, smul_neg, sub_eq_add_neg]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) =
        c (X * Y⁻¹) + Complex.I • c (Y * Y⁻¹) := by
      simp [hc, Matrix.add_mul, map_ofReal_mul]
    rw [this]; exact re_of_real_add _ _ i j
  · have : (c X + Complex.I • c Y) * (Y⁻¹.map (fun x : ℝ => (x : ℂ))) * (c X - Complex.I • c Y) =
        c (Y + X * Y⁻¹ * X) + Complex.I • c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) := by
      have e1 : c (Y + X * Y⁻¹ * X) = c (Y * Y⁻¹ * Y) + c (X * Y⁻¹ * X) := by
        rw [hYY]; ext i j; simp [hc]
      have e2 : c (Y * Y⁻¹ * X - X * Y⁻¹ * Y) = c (Y * Y⁻¹ * X) - c (X * Y⁻¹ * Y) := by
        ext i j; simp [hc]
      rw [e1, e2]
      simp only [mm]
      change _ = _ + _
      have hI : ∀ N : Matrix (Fin g) (Fin g) ℂ, Complex.I • (Complex.I • N) = -N := fun N => by
        rw [smul_smul, Complex.I_mul_I]; simp
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_add, hI]
      abel
    rw [this]
    have := re_of_real_add (Y + X * Y⁻¹ * X) (Y * Y⁻¹ * X - X * Y⁻¹ * Y) i j
    simpa [hc] using this

/- English proof (translation)
Introduce `g Hm v hH hpos hJ`. Use `set A : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inl j) i with hA`. Use `set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inr j) i with hF`. Use `set τ : Matrix (Fin g) (Fin g) ℂ := A⁻¹ * F with hτ`. Take `⟨hu, hs, hp, hform⟩` from `GlobalTheory.HolTheta.normal_form Hm (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) hH hpos (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inl k)) (fun j k => by simpa [Matrix.J] using hJ (Sum.inr j) (Sum.inr k)) (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) …`.

Establish `hPer : periodMatrix (τ.map Complex.re) (τ.map Complex.im) = τ`. Apply the tactic sequence `ext i j; apply Complex.ext <;> simp [periodMatrix]`. Establish `hXs : (τ.map Complex.re).IsSymm`. Use extensionality with `i j`. Simplify using `using congrArg Complex.re (hs.apply i j)`.

Establish `he : ∀ i, A⁻¹ *ᵥ v (Sum.inl i) = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1` using `fun i => by`. Establish `: v (Sum.inl i) = A *ᵥ Pi.single i 1` using `by ext k; simp [hA]`. Rewrite using `[this, mulVec_mulVec, nonsing_inv_mul A hu]`. Establish `hf : ∀ i, A⁻¹ *ᵥ v (Sum.inr i) = τ *ᵥ Pi.single i 1` using `fun i => by`. Establish `: v (Sum.inr i) = F *ᵥ Pi.single i 1` using `by ext k; simp [hF]`.

Rewrite using `[this, mulVec_mulVec]`. Use `⟨A⁻¹, τ.map Complex.re, τ.map Complex.im, Matrix.isUnit_nonsing_inv_det A hu, hXs, hp, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `z w`. Rewrite using `[hPer]`. Conclude with `hform z w`.

Introduce `i`. Rewrite using `[he, one_mulVec]`. Introduce `i`. Rewrite using `[hPer]`. Conclude with `hf i`.

Rewrite using `[← gram_eq_siegelGram hXs hp]`. Use extensionality with `α β`. Rewrite using `[hPer]`. Simplify using `only [of_apply]`. Rewrite using `[hform]`.

Apply the tactic sequence `rcases α with i | i <;> rcases β with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, he, hf]`.
-/
theorem normal_form_gram : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (v : Fin g ⊕ Fin g → Fin g → ℂ),
    Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) →
    (∀ α β, (hermForm Hm (v α) (v β)).im = Matrix.J (Fin g) ℝ α β) →
    ∃ (h : Matrix (Fin g) (Fin g) ℂ) (X Y : Matrix (Fin g) (Fin g) ℝ),
      IsUnit h.det ∧ X.IsSymm ∧ Y.PosDef ∧
      (∀ z w, hermForm Hm z w = hermForm (GlobalTheory.CanTh.imInv (periodMatrix X Y)) (h.mulVec z) (h.mulVec w)) ∧
      (∀ i, h.mulVec (v (Sum.inl i)) = Pi.single i 1) ∧
      (∀ i, h.mulVec (v (Sum.inr i)) = (periodMatrix X Y).mulVec (Pi.single i 1)) ∧
      (Matrix.of fun α β => (hermForm Hm (v α) (v β)).re) = siegelGram X Y := by
  intro g Hm v hH hpos hJ
  set A : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inl j) i with hA
  set F : Matrix (Fin g) (Fin g) ℂ := Matrix.of fun i j => v (Sum.inr j) i with hF
  set τ : Matrix (Fin g) (Fin g) ℂ := A⁻¹ * F with hτ
  obtain ⟨hu, hs, hp, hform⟩ := GlobalTheory.HolTheta.normal_form Hm (fun j => v (Sum.inl j)) (fun j => v (Sum.inr j)) hH hpos
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inl k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inr j) (Sum.inr k))
    (fun j k => by simpa [Matrix.J] using hJ (Sum.inl j) (Sum.inr k)) hA hτ
  have hPer : periodMatrix (τ.map Complex.re) (τ.map Complex.im) = τ := by
    ext i j; apply Complex.ext <;> simp [periodMatrix]
  have hXs : (τ.map Complex.re).IsSymm := by
    ext i j; simpa using congrArg Complex.re (hs.apply i j)
  have he : ∀ i, A⁻¹ *ᵥ v (Sum.inl i) = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inl i) = A *ᵥ Pi.single i 1 := by ext k; simp [hA]
    rw [this, mulVec_mulVec, nonsing_inv_mul A hu]
  have hf : ∀ i, A⁻¹ *ᵥ v (Sum.inr i) = τ *ᵥ Pi.single i 1 := fun i => by
    have : v (Sum.inr i) = F *ᵥ Pi.single i 1 := by ext k; simp [hF]
    rw [this, mulVec_mulVec]
  refine ⟨A⁻¹, τ.map Complex.re, τ.map Complex.im, Matrix.isUnit_nonsing_inv_det A hu, hXs, hp, ?_, ?_, ?_, ?_⟩
  · intro z w; rw [hPer]; exact hform z w
  · intro i; rw [he, one_mulVec]
  · intro i; rw [hPer]; exact hf i
  · rw [← gram_eq_siegelGram hXs hp]
    ext α β
    rw [hPer]
    simp only [of_apply]
    rw [hform]
    rcases α with i | i <;> rcases β with j | j <;> simp only [Sum.elim_inl, Sum.elim_inr, he, hf]

end GlobalTheory.CompanionTheory.NForm
