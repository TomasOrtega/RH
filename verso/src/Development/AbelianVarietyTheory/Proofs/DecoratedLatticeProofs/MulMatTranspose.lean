import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRealCoord
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open NumberField Matrix Formalism.MainNotions.S GlobalTheory.CuspGeo GlobalTheory.ClassFin
open scoped Topology

noncomputable section

namespace GlobalTheory.CuspGeo.MulCoord

variable (I : AutInst)

def vecHom (y : I.Ginf) : (Fin I.n → I.E) →+ (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun := vec I y
  map_zero' := by
    funext v
    have h0 : (fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0 := by funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((0 : Fin I.n → I.E) i)) = 0
    rw [h0, mulVec_zero, mulVec_zero]
  map_add' u w := by
    funext v
    have h : (fun i => I.φ v ((u + w) i)) = (fun i => I.φ v (u i)) + fun i => I.φ v (w i) := by
      funext i; simp
    change uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v ((u + w) i)) =
      uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (u i)) + uMat (y v)⁻¹ *ᵥ ((I.P v)⁻¹ *ᵥ fun i => I.φ v (w i))
    rw [h, mulVec_add, mulVec_add]

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem vec_sum_zsmul {N : ℕ} (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (z : Fin N → ℤ) :
    vec I y (∑ k, z k • e k) = ∑ k, z k • vec I y (e k) := by
  calc vec I y (∑ k, z k • e k) = vecHom I y (∑ k, z k • e k) := rfl
    _ = ∑ k, vecHom I y (z k • e k) := map_sum _ _ _
    _ = ∑ k, z k • vecHom I y (e k) := by simp only [map_zsmul]
    _ = _ := rfl

/- English proof (translation)
Establish `h : (fun i => I.φ v ((a • u) i)) = I.φ v a • fun i => I.φ v (u i)`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Simplify using `only [vec, h, Matrix.mulVec_smul]`.
-/
theorem vec_smul (y : I.Ginf) (a : I.E) (u : Fin I.n → I.E) (v : InfinitePlace I.F) :
    vec I y (a • u) v = I.φ v a • vec I y u v := by
  have h : (fun i => I.φ v ((a • u) i)) = I.φ v a • fun i => I.φ v (u i) := by
    funext i; simp
  simp only [vec, h, Matrix.mulVec_smul]

def mulL (c : InfinitePlace I.F → ℂ) :
    (InfinitePlace I.F → Fin I.n → ℂ) →ₗ[ℝ] (InfinitePlace I.F → Fin I.n → ℂ) where
  toFun x := fun v i => c v * x v i
  map_add' x w := by
    funext v i; simp [mul_add]
  map_smul' r x := by
    funext v i; simp [Complex.real_smul]; ring

variable {I}

def mulMat {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) : Matrix (Fin N) (Fin N) ℝ :=
  LinearMap.toMatrix' (ρ.toLinearMap ∘ₗ mulL I c ∘ₗ ρ.symm.toLinearMap)

/- English proof (translation)
Simplify using `[mulMat, LinearMap.toMatrix'_mulVec]`.
-/
theorem mulMat_mulVec {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (c : InfinitePlace I.F → ℂ) (w : Fin N → ℝ) :
    mulMat ρ c *ᵥ w = ρ (mulL I c (ρ.symm w)) := by
  simp [mulMat, LinearMap.toMatrix'_mulVec]

/- English proof (translation)
Rewrite using `[mulMat_mulVec, mulMat_mulVec]`. Establish `hb : b = ρ (ρ.symm b)` using `(ρ.apply_symm_apply b).symm`. Establish `ha : a = ρ (ρ.symm a)` using `(ρ.apply_symm_apply a).symm`. Use `conv_lhs => rw [hb]`. Use `conv_rhs => rw [ha]`.

Rewrite using `[hρ, hρ]`. Use `Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [mulL, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def]`. Put the polynomial expressions in normal form.
-/
theorem mulMat_adj {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) (a b : Fin N → ℝ) :
    (mulMat ρ c *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (mulMat ρ (fun v => starRingEnd ℂ (c v)) *ᵥ b) := by
  rw [mulMat_mulVec, mulMat_mulVec]
  have hb : b = ρ (ρ.symm b) := (ρ.apply_symm_apply b).symm
  have ha : a = ρ (ρ.symm a) := (ρ.apply_symm_apply a).symm
  conv_lhs => rw [hb]
  conv_rhs => rw [ha]
  rw [hρ, hρ]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [mulL, LinearMap.coe_mk, AddHom.coe_mk, star_mul', Complex.star_def]
  ring_nf

/- English proof (translation)
Use extensionality with `i j`. Use `mulMat_adj ρ hρ c (Pi.single i 1) (Pi.single j 1)` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_single_one, dotProduct_single, single_dotProduct]`.
-/
theorem mulMat_transpose {N : ℕ} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (hρ : IsRealCoord I ρ) (c : InfinitePlace I.F → ℂ) :
    (mulMat ρ c)ᵀ = mulMat ρ (fun v => starRingEnd ℂ (c v)) := by
  classical
  ext i j
  have := mulMat_adj ρ hρ c (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single_one, dotProduct_single, single_dotProduct] using this

end MulCoord
end GlobalTheory.CuspGeo

namespace GlobalTheory.CuspGeo.MulCoord

/- English proof (translation)
Use extensionality with `i j`. Establish `hcol : (fun k => gm I ρ y e k j) = ρ (vec I y (e j))` using `by funext k; rfl`. Establish `hR : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j = ρ (vec I y (w • e j)) i`. Establish `h1 : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j = (mulMat ρ (fun v => I.φ v w) *ᵥ fun k => gm I ρ y e k j) i`. Simplify using `[Matrix.mul_apply, Matrix.mulVec, dotProduct]`.

Rewrite using `[h1, hcol, mulMat_mulVec, LinearEquiv.symm_apply_apply]`. Establish `h2 : mulL I (fun v => I.φ v w) (vec I y (e j)) = vec I y (w • e j)`. Use function extensionality and compare the values at `v k`. Rewrite using `[vec_smul]`. Both sides reduce to the same expression.

Rewrite using `[h2]`. Rewrite using `[hR, hM j, vec_sum_zsmul, map_sum, Finset.sum_apply]`. Simplify using `only [map_zsmul]`. Simplify using `only [Matrix.mul_apply, Matrix.map_apply, Pi.smul_apply, zsmul_eq_mul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `only [gm, Matrix.of_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem gm_mul {N : ℕ} {I : AutInst} (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ))
    (y : I.Ginf) (e : Fin N → Fin I.n → I.E) (w : I.E) (M : Matrix (Fin N) (Fin N) ℤ)
    (hM : ∀ j, w • e j = ∑ i, M i j • e i) :
    gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = mulMat ρ (fun v => I.φ v w) * gm I ρ y e := by
  ext i j
  have hcol : (fun k => gm I ρ y e k j) = ρ (vec I y (e j)) := by funext k; rfl
  have hR : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j = ρ (vec I y (w • e j)) i := by
    have h1 : (mulMat ρ (fun v => I.φ v w) * gm I ρ y e) i j =
        (mulMat ρ (fun v => I.φ v w) *ᵥ fun k => gm I ρ y e k j) i := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [h1, hcol, mulMat_mulVec, LinearEquiv.symm_apply_apply]
    have h2 : mulL I (fun v => I.φ v w) (vec I y (e j)) = vec I y (w • e j) := by
      funext v k
      rw [vec_smul]
      rfl
    rw [h2]
  rw [hR, hM j, vec_sum_zsmul, map_sum, Finset.sum_apply]
  simp only [map_zsmul]
  simp only [Matrix.mul_apply, Matrix.map_apply, Pi.smul_apply, zsmul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [gm, Matrix.of_apply]
  ring

/- English proof (translation)
Introduce `I N ρ hρ α hα`. Use `⟨mulMat ρ (fun v => I.φ v α), ?_⟩` and prove the remaining obligations. Introduce `y e he`. Establish `hint : ∀ j, IntVec I (e j)` using `fun j => (he.2 _).2 ⟨Pi.single j 1, by`. Simplify using `[Pi.single_apply, ite_smul]⟩`.

Establish `hα' : IsIntegral ℤ (star α)`. Conclude with `hα.map (starRingEnd I.E).toIntAlgHom`. Establish `hz : ∀ j, ∃ z : Fin N → ℤ, α • e j = ∑ i, z i • e i` using `fun j => (he.2 (α • e j)).1 fun i => by simpa [smul_eq_mul] using hα.mul (hint j i)`. Establish `hz' : ∀ j, ∃ z : Fin N → ℤ, star α • e j = ∑ i, z i • e i` using `fun j => (he.2 (star α • e j)).1 fun i => by simpa [smul_eq_mul] using hα'.mul (hint j i)`. Use `choose z hz using hz`.

Use `choose z' hz' using hz'`. Establish `hM : ∀ j, α • e j = ∑ i, (Matrix.of fun i j => z j i) i j • e i` using `fun j => by`. Simplify using `using hz j`. Establish `hM' : ∀ j, star α • e j = ∑ i, (Matrix.of fun i j => z' j i) i j • e i` using `fun j => by`. Simplify using `using hz' j`.

Use `⟨Matrix.of fun i j => z j i, Matrix.of fun i j => z' j i, gm_mul ρ y e α _ hM, ?_, hM⟩` and prove the remaining obligations. Rewrite using `[mulMat_transpose ρ hρ, gm_mul ρ y e (star α) _ hM']`. Use `congr 2`. Use function extensionality and compare the values at `v`. Conclude with `I.cm.cmUnram.2.1 (I.φ v) α`.
-/
theorem mul_conj_coord : ∀ (I : AutInst) (N : ℕ) (ρ : (InfinitePlace I.F → Fin I.n → ℂ) ≃ₗ[ℝ] (Fin N → ℝ)),
    IsRealCoord I ρ → ∀ α : I.E, IsIntegral ℤ α → ∃ X : Matrix (Fin N) (Fin N) ℝ,
      ∀ (y : I.Ginf) (e : Fin N → Fin I.n → I.E), IsZBasis I e → ∃ M M' : Matrix (Fin N) (Fin N) ℤ,
        gm I ρ y e * M.map (Int.cast : ℤ → ℝ) = X * gm I ρ y e ∧
        gm I ρ y e * M'.map (Int.cast : ℤ → ℝ) = Xᵀ * gm I ρ y e ∧ ∀ j, α • e j = ∑ i, M i j • e i := by
  classical
  intro I N ρ hρ α hα
  refine ⟨mulMat ρ (fun v => I.φ v α), ?_⟩
  intro y e he
  have hint : ∀ j, IntVec I (e j) := fun j => (he.2 _).2 ⟨Pi.single j 1, by
    simp [Pi.single_apply, ite_smul]⟩
  have hα' : IsIntegral ℤ (star α) := by
    exact hα.map (starRingEnd I.E).toIntAlgHom
  have hz : ∀ j, ∃ z : Fin N → ℤ, α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (α • e j)).1 fun i => by simpa [smul_eq_mul] using hα.mul (hint j i)
  have hz' : ∀ j, ∃ z : Fin N → ℤ, star α • e j = ∑ i, z i • e i := fun j =>
    (he.2 (star α • e j)).1 fun i => by simpa [smul_eq_mul] using hα'.mul (hint j i)
  choose z hz using hz
  choose z' hz' using hz'
  have hM : ∀ j, α • e j = ∑ i, (Matrix.of fun i j => z j i) i j • e i := fun j => by
    simpa using hz j
  have hM' : ∀ j, star α • e j = ∑ i, (Matrix.of fun i j => z' j i) i j • e i := fun j => by
    simpa using hz' j
  refine ⟨Matrix.of fun i j => z j i, Matrix.of fun i j => z' j i, gm_mul ρ y e α _ hM, ?_, hM⟩
  rw [mulMat_transpose ρ hρ, gm_mul ρ y e (star α) _ hM']
  congr 2
  funext v
  exact I.cm.cmUnram.2.1 (I.φ v) α

end GlobalTheory.CuspGeo.MulCoord
