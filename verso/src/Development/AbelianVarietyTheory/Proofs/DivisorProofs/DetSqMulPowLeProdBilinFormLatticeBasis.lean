import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefRealDetLeProdDiagStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.MinkowskiDetBoundGramOfDetNeZero
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.LatIndex

open Matrix

/- English proof (translation)
Simplify using `[dotProduct, mulVec, Int.cast_sum, Int.cast_mul]`.
-/
theorem cast_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (z : Fin n → ℤ) :
    (((z ⬝ᵥ M *ᵥ z : ℤ)) : ℝ) =
      (fun i => (z i : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => (z i : ℝ)) := by
  simp [dotProduct, mulVec, Int.cast_sum, Int.cast_mul]

/- English proof (translation)
Simplify using `[dotProduct, mulVec, map_sum, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem gram_quad {n : ℕ} {Y : Type} [AddCommGroup Y] (β : LinearMap.BilinForm ℤ Y)
    (v : Fin n → Y) (z : Fin n → ℤ) :
    z ⬝ᵥ (Matrix.of fun i j => β (v i) (v j)) *ᵥ z = β (∑ i, z i • v i) (∑ i, z i • v i) := by
  simp [dotProduct, mulVec, map_sum, LinearMap.sum_apply, Finset.mul_sum, mul_comm, mul_left_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_` and prove the remaining obligations. Use extensionality with `i j`. Use `congrFun (congrFun hs i) j` as an intermediate fact. Simplify using `[Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢`. Rewrite using `[this]`.

Simplify using `only [star_trivial]`. Establish `hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ x}` using `isClosed_le continuous_const (by fun_prop)`. Use `(DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl fun q => ?_` and prove the remaining obligations. Use `show 0 ≤ (fun i => ((q i : ℚ) : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => ((q i : ℚ) : ℝ))`. Use `set d : ℕ := ∏ i, (q i).den with hd`.

Establish `hd0 : (0 : ℝ) < d`. Rewrite using `[hd]`. Conclude with `Finset.prod_pos fun i _ => (q i).den_pos` after adjusting the coercions. Establish `hc : ∀ i, ∃ c : ℕ, d = (q i).den * c` using `fun i => Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)`. Use `choose c hc using hc`.

Set `z : Fin n → ℤ` to `fun i => (q i).num * c i`. Establish `hz : ∀ i, ((q i : ℚ) : ℝ) = (d : ℝ)⁻¹ * (z i : ℝ)`. Introduce `i`. Establish `h1 : ((z i : ℤ) : ℚ) = q i * d`. Simplify using `only [z, hc i, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]`.

Rewrite using `[← Rat.mul_den_eq_num]`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((z i : ℤ) : ℝ) = ((q i : ℚ) : ℝ) * d`. Use `congrArg (fun t : ℚ => (t : ℝ)) h1` as an intermediate fact. Simplify using `using this`.

Rewrite using `[h2]`. Clear the denominators using the available nonvanishing facts. Establish `hfun : (fun i => ((q i : ℚ) : ℝ)) = (d : ℝ)⁻¹ • (fun i => (z i : ℝ))`. Use extensionality with `i`. Simplify using `[hz i]`.

Rewrite using `[hfun, smul_dotProduct, mulVec_smul, dotProduct_smul, ← cast_quad]`. Use `h z` as an intermediate fact. Establish `h3 : (0 : ℝ) ≤ ((z ⬝ᵥ M *ᵥ z : ℤ) : ℝ)` using `by exact_mod_cast this`. Simplify using `only [smul_eq_mul]`. Check the signs of the components of the expression.
-/
theorem posSemidef_map_intCast {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) (hs : Mᵀ = M)
    (h : ∀ z : Fin n → ℤ, 0 ≤ z ⬝ᵥ M *ᵥ z) : (M.map (Int.cast : ℤ → ℝ)).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · ext i j
    have := congrFun (congrFun hs i) j
    simp [Matrix.conjTranspose_apply, Matrix.transpose_apply] at this ⊢
    rw [this]
  · simp only [star_trivial]
    have hcl : IsClosed {x : Fin n → ℝ | 0 ≤ x ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ x} :=
      isClosed_le continuous_const (by fun_prop)
    refine (DenseRange.piMap fun _ => Rat.denseRange_cast (𝕜 := ℝ)).induction_on x hcl
      fun q => ?_
    show 0 ≤ (fun i => ((q i : ℚ) : ℝ)) ⬝ᵥ M.map (Int.cast : ℤ → ℝ) *ᵥ (fun i => ((q i : ℚ) : ℝ))
    set d : ℕ := ∏ i, (q i).den with hd
    have hd0 : (0 : ℝ) < d := by
      rw [hd]; exact_mod_cast Finset.prod_pos fun i _ => (q i).den_pos
    have hc : ∀ i, ∃ c : ℕ, d = (q i).den * c := fun i =>
      Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)
    choose c hc using hc
    let z : Fin n → ℤ := fun i => (q i).num * c i
    have hz : ∀ i, ((q i : ℚ) : ℝ) = (d : ℝ)⁻¹ * (z i : ℝ) := by
      intro i
      have h1 : ((z i : ℤ) : ℚ) = q i * d := by
        simp only [z, hc i, Int.cast_mul, Int.cast_natCast, Nat.cast_mul]
        rw [← Rat.mul_den_eq_num]; ring
      have h2 : ((z i : ℤ) : ℝ) = ((q i : ℚ) : ℝ) * d := by
        have := congrArg (fun t : ℚ => (t : ℝ)) h1
        simpa using this
      rw [h2]; field_simp
    have hfun : (fun i => ((q i : ℚ) : ℝ)) = (d : ℝ)⁻¹ • (fun i => (z i : ℝ)) := by
      ext i; simp [hz i]
    rw [hfun, smul_dotProduct, mulVec_smul, dotProduct_smul, ← cast_quad]
    have := h z
    have h3 : (0 : ℝ) ≤ ((z ⬝ᵥ M *ᵥ z : ℤ) : ℝ) := by exact_mod_cast this
    simp only [smul_eq_mul]
    positivity

/- English proof (translation)
Introduce `r X₀ _ _ _ X _ _ _ b ε k β hsym hpos lam hlam hmin`. Set `e : Module.Basis (Fin r) ℤ X` to `b.map ε.symm`. Establish `he : ∀ i, e i = ε.symm (b i)` using `fun i => by simp [e]`. Set `Gz : Matrix (Fin r) (Fin r) ℤ` to `Matrix.of fun i j => β (e i) (e j)`. Set `A : Matrix (Fin r) (Fin r) ℤ` to `LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)`.

Set `Mz : Matrix (Fin r) (Fin r) ℤ` to `Matrix.of fun i j => β (k (b i)) (k (b j))`. Establish `hkb : ∀ j, k (b j) = ∑ i, A i j • e i`. Introduce `j`. Establish `h1 : ε (k (b j)) = ∑ i, A i j • b i`. Simplify using `only [A, LinearMap.toMatrix_apply]`.

Conclude with `(b.sum_repr _).symm`. Establish `h2` using `congrArg ε.symm h1`. Simplify using `only [LinearEquiv.symm_apply_apply, map_sum, map_zsmul] at h2`. Rewrite using `[h2]`. Simplify using `[he]`.

Establish `hM : Mz = Aᵀ * Gz * A`. Use extensionality with `j l`. Simplify using `only [Mz, Gz, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hkb]`. Simplify using `[map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]`. Establish `hdetA : A.det = LinearMap.det (ε.toLinearMap ∘ₗ k)` using `LinearMap.det_toMatrix b _`.

Establish `hGs : Gzᵀ = Gz` using `by ext i j; simp [Gz, hsym]`. Establish `hMs : Mzᵀ = Mz` using `by ext i j; simp [Mz, hsym]`. Establish `hGq : ∀ z, 0 ≤ z ⬝ᵥ Gz *ᵥ z` using `fun z => by rw [gram_quad]; exact hpos _`. Establish `hMq : ∀ z, 0 ≤ z ⬝ᵥ Mz *ᵥ z` using `fun z => by rw [gram_quad]; exact hpos _`. Establish `hG` using `posSemidef_map_intCast Gz hGs hGq`.

Establish `hMp` using `posSemidef_map_intCast Mz hMs hMq`. Establish `hmink : lam ^ r ≤ (r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det`. Use `GlobalTheory.minkowski_det_bound_posSemidef r _ hG lam hlam fun z hz => ?_` and prove the remaining obligations. Rewrite using `[← cast_quad, gram_quad]`. Apply `hmin` to reduce the goal to its premises.

Introduce `h0`. Apply `hz` to reduce the goal to its premises. Establish `: e.equivFun.symm z = e.equivFun.symm 0`. Rewrite using `[map_zero, Module.Basis.equivFun_symm_apply]`. Conclude with `h0`.

Conclude with `e.equivFun.symm.injective this`. Establish `hhad` using `GlobalTheory.T.posSemidef_det_le_prod_diag' r _ hMp`. Establish `hdetM : (Mz.map (Int.cast : ℤ → ℝ)).det = ((A.det : ℤ) : ℝ) ^ 2 * (Gz.map (Int.cast : ℤ → ℝ)).det`. Establish `h1 : ∀ N : Matrix (Fin r) (Fin r) ℤ, (N.map (Int.cast : ℤ → ℝ)).det = ((N.det : ℤ) : ℝ)` using `fun N => by`. Rewrite using `[show (N.map (Int.cast : ℤ → ℝ)) = (Int.castRingHom ℝ).mapMatrix N from rfl, ← RingHom.map_det]`.

Both sides reduce to the same expression. Rewrite using `[h1, h1, hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hdiag : ∀ j, (Mz.map (Int.cast : ℤ → ℝ)) j j = (β (k (b j)) (k (b j)) : ℝ)`.

Introduce `j`. Simplify using `[Mz]`. Simplify using `only [hdiag] at hhad`. Rewrite using `[← hdetA]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem det_sq_mul_pow_le_prod :
    ∀ (r : ℕ) (X₀ : Type) [AddCommGroup X₀] [Module.Free ℤ X₀] [Module.Finite ℤ X₀] (X : Type)
      [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (b : Module.Basis (Fin r) ℤ X₀)
      (ε : X ≃ₗ[ℤ] X₀) (k : X₀ →ₗ[ℤ] X) (β : LinearMap.BilinForm ℤ X),
      (∀ a b, β a b = β b a) → (∀ y, 0 ≤ β y y) → ∀ lam : ℝ, 0 ≤ lam →
      (∀ x, x ≠ 0 → lam ≤ β x x) →
      ((LinearMap.det (ε.toLinearMap ∘ₗ k) : ℤ) : ℝ) ^ 2 * lam ^ r ≤
        (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) := by
  intro r X₀ _ _ _ X _ _ _ b ε k β hsym hpos lam hlam hmin
  classical
  let e : Module.Basis (Fin r) ℤ X := b.map ε.symm
  have he : ∀ i, e i = ε.symm (b i) := fun i => by simp [e]
  let Gz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (e i) (e j)
  let A : Matrix (Fin r) (Fin r) ℤ := LinearMap.toMatrix b b (ε.toLinearMap ∘ₗ k)
  let Mz : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => β (k (b i)) (k (b j))
  have hkb : ∀ j, k (b j) = ∑ i, A i j • e i := by
    intro j
    have h1 : ε (k (b j)) = ∑ i, A i j • b i := by
      simp only [A, LinearMap.toMatrix_apply]
      exact (b.sum_repr _).symm
    have h2 := congrArg ε.symm h1
    simp only [LinearEquiv.symm_apply_apply, map_sum, map_zsmul] at h2
    rw [h2]; simp [he]
  have hM : Mz = Aᵀ * Gz * A := by
    ext j l
    simp only [Mz, Gz, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, hkb]
    simp [map_sum, LinearMap.sum_apply, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm]
  have hdetA : A.det = LinearMap.det (ε.toLinearMap ∘ₗ k) := LinearMap.det_toMatrix b _
  have hGs : Gzᵀ = Gz := by ext i j; simp [Gz, hsym]
  have hMs : Mzᵀ = Mz := by ext i j; simp [Mz, hsym]
  have hGq : ∀ z, 0 ≤ z ⬝ᵥ Gz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hMq : ∀ z, 0 ≤ z ⬝ᵥ Mz *ᵥ z := fun z => by rw [gram_quad]; exact hpos _
  have hG := posSemidef_map_intCast Gz hGs hGq
  have hMp := posSemidef_map_intCast Mz hMs hMq
  have hmink : lam ^ r ≤ (r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    refine GlobalTheory.minkowski_det_bound_posSemidef r _ hG lam hlam fun z hz => ?_
    rw [← cast_quad, gram_quad]
    apply hmin
    intro h0
    apply hz
    have : e.equivFun.symm z = e.equivFun.symm 0 := by
      rw [map_zero, Module.Basis.equivFun_symm_apply]; exact h0
    exact e.equivFun.symm.injective this
  have hhad := GlobalTheory.T.posSemidef_det_le_prod_diag' r _ hMp
  have hdetM : (Mz.map (Int.cast : ℤ → ℝ)).det =
      ((A.det : ℤ) : ℝ) ^ 2 * (Gz.map (Int.cast : ℤ → ℝ)).det := by
    have h1 : ∀ N : Matrix (Fin r) (Fin r) ℤ, (N.map (Int.cast : ℤ → ℝ)).det = ((N.det : ℤ) : ℝ) :=
      fun N => by
        rw [show (N.map (Int.cast : ℤ → ℝ)) = (Int.castRingHom ℝ).mapMatrix N from rfl,
          ← RingHom.map_det]; rfl
    rw [h1, h1, hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    push_cast; ring
  have hdiag : ∀ j, (Mz.map (Int.cast : ℤ → ℝ)) j j = (β (k (b j)) (k (b j)) : ℝ) := by
    intro j; simp [Mz]
  simp only [hdiag] at hhad
  rw [← hdetA]
  calc ((A.det : ℤ) : ℝ) ^ 2 * lam ^ r
      ≤ ((A.det : ℤ) : ℝ) ^ 2 * ((r : ℝ) ^ r * (Gz.map (Int.cast : ℤ → ℝ)).det) :=
        mul_le_mul_of_nonneg_left hmink (sq_nonneg _)
    _ = (r : ℝ) ^ r * (Mz.map (Int.cast : ℤ → ℝ)).det := by rw [hdetM]; ring
    _ ≤ (r : ℝ) ^ r * ∏ j, (β (k (b j)) (k (b j)) : ℝ) :=
        mul_le_mul_of_nonneg_left hhad (by positivity)

end GlobalTheory.LatIndex
