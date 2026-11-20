import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OfRoots
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetFromBlocksSingle
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical

namespace GlobalTheory.LoopV.Cong

section Mat

variable {K : Type} [Field K] {r : ℕ}

/- English proof (translation)
Rewrite using `[Matrix.det_of_isLowerTriangular L (fun i j hij => (h i j).1 hij)]`. Conclude with `Finset.prod_eq_one fun i _ => (h i i).2 rfl`.
-/
theorem lo_det {N : ℕ} {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) : L.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular L (fun i j hij => (h i j).1 hij)]
  exact Finset.prod_eq_one fun i _ => (h i i).2 rfl

/- English proof (translation)
Establish `hu : IsUnit x.det` using `by rw [lo_det h]; exact isUnit_one`. Use `letI := x.invertibleOfIsUnitDet hu`. Establish `hlow : x.BlockTriangular OrderDual.toDual` using `fun i j hij => (h i j).1 hij`. Establish `hinv` using `Matrix.blockTriangular_inv_of_blockTriangular hlow`. Establish `hmul : x * x⁻¹ = 1` using `Matrix.mul_nonsing_inv x hu`.

Introduce `i j`. Use `⟨fun hij => hinv hij, fun hij => ?_⟩` and prove the remaining obligations. Substitute `hij` using the available equality. Establish `hii` using `congrFun (congrFun hmul i) i`. Rewrite `hii` using `[Matrix.mul_apply, Finset.sum_eq_single i]`.

Rewrite `hii` using `[(h i i).2 rfl, one_mul]`. Simplify using `using hii`. Introduce `k _ hk`. Break down `lt_or_gt_of_ne hk with hk | hk` into its components or cases. Rewrite using `[hinv hk, mul_zero]`.

Rewrite using `[(h i k).1 hk, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem lo_inv {N : ℕ} {x : Matrix (Fin N) (Fin N) K} (h : IsLoUni x) : IsLoUni x⁻¹ := by
  have hu : IsUnit x.det := by rw [lo_det h]; exact isUnit_one
  letI := x.invertibleOfIsUnitDet hu
  have hlow : x.BlockTriangular OrderDual.toDual := fun i j hij => (h i j).1 hij
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hlow
  have hmul : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hu
  intro i j
  refine ⟨fun hij => hinv hij, fun hij => ?_⟩
  subst hij
  have hii := congrFun (congrFun hmul i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at hii
  · rw [(h i i).2 rfl, one_mul] at hii
    simpa using hii
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hk | hk
    · rw [hinv hk, mul_zero]
    · rw [(h i k).1 hk, zero_mul]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hy, mul_zero, Finset.sum_const_zero, zero_add]`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[(h _ _).2 rfl, one_mul]`. Rewrite using `[(h _ _).1 (Fin.castSucc_lt_last i), zero_mul, hy]`.
-/
theorem lo_mulVec {L : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsLoUni L) (y : Fin (r + 1) → K)
    (hy : ∀ i : Fin r, y i.castSucc = 0) : L *ᵥ y = y := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_castSucc, hy, mul_zero, Finset.sum_const_zero, zero_add]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [(h _ _).2 rfl, one_mul]
  · rw [(h _ _).1 (Fin.castSucc_lt_last i), zero_mul, hy]

/- English proof (translation)
Use `split_ifs with hj`. Substitute `hj` using the available equality. Conclude with `(h _ _).2 rfl`. Conclude with `(h _ _).1 (lt_of_le_of_ne (Fin.le_last j) hj)`.
-/
private lemma last_apply_of_isUpUni {a : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni a) (j : Fin (r + 1)) :
    a (Fin.last r) j = if j = Fin.last r then 1 else 0 := by
  split_ifs with hj
  · subst hj; exact (h _ _).2 rfl
  · exact (h _ _).1 (lt_of_le_of_ne (Fin.le_last j) hj)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply, last_apply_of_isUpUni h, Matrix.one_apply]`. Apply the tactic sequence `split_ifs with h1 h2 h2 <;> first | exact absurd h1.symm h2 | exact absurd h2.symm h1 | simp`.
-/
theorem up_last {a : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni a) (c : Fin (r + 1) → K) :
    ((a - 1) *ᵥ c) (Fin.last r) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Matrix.sub_apply, last_apply_of_isUpUni h, Matrix.one_apply]
  split_ifs with h1 h2 h2 <;> first | exact absurd h1.symm h2 | exact absurd h2.symm h1 | simp

variable [StarRing K]

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.conjTranspose_apply]`. Conclude with `⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩`.
-/
theorem up_conjT {N : ℕ} {a : Matrix (Fin N) (Fin N) K} (h : IsUpUni a) : IsLoUni aᴴ := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.conjTranspose_apply]`. Conclude with `⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩`.
-/
theorem lo_conjT {N : ℕ} {a : Matrix (Fin N) (Fin N) K} (h : IsLoUni a) : IsUpUni aᴴ := by
  intro i j
  simp only [Matrix.conjTranspose_apply]
  exact ⟨fun hij => by rw [(h j i).1 hij, star_zero], fun hij => by subst hij; rw [(h i i).2 rfl, star_one]⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]`. Apply the tactic sequence `simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, last_apply_of_isUpUni h, Matrix.diagonal_apply] split_ifs <;> simp_all`. Introduce `k _ hk`. Simplify using `[Matrix.mul_diagonal, hk]`.

Simplify using the standard rewrite rules.
-/
theorem up_diag {a : Matrix (Fin (r + 1)) (Fin (r + 1)) K} (h : IsUpUni a) (t : K) :
    aᴴ * (diagonal fun i => if i = Fin.last r then t else 0) * a =
      diagonal fun i => if i = Fin.last r then t else 0 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
  · simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply, last_apply_of_isUpUni h, Matrix.diagonal_apply]
    split_ifs <;> simp_all
  · intro k _ hk
    simp [Matrix.mul_diagonal, hk]
  · simp

end Mat

section Int

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]

def AllInt (M : Matrix ι ι K) : Prop := ∀ i j, IsIntegral ℤ (M i j)

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.mul_apply]`. Conclude with `IsIntegral.sum _ fun k _ => (hM i k).mul (hN k j)`.
-/
theorem AllInt.mul {M N : Matrix ι ι K} (hM : AllInt M) (hN : AllInt N) : AllInt (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun k _ => (hM i k).mul (hN k j)

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `IsIntegral.sum _ fun σ _ => ?_` and prove the remaining obligations. Establish `hp : IsIntegral ℤ (∏ i, M (σ i) i)` using `IsIntegral.prod _ fun i _ => hM (σ i) i`. Break down `Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs` into its components or cases. Rewrite using `[hs, one_smul]`.

Conclude with `hp`. Rewrite using `[hs, Units.neg_smul, one_smul]`. Conclude with `hp.neg`.
-/
theorem AllInt.det {M : Matrix ι ι K} (hM : AllInt M) : IsIntegral ℤ M.det := by
  rw [Matrix.det_apply]
  refine IsIntegral.sum _ fun σ _ => ?_
  have hp : IsIntegral ℤ (∏ i, M (σ i) i) := IsIntegral.prod _ fun i _ => hM (σ i) i
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]; exact hp
  · rw [hs, Units.neg_smul, one_smul]; exact hp.neg

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.adjugate_apply]`. Apply `AllInt.det` to reduce the goal to its premises. Introduce `k l`. Rewrite using `[Matrix.updateRow_apply]`.

Use `split_ifs`. Rewrite using `[Pi.single_apply] split_ifs`. Conclude with `isIntegral_one`. Conclude with `isIntegral_zero`. Conclude with `hM k l`.
-/
theorem AllInt.adj {M : Matrix ι ι K} (hM : AllInt M) : AllInt M.adjugate := by
  intro i j
  rw [Matrix.adjugate_apply]
  apply AllInt.det
  intro k l
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]
    split_ifs
    · exact isIntegral_one
    · exact isIntegral_zero
  · exact hM k l

/- English proof (translation)
Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `isIntegral_one`. Conclude with `isIntegral_zero`.
-/
theorem allInt_one : AllInt (1 : Matrix ι ι K) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact isIntegral_one
  · exact isIntegral_zero

/- English proof (translation)
Establish `hs` using `h.map (starRingEnd K).toIntAlgHom`. Conclude with `hs`.
-/
theorem int_star [StarRing K] {x : K} (h : IsIntegral ℤ x) : IsIntegral ℤ (star x) := by
  have hs := h.map (starRingEnd K).toIntAlgHom
  exact hs

/- English proof (translation)
Introduce `i j` and use `int_star (hM j i)`.
-/
theorem AllInt.conjT [StarRing K] {M : Matrix ι ι K} (hM : AllInt M) : AllInt Mᴴ := fun i j => int_star (hM j i)

end Int

section Iso

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}
  {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Rewrite using `[← S.herm.eq y x]`. Both sides reduce to the same expression.
-/
theorem herm' (x y : S.V) : S.hT x y = star (S.hT y x) := by
  rw [← S.herm.eq y x]
  rfl

/- English proof (translation)
Simplify using `only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, dotProduct, Pi.star_apply, smul_eq_mul, starRingEnd_apply]`.
-/
theorem hT_comb_left (v : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT (∑ p, c p • v p) x = star c ⬝ᵥ fun p => S.hT (v p) x := by
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, dotProduct, Pi.star_apply,
    smul_eq_mul, starRingEnd_apply]

/- English proof (translation)
Simplify using `only [map_sum, map_smul, dotProduct, Pi.star_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[herm' x (v p), mul_comm]`.
-/
theorem hT_comb_right (v : ι → S.V) (c : ι → E) (x : S.V) :
    S.hT x (∑ p, c p • v p) = star (fun p => S.hT (v p) x) ⬝ᵥ c := by
  simp only [map_sum, map_smul, dotProduct, Pi.star_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [herm' x (v p), mul_comm]

/- English proof (translation)
Use `set B := A - 1 with hB`. Establish `hU : IsUnit Γ.det` using `isUnit_iff_ne_zero.mpr hdet`. Establish `hH : Γᴴ = Γ`. Use extensionality with `p q`. Rewrite using `[Matrix.conjTranspose_apply, hΓ, hΓ, herm' (v p) (v q)]`.

Establish `hBm : Γ * B + (Bᴴ * Γ + Bᴴ * Γ * B) = 0`. Establish `hBH : Bᴴ = Aᴴ - 1` using `by rw [hB, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]`. Rewrite using `[hBH, hB]`. Establish `e : Γ * (A - 1) + ((Aᴴ - 1) * Γ + (Aᴴ - 1) * Γ * (A - 1)) = Aᴴ * Γ * A - Γ`. Simplify using `only [mul_sub, sub_mul, mul_one, one_mul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e, hA, sub_self]`. Set `g : S.V →ₗ[E] S.V` to `{ toFun := fun x => ∑ p, (B *ᵥ (Γ⁻¹ *ᵥ fun q => S.hT (v q) x)) p • v p map_add' := fun x y => by`. Establish `hxy : (fun q => S.hT (v q) (x + y)) = (fun q => S.hT (v q) x) + (fun q => S.hT (v q) y)`. Use function extensionality and compare the values at `q`.

Simplify using the standard rewrite rules. Rewrite using `[hxy, Matrix.mulVec_add, Matrix.mulVec_add, ← Finset.sum_add_distrib]`. Simplify using `[add_smul]`. Use the proof step `map_smul' := fun c x => by`. Establish `hcx : (fun q => S.hT (v q) (c • x)) = c • (fun q => S.hT (v q) x)`.

Use function extensionality and compare the values at `q`. Simplify using the standard rewrite rules. Rewrite using `[hcx, Matrix.mulVec_smul, Matrix.mulVec_smul]`. Simplify using `[Finset.smul_sum, mul_smul] }`. Set `f : S.V →ₗ[E] S.V` to `LinearMap.id + g`.

Establish `hW : ∀ s t : ι → E, S.hT (∑ p, s p • v p) (∑ q, t q • v q) = star s ⬝ᵥ (Γ *ᵥ t)`. Introduce `s t`. Rewrite using `[hT_comb_left]`. Use `congr 1`. Use function extensionality and compare the values at `p`.

Simplify using `only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]`. Conclude with `Finset.sum_congr rfl fun q _ => by rw [hΓ, mul_comm]`. Establish `hiso : ∀ x y, S.hT (f x) (f y) = S.hT x y`. Introduce `x y`. Take `⟨ux, hux⟩ : ∃ u, u = Γ⁻¹ *ᵥ fun q => S.hT (v q) x` from `⟨_, rfl⟩`.

Take `⟨uy, huy⟩ : ∃ u, u = Γ⁻¹ *ᵥ fun q => S.hT (v q) y` from `⟨_, rfl⟩`. Establish `hfx : f x = x + ∑ p, (B *ᵥ ux) p • v p` using `by rw [hux]; rfl`. Establish `hfy : f y = y + ∑ p, (B *ᵥ uy) p • v p` using `by rw [huy]; rfl`. Establish `hcx : (fun q => S.hT (v q) x) = Γ *ᵥ ux`. Rewrite using `[hux, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]`.

Establish `hcy : (fun q => S.hT (v q) y) = Γ *ᵥ uy`. Rewrite using `[huy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]`. Establish `key : star (Γ *ᵥ ux) ⬝ᵥ (B *ᵥ uy) + (star (B *ᵥ ux) ⬝ᵥ (Γ *ᵥ uy) + star (B *ᵥ ux) ⬝ᵥ (Γ *ᵥ (B *ᵥ uy))) = 0`. Simplify using `only [star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul]`. Rewrite using `[← add_dotProduct, ← add_dotProduct, ← vecMul_add, ← vecMul_add, hBm, vecMul_zero, zero_dotProduct]`.

Rewrite using `[hfx, hfy]`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[hW (B *ᵥ ux) (B *ᵥ uy), hT_comb_left v (B *ᵥ ux) y, hT_comb_right v (B *ᵥ uy) x, hcx, hcy]`. Take the linear combination `key`. Establish `hinj : Function.Injective f`.

Introduce `x y hxy`. Rewrite using `[← sub_eq_zero]`. Apply `S.nondeg.1` to reduce the goal to its premises. Introduce `w`. Rewrite using `[← hiso (x - y) w, map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply]`.

Use `⟨LinearEquiv.ofInjectiveEndo f hinj, hiso, fun x => rfl⟩` and prove the remaining obligations.
-/
theorem exists_isom (v : ι → S.V) (Γ A : Matrix ι ι E) (hΓ : ∀ p q, Γ p q = S.hT (v p) (v q))
    (hdet : Γ.det ≠ 0) (hA : Aᴴ * Γ * A = Γ) :
    ∃ n ∈ Formalism.HermitianLatticesTheory.isom S.hT,
      ∀ x, n x = x + ∑ p, ((A - 1) *ᵥ (Γ⁻¹ *ᵥ fun q => S.hT (v q) x)) p • v p := by
  set B := A - 1 with hB
  have hU : IsUnit Γ.det := isUnit_iff_ne_zero.mpr hdet
  have hH : Γᴴ = Γ := by
    ext p q
    rw [Matrix.conjTranspose_apply, hΓ, hΓ, herm' (v p) (v q)]
  have hBm : Γ * B + (Bᴴ * Γ + Bᴴ * Γ * B) = 0 := by
    have hBH : Bᴴ = Aᴴ - 1 := by rw [hB, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    rw [hBH, hB]
    have e : Γ * (A - 1) + ((Aᴴ - 1) * Γ + (Aᴴ - 1) * Γ * (A - 1)) = Aᴴ * Γ * A - Γ := by
      simp only [mul_sub, sub_mul, mul_one, one_mul]
      abel
    rw [e, hA, sub_self]
  let g : S.V →ₗ[E] S.V :=
    { toFun := fun x => ∑ p, (B *ᵥ (Γ⁻¹ *ᵥ fun q => S.hT (v q) x)) p • v p
      map_add' := fun x y => by
        have hxy : (fun q => S.hT (v q) (x + y)) = (fun q => S.hT (v q) x) + (fun q => S.hT (v q) y) := by
          funext q
          simp
        rw [hxy, Matrix.mulVec_add, Matrix.mulVec_add, ← Finset.sum_add_distrib]
        simp [add_smul]
      map_smul' := fun c x => by
        have hcx : (fun q => S.hT (v q) (c • x)) = c • (fun q => S.hT (v q) x) := by
          funext q
          simp
        rw [hcx, Matrix.mulVec_smul, Matrix.mulVec_smul]
        simp [Finset.smul_sum, mul_smul] }
  let f : S.V →ₗ[E] S.V := LinearMap.id + g
  have hW : ∀ s t : ι → E, S.hT (∑ p, s p • v p) (∑ q, t q • v q) = star s ⬝ᵥ (Γ *ᵥ t) := by
    intro s t
    rw [hT_comb_left]
    congr 1
    funext p
    simp only [map_sum, map_smul, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun q _ => by rw [hΓ, mul_comm]
  have hiso : ∀ x y, S.hT (f x) (f y) = S.hT x y := by
    intro x y
    obtain ⟨ux, hux⟩ : ∃ u, u = Γ⁻¹ *ᵥ fun q => S.hT (v q) x := ⟨_, rfl⟩
    obtain ⟨uy, huy⟩ : ∃ u, u = Γ⁻¹ *ᵥ fun q => S.hT (v q) y := ⟨_, rfl⟩
    have hfx : f x = x + ∑ p, (B *ᵥ ux) p • v p := by rw [hux]; rfl
    have hfy : f y = y + ∑ p, (B *ᵥ uy) p • v p := by rw [huy]; rfl
    have hcx : (fun q => S.hT (v q) x) = Γ *ᵥ ux := by
      rw [hux, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    have hcy : (fun q => S.hT (v q) y) = Γ *ᵥ uy := by
      rw [huy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hU, Matrix.one_mulVec]
    have key : star (Γ *ᵥ ux) ⬝ᵥ (B *ᵥ uy) + (star (B *ᵥ ux) ⬝ᵥ (Γ *ᵥ uy) +
        star (B *ᵥ ux) ⬝ᵥ (Γ *ᵥ (B *ᵥ uy))) = 0 := by
      simp only [star_mulVec, hH, dotProduct_mulVec, vecMul_vecMul]
      rw [← add_dotProduct, ← add_dotProduct, ← vecMul_add, ← vecMul_add, hBm, vecMul_zero, zero_dotProduct]
    rw [hfx, hfy]
    simp only [map_add, LinearMap.add_apply]
    rw [hW (B *ᵥ ux) (B *ᵥ uy), hT_comb_left v (B *ᵥ ux) y, hT_comb_right v (B *ᵥ uy) x, hcx, hcy]
    linear_combination key
  have hinj : Function.Injective f := by
    intro x y hxy
    rw [← sub_eq_zero]
    apply S.nondeg.1
    intro w
    rw [← hiso (x - y) w, map_sub, hxy, sub_self, map_zero, LinearMap.zero_apply]
  refine ⟨LinearEquiv.ofInjectiveEndo f hinj, hiso, fun x => rfl⟩

end Iso

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

/- English proof (translation)
Establish `hΛ' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ` using `hΛ`. Establish `key : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x)`. Introduce `x`. Simplify using `only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply, Submodule.mem_one]`. Use `forall₂_congr fun y _ => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩` and prove the remaining obligations.

Introduce and unpack `⟨o, ho⟩`. Rewrite using `[← ho]`. Conclude with `o.isIntegral_coe`. Rewrite using `[← key, hΛ']`.
-/
theorem mem_unimod {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ) (x : S.V) :
    x ∈ Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x) := by
  have hΛ' : Formalism.HermitianLatticesTheory.dual S.hT Λ = Λ := hΛ
  have key : ∀ x, x ∈ Formalism.HermitianLatticesTheory.dual S.hT Λ ↔ ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x) := by
    intro x
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]
    refine forall₂_congr fun y _ => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
    rintro ⟨o, ho⟩
    rw [← ho]
    exact o.isIntegral_coe
  rw [← key, hΛ']

/- English proof (translation)
Establish `hc' : c ∈ integralClosure ℤ E` using `hc`. Set `o : 𝓞 E` to `⟨c, hc'⟩`. Establish `h1 : c • x = o • x` using `algebraMap_smul E o x`. Rewrite using `[h1]`. Conclude with `Λ.smul_mem o hx`.
-/
theorem int_smul_mem {Λ : Submodule (𝓞 E) S.V} {c : E} (hc : IsIntegral ℤ c) {x : S.V} (hx : x ∈ Λ) :
    c • x ∈ Λ := by
  have hc' : c ∈ integralClosure ℤ E := hc
  let o : 𝓞 E := ⟨c, hc'⟩
  have h1 : c • x = o • x := algebraMap_smul E o x
  rw [h1]
  exact Λ.smul_mem o hx

/- English proof (translation)
Establish `hiso : ∀ a b, S.hT (n a) (n b) = S.hT a b` using `hn`. Use `⟨hn, le_antisymm ?_ ?_⟩` and prove the remaining obligations. Introduce `x hx`. Take `⟨y, hy, rfl⟩` from `Submodule.mem_map.mp hx`. Conclude with `h y hy`.

Introduce `x hx`. Use `Submodule.mem_map.mpr ⟨n.symm x, ?_, n.apply_symm_apply x⟩` and prove the remaining obligations. Rewrite using `[mem_unimod hΛ]`. Introduce `y hy`. Rewrite using `[← hiso, LinearEquiv.apply_symm_apply]`.

Conclude with `(mem_unimod hΛ x).1 hx (n y) (h y hy)`.
-/
theorem isAutLam_of_mapsTo {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    {n : S.V ≃ₗ[E] S.V} (hn : n ∈ Formalism.HermitianLatticesTheory.isom S.hT) (h : ∀ x ∈ Λ, n x ∈ Λ) : IsAutLam S Λ n := by
  have hiso : ∀ a b, S.hT (n a) (n b) = S.hT a b := hn
  refine ⟨hn, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
    exact h y hy
  · intro x hx
    refine Submodule.mem_map.mpr ⟨n.symm x, ?_, n.apply_symm_apply x⟩
    rw [mem_unimod hΛ]
    intro y hy
    rw [← hiso, LinearEquiv.apply_symm_apply]
    exact (mem_unimod hΛ x).1 hx (n y) (h y hy)

variable {r : ℕ} {T T' : E}

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]`.
-/
theorem frame_cast (F : LFlag S r T) (i : Fin r) : frame F i.castSucc = F.fl.e i := by
  simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_castSucc]

/- English proof (translation)
Simplify using `only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]`.
-/
theorem frame_last (F : LFlag S r T) : frame F (Fin.last r) = F.fl.z := by
  simp only [Formalism.MainNotions.S.Lat.frame, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last]

/- English proof (translation)
Rewrite using `[Fin.sum_univ_castSucc, hc, zero_smul, add_zero]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[frame_cast]`. Use `show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.
-/
theorem comb_mem_X (F : LFlag S r T) (c : Fin (r + 1) → E) (hc : c (Fin.last r) = 0) :
    ∑ i, c i • frame F i ∈ Xsp F := by
  rw [Fin.sum_univ_castSucc, hc, zero_smul, add_zero]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  rw [frame_cast]
  show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)
  exact Submodule.subset_span ⟨i, rfl⟩

/- English proof (translation)
Establish `hgen : ∀ i : Fin r, i.1 < j + 1 → n (F.fl.e i) - F.fl.e i ∈ Xflag F j`. Introduce `i hi`. Rewrite using `[← frame_cast, hn]`. Establish `hsplit : (∑ k, a k i.castSucc • frame F k) - frame F i.castSucc = ∑ k, (a k i.castSucc - if k = i.castSucc then 1 else 0) • frame F k`. Simplify using `[sub_smul, Finset.sum_sub_distrib]`.

Rewrite using `[hsplit]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Break down `lt_trichotomy k i.castSucc with hk | hk | hk` into its components or cases. Establish `hki : k.1 < i.1` using `hk`. Take `⟨k', rfl⟩ : ∃ k' : Fin r, k'.castSucc = k` from `⟨⟨k.1, lt_trans hki i.2⟩, Fin.ext rfl⟩`.

Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Rewrite using `[frame_cast]`. Use `show F.fl.e k' ∈ Submodule.span E (F.fl.e '' {i | i.1 < j})`. Use `Submodule.subset_span ⟨k', ?_, rfl⟩` and prove the remaining obligations. Use `show k'.1 < j`.

Establish `: k'.1 < i.1` using `hki`. Use linear arithmetic over natural numbers and integers. Rewrite using `[if_pos hk, hk, (ha _ _).2 rfl, sub_self, zero_smul]`. Conclude with `Submodule.zero_mem _`. Rewrite using `[if_neg (ne_of_gt hk), (ha _ _).1 hk, sub_self, zero_smul]`.

Conclude with `Submodule.zero_mem _`. Establish `hle : Xflag F (j + 1) ≤ (Xflag F j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id)` using `by show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, hi, rfl⟩`. Conclude with `hgen i hi`.

Introduce `x hx`. Conclude with `hle hx`.
-/
theorem flag_step (F : LFlag S r T) (n : S.V ≃ₗ[E] S.V) {a : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (ha : IsUpUni a) (hn : ∀ c, n (frame F c) = ∑ i, a i c • frame F i) (j : ℕ) :
    ∀ x ∈ Xflag F (j + 1), n x - x ∈ Xflag F j := by
  have hgen : ∀ i : Fin r, i.1 < j + 1 → n (F.fl.e i) - F.fl.e i ∈ Xflag F j := by
    intro i hi
    rw [← frame_cast, hn]
    have hsplit : (∑ k, a k i.castSucc • frame F k) - frame F i.castSucc =
        ∑ k, (a k i.castSucc - if k = i.castSucc then 1 else 0) • frame F k := by
      simp [sub_smul, Finset.sum_sub_distrib]
    rw [hsplit]
    refine Submodule.sum_mem _ fun k _ => ?_
    rcases lt_trichotomy k i.castSucc with hk | hk | hk
    · have hki : k.1 < i.1 := hk
      obtain ⟨k', rfl⟩ : ∃ k' : Fin r, k'.castSucc = k := ⟨⟨k.1, lt_trans hki i.2⟩, Fin.ext rfl⟩
      refine Submodule.smul_mem _ _ ?_
      rw [frame_cast]
      show F.fl.e k' ∈ Submodule.span E (F.fl.e '' {i | i.1 < j})
      refine Submodule.subset_span ⟨k', ?_, rfl⟩
      show k'.1 < j
      have : k'.1 < i.1 := hki
      omega
    · rw [if_pos hk, hk, (ha _ _).2 rfl, sub_self, zero_smul]
      exact Submodule.zero_mem _
    · rw [if_neg (ne_of_gt hk), (ha _ _).1 hk, sub_self, zero_smul]
      exact Submodule.zero_mem _
  have hle : Xflag F (j + 1) ≤ (Xflag F j).comap ((n : S.V →ₗ[E] S.V) - LinearMap.id) := by
    show Submodule.span E (F.fl.e '' {i | i.1 < j + 1}) ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact hgen i hi
  intro x hx
  exact hle hx

/- English proof (translation)
Establish `hz : ∀ a : Fin r, S.hT F.fl.z (F.fl.e a) = 0` using `fun a => by rw [herm', F.fl.z_orth, star_zero]`. Establish `hne : ∀ i : Fin r, Fin.last r ≠ Fin.castSucc i` using `fun i => (Fin.castSucc_ne_last i).symm`. Rewrite using `[Matrix.diagonal_apply]`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b`. Simplify using `[frame_last, F.fl.z_norm]`.

Simplify using `[frame_last, frame_cast, hz, hne]`. Simplify using `[frame_last, frame_cast, F.fl.z_orth, Fin.castSucc_ne_last]`. Simplify using `[frame_cast, F.fl.e_iso, Fin.castSucc_ne_last]`.
-/
theorem gram_self (F : LFlag S r T) (a b : Fin (r + 1)) :
    S.hT (frame F a) (frame F b) = diagonal (fun a => if a = Fin.last r then -T else 0) a b := by
  have hz : ∀ a : Fin r, S.hT F.fl.z (F.fl.e a) = 0 := fun a => by rw [herm', F.fl.z_orth, star_zero]
  have hne : ∀ i : Fin r, Fin.last r ≠ Fin.castSucc i := fun i => (Fin.castSucc_ne_last i).symm
  rw [Matrix.diagonal_apply]
  refine Fin.lastCases ?_ (fun i => ?_) a <;> refine Fin.lastCases ?_ (fun j => ?_) b
  · simp [frame_last, F.fl.z_norm]
  · simp [frame_last, frame_cast, hz, hne]
  · simp [frame_last, frame_cast, F.fl.z_orth, Fin.castSucc_ne_last]
  · simp [frame_cast, F.fl.e_iso, Fin.castSucc_ne_last]

def gramM (F : LFlag S r T) (F' : LFlag S r T') :
    Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E :=
  fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) (ZhatL F F') (ZhatL F F')ᴴ
    (diagonal fun a => if a = Fin.last r then -T' else 0)

/- English proof (translation)
Apply the tactic sequence `rcases p with a | a <;> rcases q with b | b`. Conclude with `(gram_self F a b).symm`. Both sides reduce to the same expression. Use `show star (S.hT (frame F b) (frame F' a)) = S.hT (frame F' a) (frame F b)`. Conclude with `(herm' _ _).symm`.

Conclude with `(gram_self F' a b).symm`.
-/
theorem gramM_apply (F : LFlag S r T) (F' : LFlag S r T') (p q) :
    gramM F F' p q = S.hT (Sum.elim (frame F) (frame F') p) (Sum.elim (frame F) (frame F') q) := by
  rcases p with a | a <;> rcases q with b | b
  · exact (gram_self F a b).symm
  · rfl
  · show star (S.hT (frame F b) (frame F' a)) = S.hT (frame F' a) (frame F b)
    exact (herm' _ _).symm
  · exact (gram_self F' a b).symm

/- English proof (translation)
Use `show leadMinorE (Zhat F.fl F'.fl) (r + 1) = _`. Unfold `leadMinorE`. Rewrite using `[dif_pos le_rfl]`. Establish `hc : (Fin.castLE (le_refl (r + 1))) = id` using `funext fun i => Fin.ext rfl`. Rewrite using `[hc, Matrix.submatrix_id_id]`.
-/
theorem Dr1_eq (F : LFlag S r T) (F' : LFlag S r T') : Dr1 F F' = (ZhatL F F').det := by
  show leadMinorE (Zhat F.fl F'.fl) (r + 1) = _
  unfold leadMinorE
  rw [dif_pos le_rfl]
  have hc : (Fin.castLE (le_refl (r + 1))) = id := funext fun i => Fin.ext rfl
  rw [hc, Matrix.submatrix_id_id]

/- English proof (translation)
Establish `h1` using `GlobalTheory.SA.TransvG.det_fromBlocks_last (ZhatL F F') (ZhatL F F')ᴴ T T'`. Unfold `gramM`. Rewrite using `[h1]`. Use `congr 1`. Establish `hr : Dl F.fl F'.fl r = ((ZhatL F F').submatrix Fin.castSucc Fin.castSucc).det` using `by show leadMinorE (Zhat F.fl F'.fl) r = _`.

Unfold `leadMinorE`. Rewrite using `[dif_pos (Nat.le_succ r)]`. Both sides reduce to the same expression. Establish `hr1 : Dl F.fl F'.fl (r + 1) = (ZhatL F F').det` using `Dr1_eq F F'`. Use `show _ = Gflag F.fl F'.fl`.

Unfold `Gflag`. Rewrite using `[hr, hr1, Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]`.
-/
theorem gramM_det (F : LFlag S r T) (F' : LFlag S r T') : (gramM F F').det = (-1) ^ (r + 1) * Gval F F' := by
  have h1 := GlobalTheory.SA.TransvG.det_fromBlocks_last (ZhatL F F') (ZhatL F F')ᴴ T T'
  unfold gramM
  rw [h1]
  congr 1
  have hr : Dl F.fl F'.fl r = ((ZhatL F F').submatrix Fin.castSucc Fin.castSucc).det := by
    show leadMinorE (Zhat F.fl F'.fl) r = _
    unfold leadMinorE
    rw [dif_pos (Nat.le_succ r)]
    rfl
  have hr1 : Dl F.fl F'.fl (r + 1) = (ZhatL F F').det := Dr1_eq F F'
  show _ = Gflag F.fl F'.fl
  unfold Gflag
  rw [hr, hr1, Matrix.det_conjTranspose, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose]

/- English proof (translation)
Rewrite using `[Matrix.mulVec_diagonal, if_neg (Fin.castSucc_ne_last i), zero_mul]`.
-/
theorem diag_cast (t : E) (c : Fin (r + 1) → E) (i : Fin r) :
    ((diagonal fun a : Fin (r + 1) => if a = Fin.last r then t else 0) *ᵥ c) i.castSucc = 0 := by
  rw [Matrix.mulVec_diagonal, if_neg (Fin.castSucc_ne_last i), zero_mul]

/- English proof (translation)
Establish `hU : IsUnit Mx.det` using `isUnit_iff_ne_zero.mpr hM`. Establish `h1` using `congrArg (fun t => Mx⁻¹ *ᵥ t) h`. Simplify `h1` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU]`.
-/
private lemma cancel_lemma {N : Type} [Fintype N] [DecidableEq N] {Mx : Matrix N N E} (hM : Mx.det ≠ 0)
    {w w' : N → E} (h : Mx *ᵥ w = Mx *ᵥ w') : w = w' := by
  have hU : IsUnit Mx.det := isUnit_iff_ne_zero.mpr hM
  have h1 := congrArg (fun t => Mx⁻¹ *ᵥ t) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hU] using h1

/- English proof (translation)
Take `⟨Z, hZ⟩ : ∃ Z, Z = ZhatL F F'` from `⟨_, rfl⟩`. Rewrite `ha` using `[← hZ]`. Establish `hΛint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x)` using `fun x hx => (mem_unimod hΛ x).1 hx`. Establish `hZD : Z.det = Dr1 F F'` using `by rw [hZ, Dr1_eq]`. Establish `hZdet : Z.det ≠ 0` using `by rw [hZD]; exact hD`.

Establish `hZU : IsUnit Z.det` using `isUnit_iff_ne_zero.mpr hZdet`. Establish `haU : IsUpUni a` using `ha.1`. Take `⟨Lm, hLm⟩ : ∃ L, L = Z * a * Z⁻¹` from `⟨_, rfl⟩`. Establish `hL : IsLoUni Lm` using `hLm ▸ ha.2`. Establish `hLZ : Lm * Z = Z * a` using `by rw [hLm]; exact Matrix.nonsing_inv_mul_cancel_right _ _ hZU`.

Establish `hLU : IsUnit Lm.det` using `by rw [lo_det hL]; exact isUnit_one`. Take `⟨b, hb⟩ : ∃ b, b = (Lm⁻¹)ᴴ` from `⟨_, rfl⟩`. Establish `hbU : IsUpUni b` using `hb ▸ lo_conjT (lo_inv hL)`. Establish `hbZa : bᴴ * Z * a = Z`. Rewrite using `[hb, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← hLZ, Matrix.nonsing_inv_mul_cancel_left _ _ hLU]`.

Establish `hAZb : aᴴ * Zᴴ * b = Zᴴ`. Establish `h1` using `congrArg Matrix.conjTranspose hbZa`. Simplify `h1` using `[Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Establish `ha_det : a.det = 1`. Establish `h1` using `lo_det (up_conjT haU)`.

Rewrite `h1` using `[Matrix.det_conjTranspose]`. Simplify using `using congrArg star h1`. Establish `haU' : IsUnit a.det` using `by rw [ha_det]; exact isUnit_one`. Establish `hainv : a⁻¹ = a.adjugate` using `by rw [Matrix.inv_def, ha_det, Ring.inverse_one, one_smul]`. Establish `hZinv : Z⁻¹ = (Z.det)⁻¹ • Z.adjugate` using `by rw [Matrix.inv_def, Ring.inverse_eq_inv']`.

Establish `hLinv : Lm⁻¹ = Z * a.adjugate * Z⁻¹`. Rewrite using `[hLm, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZU, hainv, Matrix.mul_assoc]`. Establish `hadj_a : a.adjugate * a = 1` using `by rw [← hainv]; exact Matrix.nonsing_inv_mul _ haU'`. Establish `hL1 : Lm⁻¹ - 1 = (-Gval F F') • (Z * a.adjugate * M * Z.adjugate)`. Rewrite using `[hLinv]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hadj_a, Matrix.mul_one, Matrix.mul_nonsing_inv _ hZU]`. Use `_ = -(Z * a.adjugate * (a - 1) * Z⁻¹) := by`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Use `_ = (-Gval F F') • (Z * a.adjugate * M * Z.adjugate) := by`. Rewrite using `[haM, hZinv, hZD]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]`. Use `congr 1`. Clear the denominators using the available nonvanishing facts.

Take `⟨v, hvdef⟩ : ∃ v : Fin (r + 1) ⊕ Fin (r + 1) → S.V, v = Sum.elim (frame F) (frame F')` from `⟨_, rfl⟩`. Establish `hΓ : ∀ p q, gramM F F' p q = S.hT (v p) (v q)` using `by rw [hvdef]; exact gramM_apply F F'`. Establish `hΓdef : gramM F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) Z Zᴴ (diagonal fun a => if a = Fin.last r then -T' else 0)` using `by rw [hZ]; rfl`. Establish `hv : ∀ p, v p ∈ Λ`. Rewrite using `[hvdef]`.

Introduce and unpack `(p | p)`. Conclude with `hF p`. Conclude with `hF' p`. Establish `hΓH : (gramM F F')ᴴ = gramM F F'`. Use extensionality with `p q`.

Rewrite using `[Matrix.conjTranspose_apply, hΓ, hΓ, herm' (v p) (v q)]`. Establish `hε : ((-1 : E) ^ (r + 1)) ≠ 0` using `pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)`. Establish `hGstar : star (Gval F F') = Gval F F'`. Establish `h1 : star (gramM F F').det = (gramM F F').det` using `by rw [← Matrix.det_conjTranspose, hΓH]`. Rewrite `h1` using `[gramM_det, star_mul', star_pow, star_neg, star_one]`.

Conclude with `mul_left_cancel₀ hε h1`. Establish `hb1 : b - 1 = Gval F F' • -(Z * a.adjugate * M * Z.adjugate)ᴴ`. Establish `h1 : b - 1 = (Lm⁻¹ - 1)ᴴ` using `by rw [hb, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]`. Rewrite using `[h1, hL1, Matrix.conjTranspose_smul, star_neg, hGstar, smul_neg, neg_smul]`. Establish `ha1 : a - 1 = Gval F F' • (Dr1 F F' • M)` using `by rw [haM, mul_smul]`.

Establish `hΓint : AllInt (gramM F F')` using `fun p q => by rw [hΓ]; exact hΛint _ (hv q) _ (hv p)`. Establish `hZint : AllInt Z` using `fun i j => by`. Establish `h1` using `hΓint (Sum.inl i) (Sum.inr j)`. Rewrite `h1` using `[hΓdef, Matrix.fromBlocks_apply₁₂]`. Then use the resulting hypothesis. Establish `hGint : IsIntegral ℤ (Gval F F')`.

Establish `h1 : Gval F F' = (-1) ^ (r + 1) * (gramM F F').det`. Rewrite using `[gramM_det, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Rewrite using `[h1]`. Conclude with `(isIntegral_one.neg.pow _).mul hΓint.det`. Establish `hDint : IsIntegral ℤ (Dr1 F F')` using `by rw [← hZD]; exact hZint.det`.

Establish `haint : AllInt a`. Establish `h1 : a = 1 + (Gval F F' * Dr1 F F') • M` using `by rw [← haM]; abel`. Rewrite using `[h1]`. Introduce `i j`. Rewrite using `[Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `(allInt_one i j).add ((hGint.mul hDint).mul (hM i j))`. Take `⟨Q, hQ⟩ : ∃ Q, Q = Z * a.adjugate * M * Z.adjugate` from `⟨_, rfl⟩`. Establish `hQint : AllInt Q` using `by rw [hQ]; exact ((hZint.mul haint.adj).mul hM).mul hZint.adj`. Rewrite `hb1` using `[← hQ]`. Take `⟨P, hP⟩ : ∃ P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E, P = fromBlocks (-Qᴴ) 0 0 (Dr1 F F' • M)` from `⟨_, rfl⟩`.

Establish `hPint : AllInt P`. Rewrite using `[hP]`. Introduce and unpack `(i | i) (j | j)`. Rewrite using `[Matrix.fromBlocks_apply₁₁, Matrix.neg_apply]`. Conclude with `(hQint.conjT i j).neg`.

Rewrite using `[Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]`. Conclude with `isIntegral_zero`. Rewrite using `[Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]`. Conclude with `isIntegral_zero`. Rewrite using `[Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `hDint.mul (hM i j)`. Take `⟨A, hAdef⟩ : ∃ A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E, A = fromBlocks b 0 0 a` from `⟨_, rfl⟩`. Establish `hAΓA : Aᴴ * gramM F F' * A = gramM F F'`. Rewrite using `[hΓdef, hAdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]`. Simplify using `only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]`.

Rewrite using `[up_diag hbU, up_diag haU, hbZa, hAZb]`. Establish `hΓdet : (gramM F F').det ≠ 0` using `by rw [gramM_det]; exact mul_ne_zero hε hG`. Establish `hΓU : IsUnit (gramM F F').det` using `isUnit_iff_ne_zero.mpr hΓdet`. Take `⟨n, hniso, hn⟩` from `exists_isom v (gramM F F') A hΓ hΓdet hAΓA`. Establish `hnv : ∀ q, n (v q) = ∑ p, A p q • v p`.

Introduce `q`. Rewrite using `[hn]`. Establish `hcol : (fun p => S.hT (v p) (v q)) = gramM F F' *ᵥ Pi.single q 1`. Use function extensionality and compare the values at `p`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, hΓ]`.

Rewrite using `[hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΓU, Matrix.mul_one]`. Simplify using `[Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.sub_apply, Matrix.one_apply, sub_smul, Finset.sum_sub_distrib]`. Establish `hnF' : ∀ c, n (frame F' c) = ∑ i, a i c • frame F' i`. Introduce `c`. Establish `h1` using `hnv (Sum.inr c)`.

Simplify `h1` using `[hvdef, hAdef, Fintype.sum_sum_type]`. Establish `hnF : ∀ c, n (frame F c) = ∑ i, b i c • frame F i`. Introduce `c`. Establish `h1` using `hnv (Sum.inl c)`. Simplify `h1` using `[hvdef, hAdef, Fintype.sum_sum_type]`.

Establish `hA1 : A - 1 = Gval F F' • P`. Establish `h1 : A - 1 = fromBlocks (b - 1) 0 0 (a - 1)`. Rewrite using `[hAdef]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`. Rewrite using `[h1, hP, Matrix.fromBlocks_smul, smul_zero, ← hb1, ← ha1]`.

Establish `hAG : (A - 1) * (gramM F F')⁻¹ = ((-1 : E) ^ (r + 1)) • (P * (gramM F F').adjugate)`. Rewrite using `[hA1, Matrix.inv_def, Ring.inverse_eq_inv', gramM_det, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `congr 1`. Rewrite using `[mul_inv, mul_left_comm, mul_inv_cancel₀ hG, mul_one, ← inv_pow, inv_neg, inv_one]`. Establish `hcoef : AllInt ((A - 1) * (gramM F F')⁻¹)`.

Rewrite using `[hAG]`. Introduce `i j`. Rewrite using `[Matrix.smul_apply, smul_eq_mul]`. Conclude with `(isIntegral_one.neg.pow _).mul ((hPint.mul hΓint.adj) i j)`. Establish `hnΛ : ∀ x ∈ Λ, n x ∈ Λ`.

Introduce `x hx`. Rewrite using `[hn]`. Use `Λ.add_mem hx (Submodule.sum_mem _ fun p _ => int_smul_mem ?_ (hv p))` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_mulVec]`. Simplify using `only [Matrix.mulVec, dotProduct]`.

Conclude with `IsIntegral.sum _ fun q _ => (hcoef p q).mul (hΛint _ hx _ (hv q))`. Establish `hAut : IsAutLam S Λ n` using `isAutLam_of_mapsTo hΛ hniso hnΛ`. Establish `hcv : ∀ x, gramM F F' *ᵥ ((gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x) = fun q => S.hT (v q) x`. Introduce `x`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΓU, Matrix.one_mulVec]`.

Establish `hAm1 : A - 1 = fromBlocks (b - 1) 0 0 (a - 1)`. Rewrite using `[hAdef]`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [Matrix.one_apply]`. Establish `hXe : ∀ i : Fin r, F.fl.e i ∈ Xsp F` using `fun i => by show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`.

Establish `hXe' : ∀ i : Fin r, F'.fl.e i ∈ Xsp F'` using `fun i => by show F'.fl.e i ∈ Submodule.span E (Set.range F'.fl.e)`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Establish `horthF : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F`. Introduce `x hx`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx`.

Take `⟨u, hu⟩ : ∃ u, u = (gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x` from `⟨_, rfl⟩`. Establish `hGu : gramM F F' *ᵥ u = fun q => S.hT (v q) x` using `by rw [hu]; exact hcv x`. Establish `hy : ∀ i : Fin r, (Z *ᵥ (u ∘ Sum.inr)) i.castSucc = 0`. Introduce `i`. Establish `h1` using `congrFun hGu (Sum.inl i.castSucc)`.

Rewrite `h1` using `[hΓdef, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, diag_cast, zero_add]`. Rewrite using `[h1]`. Use `show S.hT (v (Sum.inl i.castSucc)) x = 0`. Rewrite using `[hvdef, Sum.elim_inl, frame_cast]`. Conclude with `hx _ (hXe i)`.

Establish `hau : (a - 1) *ᵥ (u ∘ Sum.inr) = 0`. Establish `h2 : Z *ᵥ (a *ᵥ (u ∘ Sum.inr)) = Z *ᵥ (u ∘ Sum.inr)`. Rewrite using `[Matrix.mulVec_mulVec, ← hLZ, ← Matrix.mulVec_mulVec, lo_mulVec hL _ hy]`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, cancel_lemma hZdet h2, sub_self]`. Rewrite using `[hn, add_sub_cancel_left, ← hu, Fintype.sum_sum_type, hAm1, Matrix.fromBlocks_mulVec]`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add, hau, Pi.zero_apply, zero_smul, Finset.sum_const_zero, hvdef, Pi.add_apply]`. Conclude with `comb_mem_X F _ (up_last hbU _)`. Establish `horthF' : ∀ x ∈ orth S (Xsp F'), n x - x ∈ Xsp F'`. Introduce `x hx`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx`.

Take `⟨u, hu⟩ : ∃ u, u = (gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x` from `⟨_, rfl⟩`. Establish `hGu : gramM F F' *ᵥ u = fun q => S.hT (v q) x` using `by rw [hu]; exact hcv x`. Establish `hy : ∀ j : Fin r, (Zᴴ *ᵥ (u ∘ Sum.inl)) j.castSucc = 0`. Introduce `j`. Establish `h1` using `congrFun hGu (Sum.inr j.castSucc)`.

Rewrite `h1` using `[hΓdef, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, diag_cast, add_zero]`. Rewrite using `[h1]`. Use `show S.hT (v (Sum.inr j.castSucc)) x = 0`. Rewrite using `[hvdef, Sum.elim_inr, frame_cast]`. Conclude with `hx _ (hXe' j)`.

Establish `hbu : (b - 1) *ᵥ (u ∘ Sum.inl) = 0`. Establish `hZH : (Zᴴ).det ≠ 0` using `by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hZdet`. Establish `haH : (aᴴ).det ≠ 0` using `by rw [lo_det (up_conjT haU)]; exact one_ne_zero`. Establish `h2 : aᴴ *ᵥ (Zᴴ *ᵥ (b *ᵥ (u ∘ Sum.inl))) = aᴴ *ᵥ (Zᴴ *ᵥ (u ∘ Sum.inl))`. Rewrite using `[lo_mulVec (up_conjT haU) _ hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAZb]`.

Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, cancel_lemma hZH (cancel_lemma haH h2), sub_self]`. Rewrite using `[hn, add_sub_cancel_left, ← hu, Fintype.sum_sum_type, hAm1, Matrix.fromBlocks_mulVec]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add, hbu, Pi.zero_apply, zero_smul, Finset.sum_const_zero, hvdef, Pi.add_apply]`. Conclude with `comb_mem_X F' _ (up_last haU _)`. Conclude with `⟨n, ⟨⟨hAut, fun j => flag_step F n hbU hnF j, horthF⟩, ⟨hAut, fun j => flag_step F' n haU hnF' j, horthF'⟩⟩, hnF'⟩`.
-/
theorem main_gen {Λ : Submodule (𝓞 E) S.V} (hΛ : Formalism.HermitianLatticesTheory.IsUnimodular S.hT Λ)
    (F : LFlag S r T) (F' : LFlag S r T') (hF : ∀ b, frame F b ∈ Λ) (hF' : ∀ b, frame F' b ∈ Λ)
    (hG : Gval F F' ≠ 0) (hD : Dr1 F F' ≠ 0) {a M : Matrix (Fin (r + 1)) (Fin (r + 1)) E}
    (ha : a ∈ stabU (ZhatL F F')) (hM : AllInt M) (haM : a - 1 = (Gval F F' * Dr1 F F') • M) :
    ∃ n ∈ NLam Λ F ∩ NLam Λ F', ∀ c, n (frame F' c) = ∑ i, a i c • frame F' i := by
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ZhatL F F' := ⟨_, rfl⟩
  rw [← hZ] at ha
  have hΛint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT y x) := fun x hx => (mem_unimod hΛ x).1 hx
  have hZD : Z.det = Dr1 F F' := by rw [hZ, Dr1_eq]
  have hZdet : Z.det ≠ 0 := by rw [hZD]; exact hD
  have hZU : IsUnit Z.det := isUnit_iff_ne_zero.mpr hZdet
  have haU : IsUpUni a := ha.1
  obtain ⟨Lm, hLm⟩ : ∃ L, L = Z * a * Z⁻¹ := ⟨_, rfl⟩
  have hL : IsLoUni Lm := hLm ▸ ha.2
  have hLZ : Lm * Z = Z * a := by rw [hLm]; exact Matrix.nonsing_inv_mul_cancel_right _ _ hZU
  have hLU : IsUnit Lm.det := by rw [lo_det hL]; exact isUnit_one
  obtain ⟨b, hb⟩ : ∃ b, b = (Lm⁻¹)ᴴ := ⟨_, rfl⟩
  have hbU : IsUpUni b := hb ▸ lo_conjT (lo_inv hL)
  have hbZa : bᴴ * Z * a = Z := by
    rw [hb, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← hLZ, Matrix.nonsing_inv_mul_cancel_left _ _ hLU]
  have hAZb : aᴴ * Zᴴ * b = Zᴴ := by
    have h1 := congrArg Matrix.conjTranspose hbZa
    simpa [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h1
  have ha_det : a.det = 1 := by
    have h1 := lo_det (up_conjT haU)
    rw [Matrix.det_conjTranspose] at h1
    simpa using congrArg star h1
  have haU' : IsUnit a.det := by rw [ha_det]; exact isUnit_one
  have hainv : a⁻¹ = a.adjugate := by rw [Matrix.inv_def, ha_det, Ring.inverse_one, one_smul]
  have hZinv : Z⁻¹ = (Z.det)⁻¹ • Z.adjugate := by rw [Matrix.inv_def, Ring.inverse_eq_inv']
  have hLinv : Lm⁻¹ = Z * a.adjugate * Z⁻¹ := by
    rw [hLm, Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hZU, hainv, Matrix.mul_assoc]
  have hadj_a : a.adjugate * a = 1 := by rw [← hainv]; exact Matrix.nonsing_inv_mul _ haU'
  have hL1 : Lm⁻¹ - 1 = (-Gval F F') • (Z * a.adjugate * M * Z.adjugate) := by
    rw [hLinv]
    calc Z * a.adjugate * Z⁻¹ - 1 = Z * a.adjugate * Z⁻¹ - Z * (a.adjugate * a) * Z⁻¹ := by
          rw [hadj_a, Matrix.mul_one, Matrix.mul_nonsing_inv _ hZU]
      _ = -(Z * a.adjugate * (a - 1) * Z⁻¹) := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
          abel
      _ = (-Gval F F') • (Z * a.adjugate * M * Z.adjugate) := by
          rw [haM, hZinv, hZD]
          simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← neg_smul]
          congr 1
          field_simp
  obtain ⟨v, hvdef⟩ : ∃ v : Fin (r + 1) ⊕ Fin (r + 1) → S.V, v = Sum.elim (frame F) (frame F') := ⟨_, rfl⟩
  have hΓ : ∀ p q, gramM F F' p q = S.hT (v p) (v q) := by rw [hvdef]; exact gramM_apply F F'
  have hΓdef : gramM F F' = fromBlocks (diagonal fun a => if a = Fin.last r then -T else 0) Z Zᴴ
      (diagonal fun a => if a = Fin.last r then -T' else 0) := by rw [hZ]; rfl
  have hv : ∀ p, v p ∈ Λ := by
    rw [hvdef]
    rintro (p | p)
    · exact hF p
    · exact hF' p
  have hΓH : (gramM F F')ᴴ = gramM F F' := by
    ext p q
    rw [Matrix.conjTranspose_apply, hΓ, hΓ, herm' (v p) (v q)]
  have hε : ((-1 : E) ^ (r + 1)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hGstar : star (Gval F F') = Gval F F' := by
    have h1 : star (gramM F F').det = (gramM F F').det := by rw [← Matrix.det_conjTranspose, hΓH]
    rw [gramM_det, star_mul', star_pow, star_neg, star_one] at h1
    exact mul_left_cancel₀ hε h1
  have hb1 : b - 1 = Gval F F' • -(Z * a.adjugate * M * Z.adjugate)ᴴ := by
    have h1 : b - 1 = (Lm⁻¹ - 1)ᴴ := by rw [hb, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    rw [h1, hL1, Matrix.conjTranspose_smul, star_neg, hGstar, smul_neg, neg_smul]
  have ha1 : a - 1 = Gval F F' • (Dr1 F F' • M) := by rw [haM, mul_smul]
  have hΓint : AllInt (gramM F F') := fun p q => by rw [hΓ]; exact hΛint _ (hv q) _ (hv p)
  have hZint : AllInt Z := fun i j => by
    have h1 := hΓint (Sum.inl i) (Sum.inr j)
    rwa [hΓdef, Matrix.fromBlocks_apply₁₂] at h1
  have hGint : IsIntegral ℤ (Gval F F') := by
    have h1 : Gval F F' = (-1) ^ (r + 1) * (gramM F F').det := by
      rw [gramM_det, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    rw [h1]
    exact (isIntegral_one.neg.pow _).mul hΓint.det
  have hDint : IsIntegral ℤ (Dr1 F F') := by rw [← hZD]; exact hZint.det
  have haint : AllInt a := by
    have h1 : a = 1 + (Gval F F' * Dr1 F F') • M := by rw [← haM]; abel
    rw [h1]
    intro i j
    rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (allInt_one i j).add ((hGint.mul hDint).mul (hM i j))
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = Z * a.adjugate * M * Z.adjugate := ⟨_, rfl⟩
  have hQint : AllInt Q := by rw [hQ]; exact ((hZint.mul haint.adj).mul hM).mul hZint.adj
  rw [← hQ] at hb1
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E,
      P = fromBlocks (-Qᴴ) 0 0 (Dr1 F F' • M) := ⟨_, rfl⟩
  have hPint : AllInt P := by
    rw [hP]
    rintro (i | i) (j | j)
    · rw [Matrix.fromBlocks_apply₁₁, Matrix.neg_apply]; exact (hQint.conjT i j).neg
    · rw [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact isIntegral_zero
    · rw [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact isIntegral_zero
    · rw [Matrix.fromBlocks_apply₂₂, Matrix.smul_apply, smul_eq_mul]; exact hDint.mul (hM i j)
  obtain ⟨A, hAdef⟩ : ∃ A : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) E,
      A = fromBlocks b 0 0 a := ⟨_, rfl⟩
  have hAΓA : Aᴴ * gramM F F' * A = gramM F F' := by
    rw [hΓdef, hAdef, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    rw [up_diag hbU, up_diag haU, hbZa, hAZb]
  have hΓdet : (gramM F F').det ≠ 0 := by rw [gramM_det]; exact mul_ne_zero hε hG
  have hΓU : IsUnit (gramM F F').det := isUnit_iff_ne_zero.mpr hΓdet
  obtain ⟨n, hniso, hn⟩ := exists_isom v (gramM F F') A hΓ hΓdet hAΓA
  have hnv : ∀ q, n (v q) = ∑ p, A p q • v p := by
    intro q
    rw [hn]
    have hcol : (fun p => S.hT (v p) (v q)) = gramM F F' *ᵥ Pi.single q 1 := by
      funext p
      simp [Matrix.mulVec, dotProduct, Pi.single_apply, hΓ]
    rw [hcol, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hΓU, Matrix.mul_one]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.sub_apply, Matrix.one_apply, sub_smul,
      Finset.sum_sub_distrib]
  have hnF' : ∀ c, n (frame F' c) = ∑ i, a i c • frame F' i := by
    intro c
    have h1 := hnv (Sum.inr c)
    simpa [hvdef, hAdef, Fintype.sum_sum_type] using h1
  have hnF : ∀ c, n (frame F c) = ∑ i, b i c • frame F i := by
    intro c
    have h1 := hnv (Sum.inl c)
    simpa [hvdef, hAdef, Fintype.sum_sum_type] using h1
  have hA1 : A - 1 = Gval F F' • P := by
    have h1 : A - 1 = fromBlocks (b - 1) 0 0 (a - 1) := by
      rw [hAdef]
      ext (i | i) (j | j) <;> simp [Matrix.one_apply]
    rw [h1, hP, Matrix.fromBlocks_smul, smul_zero, ← hb1, ← ha1]
  have hAG : (A - 1) * (gramM F F')⁻¹ = ((-1 : E) ^ (r + 1)) • (P * (gramM F F').adjugate) := by
    rw [hA1, Matrix.inv_def, Ring.inverse_eq_inv', gramM_det, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    congr 1
    rw [mul_inv, mul_left_comm, mul_inv_cancel₀ hG, mul_one, ← inv_pow, inv_neg, inv_one]
  have hcoef : AllInt ((A - 1) * (gramM F F')⁻¹) := by
    rw [hAG]
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isIntegral_one.neg.pow _).mul ((hPint.mul hΓint.adj) i j)
  have hnΛ : ∀ x ∈ Λ, n x ∈ Λ := by
    intro x hx
    rw [hn]
    refine Λ.add_mem hx (Submodule.sum_mem _ fun p _ => int_smul_mem ?_ (hv p))
    rw [Matrix.mulVec_mulVec]
    simp only [Matrix.mulVec, dotProduct]
    exact IsIntegral.sum _ fun q _ => (hcoef p q).mul (hΛint _ hx _ (hv q))
  have hAut : IsAutLam S Λ n := isAutLam_of_mapsTo hΛ hniso hnΛ
  have hcv : ∀ x, gramM F F' *ᵥ ((gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x) = fun q => S.hT (v q) x := by
    intro x
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hΓU, Matrix.one_mulVec]
  have hAm1 : A - 1 = fromBlocks (b - 1) 0 0 (a - 1) := by
    rw [hAdef]
    ext (i | i) (j | j) <;> simp [Matrix.one_apply]
  have hXe : ∀ i : Fin r, F.fl.e i ∈ Xsp F := fun i => by
    show F.fl.e i ∈ Submodule.span E (Set.range F.fl.e)
    exact Submodule.subset_span ⟨i, rfl⟩
  have hXe' : ∀ i : Fin r, F'.fl.e i ∈ Xsp F' := fun i => by
    show F'.fl.e i ∈ Submodule.span E (Set.range F'.fl.e)
    exact Submodule.subset_span ⟨i, rfl⟩
  have horthF : ∀ x ∈ orth S (Xsp F), n x - x ∈ Xsp F := by
    intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    obtain ⟨u, hu⟩ : ∃ u, u = (gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x := ⟨_, rfl⟩
    have hGu : gramM F F' *ᵥ u = fun q => S.hT (v q) x := by rw [hu]; exact hcv x
    have hy : ∀ i : Fin r, (Z *ᵥ (u ∘ Sum.inr)) i.castSucc = 0 := by
      intro i
      have h1 := congrFun hGu (Sum.inl i.castSucc)
      rw [hΓdef, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, diag_cast, zero_add] at h1
      rw [h1]
      show S.hT (v (Sum.inl i.castSucc)) x = 0
      rw [hvdef, Sum.elim_inl, frame_cast]
      exact hx _ (hXe i)
    have hau : (a - 1) *ᵥ (u ∘ Sum.inr) = 0 := by
      have h2 : Z *ᵥ (a *ᵥ (u ∘ Sum.inr)) = Z *ᵥ (u ∘ Sum.inr) := by
        rw [Matrix.mulVec_mulVec, ← hLZ, ← Matrix.mulVec_mulVec, lo_mulVec hL _ hy]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, cancel_lemma hZdet h2, sub_self]
    rw [hn, add_sub_cancel_left, ← hu, Fintype.sum_sum_type, hAm1, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add, hau, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, hvdef, Pi.add_apply]
    exact comb_mem_X F _ (up_last hbU _)
  have horthF' : ∀ x ∈ orth S (Xsp F'), n x - x ∈ Xsp F' := by
    intro x hx
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hx
    obtain ⟨u, hu⟩ : ∃ u, u = (gramM F F')⁻¹ *ᵥ fun q => S.hT (v q) x := ⟨_, rfl⟩
    have hGu : gramM F F' *ᵥ u = fun q => S.hT (v q) x := by rw [hu]; exact hcv x
    have hy : ∀ j : Fin r, (Zᴴ *ᵥ (u ∘ Sum.inl)) j.castSucc = 0 := by
      intro j
      have h1 := congrFun hGu (Sum.inr j.castSucc)
      rw [hΓdef, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, diag_cast, add_zero] at h1
      rw [h1]
      show S.hT (v (Sum.inr j.castSucc)) x = 0
      rw [hvdef, Sum.elim_inr, frame_cast]
      exact hx _ (hXe' j)
    have hbu : (b - 1) *ᵥ (u ∘ Sum.inl) = 0 := by
      have hZH : (Zᴴ).det ≠ 0 := by rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hZdet
      have haH : (aᴴ).det ≠ 0 := by rw [lo_det (up_conjT haU)]; exact one_ne_zero
      have h2 : aᴴ *ᵥ (Zᴴ *ᵥ (b *ᵥ (u ∘ Sum.inl))) = aᴴ *ᵥ (Zᴴ *ᵥ (u ∘ Sum.inl)) := by
        rw [lo_mulVec (up_conjT haU) _ hy, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hAZb]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, cancel_lemma hZH (cancel_lemma haH h2), sub_self]
    rw [hn, add_sub_cancel_left, ← hu, Fintype.sum_sum_type, hAm1, Matrix.fromBlocks_mulVec]
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add, hbu, Pi.zero_apply, zero_smul,
      Finset.sum_const_zero, hvdef, Pi.add_apply]
    exact comb_mem_X F' _ (up_last haU _)
  exact ⟨n, ⟨⟨hAut, fun j => flag_step F n hbU hnF j, horthF⟩, ⟨hAut, fun j => flag_step F' n haU hnF' j, horthF'⟩⟩,
    hnF'⟩

end Lat

section Det

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

/- English proof (translation)
Introduce `hD0`. Establish `hZ0 : (ZhatL F F').det = 0` using `by rw [← Dr1_eq]; exact hD0`. Take `⟨w, hw0, hZw⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hZ0`. Take `⟨y, hy⟩ : ∃ y, y = ∑ b, w b • frame F' b` from `⟨_, rfl⟩`. Establish `hperp : ∀ c, S.hT (frame F c) y = 0`.

Introduce `c`. Rewrite using `[hy, map_sum]`. Simplify using `only [map_smul, smul_eq_mul]`. Establish `h1` using `congrFun hZw c`. Simplify using `only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1`.

Rewrite using `[← h1]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`. Both sides reduce to the same expression. Establish `hΓdet : (gramM F F').det ≠ 0`.

Rewrite using `[gramM_det]`. Conclude with `mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hG`. Establish `hindep : ∀ s : Fin (r + 1) ⊕ Fin (r + 1) → E, ∑ p, s p • Sum.elim (frame F) (frame F') p = 0 → s = 0`. Introduce `s hs`. Establish `h1 : gramM F F' *ᵥ s = gramM F F' *ᵥ 0`.

Rewrite using `[Matrix.mulVec_zero]`. Use function extensionality and compare the values at `p`. Establish `h2` using `congrArg (S.hT (Sum.elim (frame F) (frame F') p)) hs`. Rewrite `h2` using `[map_sum, map_zero]`. Simplify using `only [map_smul, smul_eq_mul] at h2`.

Rewrite using `[Pi.zero_apply, ← h2]`. Simplify using `only [Matrix.mulVec, dotProduct, gramM_apply]`. Conclude with `Finset.sum_congr rfl fun q _ => mul_comm _ _`. Conclude with `cancel_lemma hΓdet h1`. Establish `hyX : y ∈ orth S (Xplus F)`.

Establish `hle : Xplus F ≤ LinearMap.ker (S.hT.flip y)` using `by show F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _`. Use `sup_le ?_ ?_` and prove the remaining obligations. Use `show Submodule.span E (Set.range F.fl.e) ≤ _`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`.

Use `show S.hT (F.fl.e i) y = 0`. Rewrite using `[← frame_cast]`. Conclude with `hperp _`. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff] show S.hT F.fl.z y = 0`. Rewrite using `[← frame_last]`.

Conclude with `hperp _`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `x hx`. Conclude with `hle hx`. Distinguish the cases in `hyin : y ∈ Xsp F`.

Take `⟨t, ht⟩` from `(Submodule.mem_span_range_iff_exists_fun E).mp (show y ∈ Submodule.span E (Set.range F.fl.e) from hyin)`. Establish `hs` using `hindep (Sum.elim (Fin.snoc (α := fun _ => E) t 0) (-w)) (by`. Rewrite using `[Fintype.sum_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, zero_smul, add_zero, frame_cast, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ht, hy]`. Conclude with `add_neg_cancel _)`.

Apply `hw0` to reduce the goal to its premises. Use function extensionality and compare the values at `b`. Establish `h1` using `congrFun hs (Sum.inr b)`. Simplify using `using h1`. Establish `hp` using `hpos y hyX hyin`.

Establish `hyy : S.hT y y = star (w (Fin.last r)) * w (Fin.last r) * -(T' : E)`. Establish `h1 : ∀ b, S.hT (frame F' b) y = w b * (if b = Fin.last r then -(T' : E) else 0)`. Introduce `b`. Rewrite using `[hy, map_sum]`. Simplify using `only [map_smul, smul_eq_mul, gram_self, Matrix.diagonal_apply]`.

Rewrite using `[Finset.sum_eq_single b]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules.

Establish `e : S.hT (∑ b, w b • frame F' b) y = star w ⬝ᵥ fun p => S.hT (frame F' p) y` using `hT_comb_left _ _ _`. Rewrite using `[show S.hT y y = S.hT (∑ b, w b • frame F' b) y by rw [← hy], e]`. Simplify using `only [dotProduct, Pi.star_apply, h1]`. Rewrite using `[Finset.sum_eq_single (Fin.last r)]`. Rewrite using `[if_pos rfl]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `c _ hc`. Simplify using `[hc]`. Simplify using the standard rewrite rules. Rewrite `hp` using `[hyy, map_mul, map_mul, hτ, map_neg, map_natCast]`.

Establish `h2 : (starRingEnd ℂ (τ (w (Fin.last r))) * τ (w (Fin.last r)) * -(T' : ℂ)).re = -(T' : ℝ) * Complex.normSq (τ (w (Fin.last r)))`. Rewrite using `[mul_comm (starRingEnd ℂ _), Complex.mul_conj]`. Simplify using `[Complex.ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hp` using `[h2]`.

Establish `h3 : 0 ≤ (T' : ℝ) * Complex.normSq (τ (w (Fin.last r)))` using `mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem Dr1_ne_zero {T' : ℕ} (F : LFlag S r T) (F' : LFlag S r (T' : E)) (τ : E →+* ℂ)
    (hτ : ∀ a, τ (star a) = starRingEnd ℂ (τ a))
    (hpos : ∀ x ∈ orth S (Xplus F), x ∉ Xsp F → 0 < (τ (S.hT x x)).re) (hG : Gval F F' ≠ 0) :
    Dr1 F F' ≠ 0 := by
  intro hD0
  have hZ0 : (ZhatL F F').det = 0 := by rw [← Dr1_eq]; exact hD0
  obtain ⟨w, hw0, hZw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hZ0
  obtain ⟨y, hy⟩ : ∃ y, y = ∑ b, w b • frame F' b := ⟨_, rfl⟩
  have hperp : ∀ c, S.hT (frame F c) y = 0 := by
    intro c
    rw [hy, map_sum]
    simp only [map_smul, smul_eq_mul]
    have h1 := congrFun hZw c
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]
    rfl
  have hΓdet : (gramM F F').det ≠ 0 := by
    rw [gramM_det]; exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)) hG
  have hindep : ∀ s : Fin (r + 1) ⊕ Fin (r + 1) → E,
      ∑ p, s p • Sum.elim (frame F) (frame F') p = 0 → s = 0 := by
    intro s hs
    have h1 : gramM F F' *ᵥ s = gramM F F' *ᵥ 0 := by
      rw [Matrix.mulVec_zero]
      funext p
      have h2 := congrArg (S.hT (Sum.elim (frame F) (frame F') p)) hs
      rw [map_sum, map_zero] at h2
      simp only [map_smul, smul_eq_mul] at h2
      rw [Pi.zero_apply, ← h2]
      simp only [Matrix.mulVec, dotProduct, gramM_apply]
      exact Finset.sum_congr rfl fun q _ => mul_comm _ _
    exact cancel_lemma hΓdet h1
  have hyX : y ∈ orth S (Xplus F) := by
    have hle : Xplus F ≤ LinearMap.ker (S.hT.flip y) := by
      show F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _
      refine sup_le ?_ ?_
      · show Submodule.span E (Set.range F.fl.e) ≤ _
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        show S.hT (F.fl.e i) y = 0
        rw [← frame_cast]; exact hperp _
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        show S.hT F.fl.z y = 0
        rw [← frame_last]; exact hperp _
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker]
    intro x hx
    exact hle hx
  by_cases hyin : y ∈ Xsp F
  · obtain ⟨t, ht⟩ := (Submodule.mem_span_range_iff_exists_fun E).mp (show y ∈ Submodule.span E (Set.range F.fl.e) from hyin)
    have hs := hindep (Sum.elim (Fin.snoc (α := fun _ => E) t 0) (-w)) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_castSucc, Fin.snoc_castSucc, Fin.snoc_last, zero_smul,
        add_zero, frame_cast, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib, ht, hy]
      exact add_neg_cancel _)
    apply hw0
    funext b
    have h1 := congrFun hs (Sum.inr b)
    simpa using h1
  · have hp := hpos y hyX hyin
    have hyy : S.hT y y = star (w (Fin.last r)) * w (Fin.last r) * -(T' : E) := by
      have h1 : ∀ b, S.hT (frame F' b) y = w b * (if b = Fin.last r then -(T' : E) else 0) := by
        intro b
        rw [hy, map_sum]
        simp only [map_smul, smul_eq_mul, gram_self, Matrix.diagonal_apply]
        rw [Finset.sum_eq_single b]
        · simp
        · intro c _ hc; simp [Ne.symm hc]
        · simp
      have e : S.hT (∑ b, w b • frame F' b) y = star w ⬝ᵥ fun p => S.hT (frame F' p) y := hT_comb_left _ _ _
      rw [show S.hT y y = S.hT (∑ b, w b • frame F' b) y by rw [← hy], e]
      simp only [dotProduct, Pi.star_apply, h1]
      rw [Finset.sum_eq_single (Fin.last r)]
      · rw [if_pos rfl]; ring
      · intro c _ hc; simp [hc]
      · simp
    rw [hyy, map_mul, map_mul, hτ, map_neg, map_natCast] at hp
    have h2 : (starRingEnd ℂ (τ (w (Fin.last r))) * τ (w (Fin.last r)) * -(T' : ℂ)).re =
        -(T' : ℝ) * Complex.normSq (τ (w (Fin.last r))) := by
      rw [mul_comm (starRingEnd ℂ _), Complex.mul_conj]
      simp [Complex.ofReal_mul]
      ring
    rw [h2] at hp
    have h3 : 0 ≤ (T' : ℝ) * Complex.normSq (τ (w (Fin.last r))) :=
      mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)
    linarith

end Det

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Use `Fin.lastCases ?_ (fun i => ?_) b` and prove the remaining obligations. Rewrite using `[frame_last]`. Conclude with `hz`. Rewrite using `[frame_cast]`. Establish `hIne : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥`.

Rewrite using `[Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]`. Conclude with `differentIdeal_ne_bot`. Establish `h1mem : (1 : D.host.E) ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)`. Take `⟨k, hk⟩ : ∃ k : ℕ, (D.R.rS : ℤ) - ((i : ℕ) : ℤ) = k` from `⟨D.R.rS - i, by have := i.2; omega⟩`. Rewrite using `[hk, _root_.zpow_neg, _root_.zpow_natCast]`.

Unfold `ddS`. Rewrite using `[← FractionalIdeal.coeIdeal_pow]`. Establish `hne : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ k : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hIne)`. Rewrite using `[FractionalIdeal.mem_inv_iff hne]`. Introduce `y hy`.

Rewrite using `[one_mul]`. Conclude with `FractionalIdeal.coeIdeal_le_one hy`. Establish `h1 : F.fl.e i ∈ XS D F.fl` using `Submodule.subset_span ⟨i, 1, h1mem, (one_smul _ _).symm⟩`. Rewrite `h1` using `[← hX]`. Conclude with `h1.1`.
-/
theorem frame_mem_of_XS (D : D7) (Λ : LatV D) {T : D.host.E} (F : LFlag (hS D) D.R.rS T) (hz : F.fl.z ∈ Λ)
    (hX : XLam Λ F = XS D F.fl) (b : Fin (D.R.rS + 1)) : frame F b ∈ Λ := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · rw [frame_last]; exact hz
  · rw [frame_cast]
    have hIne : (Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ≠ ⊥ := by
      rw [Ne, Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective _ _)]
      exact differentIdeal_ne_bot
    have h1mem : (1 : D.host.E) ∈ (ddS D ^ (-((D.R.rS : ℤ) - ((i : ℕ) : ℤ))) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (D.R.rS : ℤ) - ((i : ℕ) : ℤ) = k := ⟨D.R.rS - i, by have := i.2; omega⟩
      rw [hk, _root_.zpow_neg, _root_.zpow_natCast]
      unfold ddS
      rw [← FractionalIdeal.coeIdeal_pow]
      have hne : (((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F))) ^ k :
          Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
        FractionalIdeal.coeIdeal_ne_zero.mpr (pow_ne_zero _ hIne)
      rw [FractionalIdeal.mem_inv_iff hne]
      intro y hy
      rw [one_mul]
      exact FractionalIdeal.coeIdeal_le_one hy
    have h1 : F.fl.e i ∈ XS D F.fl := Submodule.subset_span ⟨i, 1, h1mem, (one_smul _ _).symm⟩
    rw [← hX] at h1
    exact h1.1

/- English proof (translation)
Introduce `D u u' F0 Λ hSt hBase hR F' hTF`. Take `⟨hcard, hfinE, -, hm, -, hstar, hprod, -, -, -⟩` from `GlobalTheory.real_places_facts D`. Take `⟨hWH, -, hposW, -, -, -, -⟩` from `GlobalTheory.LoopC.Base.main D u u' F0 Λ hSt hBase hR`. Take `⟨-, ⟨-, hunim, hlift, -⟩, hXS⟩` from `hR`. Take `⟨⟨hlift', -, hG⟩, -, hXS'⟩` from `hTF`.

Establish `hF : ∀ b, frame (lf D F0) b ∈ Λ` using `frame_mem_of_XS D Λ (lf D F0) hlift.1 hXS`. Establish `hF' : ∀ b, frame F' b ∈ Λ` using `frame_mem_of_XS D Λ F' hlift'.1 hXS'`. Establish `hf : 0 < D.R.f`. Establish `h1 : 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Use linear arithmetic over natural numbers and integers.

Take `⟨τ0⟩ : Nonempty D.what₂.Tau` from `Fintype.card_pos_iff.mp (by rw [hcard]; exact hf)`. Establish `hm0 : 0 < D.R.m` using `by omega`. Establish `hW1 : Wsp D ⊔ Xsp (lf D F0) = orth (hS D) (Xplus (lf D F0))` using `hWH.1`. Establish `hpos : ∀ x ∈ orth (hS D) (Xplus (lf D F0)), x ∉ Xsp (lf D F0) → 0 < (embS D τ0 ((hS D).hT x x)).re`. Introduce `x hx hxX`.

Rewrite `hx` using `[← hW1]`. Take `⟨w, hw, y, hy, rfl⟩` from `Submodule.mem_sup.mp hx`. Establish `hw2 : w ∈ LinearMap.range (D.sp.iXY 0)` using `hw`. Take `⟨w', rfl⟩` from `LinearMap.mem_range.mp hw2`. Establish `hw'0 : w' ≠ 0`.

Introduce and unpack `rfl`. Apply `hxX` to reduce the goal to its premises. Simplify using `using hy`. Establish `hyO : y ∈ orth (hS D) (Xplus (lf D F0))` using `by rw [← hW1]; exact Submodule.mem_sup_right hy`. Establish `hwO : D.sp.iXY 0 w' ∈ orth (hS D) (Xplus (lf D F0))` using `by rw [← hW1]; exact Submodule.mem_sup_left hw`.

Establish `hyP : y ∈ Xplus (lf D F0)` using `Submodule.mem_sup_left hy`. Simplify using `only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hyO hwO`. Establish `e1 : (hS D).hT y (D.sp.iXY 0 w') = 0` using `hwO y hyP`. Establish `e2 : (hS D).hT (D.sp.iXY 0 w') y = 0` using `by rw [herm', e1, star_zero]`. Establish `e3 : (hS D).hT y y = 0` using `hyO y hyP`.

Establish `e4 : (hS D).hT (D.sp.iXY 0 w') (D.sp.iXY 0 w') = (D.sp.X 0).hT w' w'` using `D.sp.iXY_isom 0 hm0 w' w'`. Simplify using `only [map_add, LinearMap.add_apply]`. Rewrite using `[e1, e2, e3, e4]`. Simplify using `only [map_zero, add_zero]`. Conclude with `hposW (embS D τ0) w' hw'0`.

Establish `hD : Dr1 (lf D F0) F' ≠ 0` using `Dr1_ne_zero (lf D F0) F' (embS D τ0) (hstar τ0) hpos hG`. Establish `hΛint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((hS D).hT y x)` using `fun x hx => (mem_unimod hunim x).1 hx`. Establish `hΓint : AllInt (gramM (lf D F0) F')` using `fun p q => by`. Rewrite using `[gramM_apply]`. Apply the tactic sequence `rcases p with p | p <;> rcases q with q | q <;>`.

Apply the tactic sequence `exact hΛint _ (by first | exact hF q | exact hF' q) _ (by first | exact hF p | exact hF' p)`. Establish `hGint : IsIntegral ℤ (Gval (lf D F0) F')`. Establish `h1 : Gval (lf D F0) F' = (-1) ^ (D.R.rS + 1) * (gramM (lf D F0) F').det`. Rewrite using `[gramM_det, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`. Rewrite using `[h1]`.

Conclude with `(isIntegral_one.neg.pow _).mul hΓint.det`. Establish `hZint : AllInt (ZhatL (lf D F0) F')` using `fun i j => hΓint (Sum.inl i) (Sum.inr j)`. Establish `hDint : IsIntegral ℤ (Dr1 (lf D F0) F')` using `by rw [Dr1_eq]; exact hZint.det`. Take `⟨g, hg⟩ : ∃ g : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E g = Gval (lf D F0) F'` from `⟨⟨_, hGint⟩, rfl⟩`. Take `⟨d, hd⟩ : ∃ d : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E d = Dr1 (lf D F0) F'` from `⟨⟨_, hDint⟩, rfl⟩`.

Establish `hg0 : g ≠ 0` using `by rintro rfl; apply hG; rw [← hg, map_zero]`. Establish `hd0 : d ≠ 0` using `by rintro rfl; apply hD; rw [← hd, map_zero]`. Use `⟨Ideal.span {g ^ 2 * d}, ?_, le_of_eq ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_bot]`. Conclude with `mul_ne_zero (pow_ne_zero _ hg0) hd0`.

Rewrite using `[Ideal.absNorm_span_singleton]`. Establish `h1` using `hprod (algebraMap (𝓞 D.host.E) D.host.E (g ^ 2 * d))`. Rewrite `h1` using `[← Algebra.coe_norm_int]`. Establish `h2 : (((Algebra.norm ℤ (g ^ 2 * d)).natAbs : ℕ) : ℝ) = |(((Algebra.norm ℤ (g ^ 2 * d) : ℤ) : ℚ) : ℝ)|`. Simplify using the standard rewrite rules.

Rewrite using `[h2, ← h1, map_mul, map_pow, hg, hd, ← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, norm_mul, norm_pow]`. Expand and normalize the polynomial expressions, which then agree. Introduce `a ha hEnt`.

Establish `hent : ∀ i j, ∃ m : D.host.E, IsIntegral ℤ m ∧ (a - 1) i j = (Gval (lf D F0) F' * Dr1 (lf D F0) F') * m`. Introduce `i j`. Take `⟨o, ho, hoe⟩` from `hEnt i j`. Take `⟨k, rfl⟩` from `Ideal.mem_span_singleton'.mp ho`. Use `⟨algebraMap (𝓞 D.host.E) D.host.E k * Gval (lf D F0) F', (RingOfIntegers.isIntegral_coe k).mul hGint, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hoe]`. Use `show algebraMap (𝓞 D.host.E) D.host.E (k * (g ^ 2 * d)) = _`. Rewrite using `[map_mul, map_mul, map_pow, hg, hd]`. Expand and normalize the polynomial expressions, which then agree. Use `choose m hm hme using hent`.

Conclude with `main_gen hunim (lf D F0) F' hF hF' hG hD (M := Matrix.of m) ha (fun i j => hm i j) (by ext i j; rw [hme, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul])`.
-/
theorem congruence_mem : ∀ (D : D7) (u u' : D.what₂.Word) (F0 : Fb D u) (Λ : LatV D), Stand D u u' → IsBase D u F0 → IsRowLat D F0 Λ → ∀ F' : FlagU D u', IsTermF D Λ (lf D F0) F' → ∃ I : Ideal (𝓞 D.host.E), I ≠ ⊥ ∧ (Ideal.absNorm I : ℝ) ≤ (∏ τ, ‖embS D τ (Gval (lf D F0) F')‖) ^ 4 * ∏ τ, ‖embS D τ (Dr1 (lf D F0) F')‖ ^ 2 ∧ ∀ a ∈ GlobalTheory.LoopV.stabU (ZhatL (lf D F0) F'), GlobalTheory.LoopV.EntIn I (a - 1) → ∃ n ∈ NLam Λ (lf D F0) ∩ NLam Λ F', ∀ c, n (frame F' c) = ∑ i, a i c • frame F' i := by
  intro D u u' F0 Λ hSt hBase hR F' hTF
  obtain ⟨hcard, hfinE, -, hm, -, hstar, hprod, -, -, -⟩ := GlobalTheory.real_places_facts D
  obtain ⟨hWH, -, hposW, -, -, -, -⟩ := GlobalTheory.LoopC.Base.main D u u' F0 Λ hSt hBase hR
  obtain ⟨-, ⟨-, hunim, hlift, -⟩, hXS⟩ := hR
  obtain ⟨⟨hlift', -, hG⟩, -, hXS'⟩ := hTF
  have hF : ∀ b, frame (lf D F0) b ∈ Λ := frame_mem_of_XS D Λ (lf D F0) hlift.1 hXS
  have hF' : ∀ b, frame F' b ∈ Λ := frame_mem_of_XS D Λ F' hlift'.1 hXS'
  have hf : 0 < D.R.f := by
    have h1 : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    omega
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := Fintype.card_pos_iff.mp (by rw [hcard]; exact hf)
  have hm0 : 0 < D.R.m := by omega
  have hW1 : Wsp D ⊔ Xsp (lf D F0) = orth (hS D) (Xplus (lf D F0)) := hWH.1
  have hpos : ∀ x ∈ orth (hS D) (Xplus (lf D F0)), x ∉ Xsp (lf D F0) →
      0 < (embS D τ0 ((hS D).hT x x)).re := by
    intro x hx hxX
    rw [← hW1] at hx
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    have hw2 : w ∈ LinearMap.range (D.sp.iXY 0) := hw
    obtain ⟨w', rfl⟩ := LinearMap.mem_range.mp hw2
    have hw'0 : w' ≠ 0 := by
      rintro rfl
      apply hxX
      simpa using hy
    have hyO : y ∈ orth (hS D) (Xplus (lf D F0)) := by rw [← hW1]; exact Submodule.mem_sup_right hy
    have hwO : D.sp.iXY 0 w' ∈ orth (hS D) (Xplus (lf D F0)) := by rw [← hW1]; exact Submodule.mem_sup_left hw
    have hyP : y ∈ Xplus (lf D F0) := Submodule.mem_sup_left hy
    simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hyO hwO
    have e1 : (hS D).hT y (D.sp.iXY 0 w') = 0 := hwO y hyP
    have e2 : (hS D).hT (D.sp.iXY 0 w') y = 0 := by rw [herm', e1, star_zero]
    have e3 : (hS D).hT y y = 0 := hyO y hyP
    have e4 : (hS D).hT (D.sp.iXY 0 w') (D.sp.iXY 0 w') = (D.sp.X 0).hT w' w' := D.sp.iXY_isom 0 hm0 w' w'
    simp only [map_add, LinearMap.add_apply]
    rw [e1, e2, e3, e4]
    simp only [map_zero, add_zero]
    exact hposW (embS D τ0) w' hw'0
  have hD : Dr1 (lf D F0) F' ≠ 0 := Dr1_ne_zero (lf D F0) F' (embS D τ0) (hstar τ0) hpos hG
  have hΛint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((hS D).hT y x) := fun x hx => (mem_unimod hunim x).1 hx
  have hΓint : AllInt (gramM (lf D F0) F') := fun p q => by
    rw [gramM_apply]
    rcases p with p | p <;> rcases q with q | q <;>
      exact hΛint _ (by first | exact hF q | exact hF' q) _ (by first | exact hF p | exact hF' p)
  have hGint : IsIntegral ℤ (Gval (lf D F0) F') := by
    have h1 : Gval (lf D F0) F' = (-1) ^ (D.R.rS + 1) * (gramM (lf D F0) F').det := by
      rw [gramM_det, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]
    rw [h1]
    exact (isIntegral_one.neg.pow _).mul hΓint.det
  have hZint : AllInt (ZhatL (lf D F0) F') := fun i j => hΓint (Sum.inl i) (Sum.inr j)
  have hDint : IsIntegral ℤ (Dr1 (lf D F0) F') := by rw [Dr1_eq]; exact hZint.det
  obtain ⟨g, hg⟩ : ∃ g : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E g = Gval (lf D F0) F' := ⟨⟨_, hGint⟩, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E d = Dr1 (lf D F0) F' := ⟨⟨_, hDint⟩, rfl⟩
  have hg0 : g ≠ 0 := by rintro rfl; apply hG; rw [← hg, map_zero]
  have hd0 : d ≠ 0 := by rintro rfl; apply hD; rw [← hd, map_zero]
  refine ⟨Ideal.span {g ^ 2 * d}, ?_, le_of_eq ?_, ?_⟩
  · rw [Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero (pow_ne_zero _ hg0) hd0
  · rw [Ideal.absNorm_span_singleton]
    have h1 := hprod (algebraMap (𝓞 D.host.E) D.host.E (g ^ 2 * d))
    rw [← Algebra.coe_norm_int] at h1
    have h2 : (((Algebra.norm ℤ (g ^ 2 * d)).natAbs : ℕ) : ℝ) = |(((Algebra.norm ℤ (g ^ 2 * d) : ℤ) : ℚ) : ℝ)| := by
      simp
    rw [h2, ← h1, map_mul, map_pow, hg, hd, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_mul, map_pow, norm_mul, norm_pow]
    ring
  · intro a ha hEnt
    have hent : ∀ i j, ∃ m : D.host.E, IsIntegral ℤ m ∧
        (a - 1) i j = (Gval (lf D F0) F' * Dr1 (lf D F0) F') * m := by
      intro i j
      obtain ⟨o, ho, hoe⟩ := hEnt i j
      obtain ⟨k, rfl⟩ := Ideal.mem_span_singleton'.mp ho
      refine ⟨algebraMap (𝓞 D.host.E) D.host.E k * Gval (lf D F0) F', (RingOfIntegers.isIntegral_coe k).mul hGint, ?_⟩
      rw [← hoe]
      show algebraMap (𝓞 D.host.E) D.host.E (k * (g ^ 2 * d)) = _
      rw [map_mul, map_mul, map_pow, hg, hd]
      ring
    choose m hm hme using hent
    exact main_gen hunim (lf D F0) F' hF hF' hG hD (M := Matrix.of m) ha (fun i j => hm i j)
      (by ext i j; rw [hme, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul])

end GlobalTheory.LoopV.Cong
