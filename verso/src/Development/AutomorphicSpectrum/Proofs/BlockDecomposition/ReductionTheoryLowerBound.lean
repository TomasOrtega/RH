import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicTensorRationalApproximationStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactHeightLowerBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicBoxCompactStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactAdelicNormBoundedStatement

set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open PositivityTheory.ThKEst (rId)
open PositivityTheory.ThKEst.Sieg (rId_add rId_zero' rId_snd rId_inf)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ}

/- English proof (translation)
The claim follows from `funext fun i => map_sub (inclR (F := F) (AF F)) _ _`.
-/
theorem ratV_sub (u v : Fin n → E) : ratV F (u - v) = ratV F u - ratV F v :=
  funext fun i => map_sub (inclR (F := F) (AF F)) _ _

/- English proof (translation)
The claim follows from `funext fun i => map_mul (inclR (F := F) (AF F)) _ _`.
-/
theorem ratV_smul (c : E) (v : Fin n → E) : ratV F (c • v) = inclR (F := F) (AF F) c • ratV F v :=
  funext fun i => map_mul (inclR (F := F) (AF F)) _ _

/- English proof (translation)
Use function extensionality and compare the values at `k`. Establish `e` using `congrFun (congrFun hB k) j`. Simplify using `only [Matrix.mul_apply] at e`. Simplify using `only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `Eq.trans e (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations.

Conclude with `mul_comm _ _`.
-/
theorem mulVec_col {m : ℕ} {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {X : Matrix (Fin n) (Fin m) E}
    {B : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)} (hB : M * adMat F X = adMat F X * B) (j : Fin m) :
    M *ᵥ ratV F (Xᵀ j) = ∑ i, B i j • ratV F (Xᵀ i) := by
  funext k
  have e := congrFun (congrFun hB k) j
  simp only [Matrix.mul_apply] at e
  simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Eq.trans e (Finset.sum_congr rfl fun i _ => ?_)
  exact mul_comm _ _

/- English proof (translation)
Establish `hm : ∀ w : InfinitePlace F, w.mult = 1` using `fun w => by`. Rewrite using `[InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]`. Establish `hw : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ = Real.exp c` using `fun w => norm_evInf_rId w c`. Establish `hv : ∀ v, GroundTheory.Automorphic.Reduction.finComp v (rId F c • y) = GroundTheory.Automorphic.Reduction.finComp v y` using `fun v => by`. Rewrite using `[GroundTheory.Automorphic.Reduction.finComp_smul, rId_snd]`.

Conclude with `one_smul _ _`. Simplify using `only [GroundTheory.Automorphic.Reduction.adelicNorm, GroundTheory.Automorphic.Reduction.infComp_smul, GroundTheory.Automorphic.Reduction.euclidNorm_smul, hw, hm, pow_one, hv]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul, mul_assoc]`.
-/
theorem adelicNorm_rId [IsTotallyReal F] {N : ℕ} (c : ℝ) (y : Fin N → AF F) :
    GroundTheory.Automorphic.Reduction.adelicNorm (rId F c • y) =
      Real.exp (Module.finrank ℚ F * c) * GroundTheory.Automorphic.Reduction.adelicNorm y := by
  have hm : ∀ w : InfinitePlace F, w.mult = 1 := fun w => by
    rw [InfinitePlace.mult, if_pos (IsTotallyReal.isReal w)]
  have hw : ∀ w : InfinitePlace F, ‖(rId F c).1 w‖ = Real.exp c := fun w => norm_evInf_rId w c
  have hv : ∀ v, GroundTheory.Automorphic.Reduction.finComp v (rId F c • y) = GroundTheory.Automorphic.Reduction.finComp v y := fun v => by
    rw [GroundTheory.Automorphic.Reduction.finComp_smul, rId_snd]
    exact one_smul _ _
  simp only [GroundTheory.Automorphic.Reduction.adelicNorm, GroundTheory.Automorphic.Reduction.infComp_smul,
    GroundTheory.Automorphic.Reduction.euclidNorm_smul, hw, hm, pow_one, hv]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, card_infinitePlace, ← Real.exp_nat_mul, mul_assoc]

/- English proof (translation)
Unfold `hv`. Rewrite using `[← adelicNorm_rId]`. Use `congr 1`. Use function extensionality and compare the values at `p`. Simplify using `only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul, Finsupp.smul_apply]`.
-/
theorem hv_rId [IsTotallyReal F] (c : ℝ) (ξ : Fin n → AF F ⊗[F] E) :
    hv (algebraMap (AF F) (AF F ⊗[F] E) (rId F c) • ξ) = Real.exp (Module.finrank ℚ F * c) * hv ξ := by
  unfold hv
  rw [← adelicNorm_rId]
  congr 1
  funext p
  simp only [Pi.smul_apply, smul_eq_mul, ← Algebra.smul_def, map_smul, Finsupp.smul_apply]

/- English proof (translation)
Rewrite using `[map_mul, Units.val_mul]`.
-/
theorem matHom_mul_val (g h : GAd σ J) :
    (matHom _ σ J (g * h)).1 = (matHom _ σ J g).1 * (matHom _ σ J h).1 := by
  rw [map_mul, Units.val_mul]

variable {X Y : Matrix (Fin n) (Fin (r + 1)) E} {a : (Fin (r + 1) → ℝ) → GAd σ J}

/- English proof (translation)
Rewrite using `[mulVec_col (ha.onX t) i, Finset.sum_eq_single i]`. Rewrite using `[Matrix.diagonal_apply_eq]`. Introduce `k _ hk`. Rewrite using `[Matrix.diagonal_apply_ne _ hk, zero_smul]`. Introduce `hi`.

Conclude with `absurd (Finset.mem_univ i) hi`.
-/
theorem torus_col (ha : IsTorus σ J X Y a) (t : Fin (r + 1) → ℝ) (i : Fin (r + 1)) :
    (matHom _ σ J (a t)).1 *ᵥ ratV F (Xᵀ i) = algebraMap (AF F) (AF F ⊗[F] E) (rId F (t i)) • ratV F (Xᵀ i) := by
  rw [mulVec_col (ha.onX t) i, Finset.sum_eq_single i]
  · rw [Matrix.diagonal_apply_eq]
  · intro k _ hk
    rw [Matrix.diagonal_apply_ne _ hk, zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/- English proof (translation)
Establish `h0 : a 0 = 1`. Establish `e` using `ha.add 0 0`. Rewrite `e` using `[add_zero]`. Conclude with `mul_left_cancel (e.symm.trans (mul_one _).symm)`. Conclude with `inv_eq_of_mul_eq_one_right (by rw [← ha.add, add_neg_cancel, h0])`.
-/
theorem torus_inv (ha : IsTorus σ J X Y a) (s : Fin (r + 1) → ℝ) : (a s)⁻¹ = a (-s) := by
  have h0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  exact inv_eq_of_mul_eq_one_right (by rw [← ha.add, add_neg_cancel, h0])

/- English proof (translation)
Rewrite using `[mulVec_col e 0, Finset.sum_eq_single 0]`. Introduce `k _ hk`. Rewrite using `[hB (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk), zero_smul]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ 0) hi`.
-/
theorem par_col_zero {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) :
    M *ᵥ ratV F (Xᵀ 0) = B 0 0 • ratV F (Xᵀ 0) := by
  rw [mulVec_col e 0, Finset.sum_eq_single 0]
  · intro k _ hk
    rw [hB (show id (0 : Fin (r + 1)) < id k from Fin.pos_of_ne_zero hk), zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ 0) hi

/- English proof (translation)
Establish `hj0 : (0 : Fin (r + 1)) ≠ j` using `fun h => by rw [← h] at hj; simp at hj`. Rewrite using `[mulVec_col e j, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (r + 1))), Finset.sum_eq_single_of_mem j (Finset.mem_erase.2 ⟨hj0.symm, Finset.mem_univ _⟩)]`. Introduce `k hk hkj`. Establish `hk0 : k ≠ 0` using `(Finset.mem_erase.1 hk).1`. Establish `: j < k`.

Establish `h1 : k.val ≠ 0` using `fun h => hk0 (Fin.ext h)`. Establish `h2 : k.val ≠ 1` using `fun h => hkj (Fin.ext (h.trans hj.symm))`. Conclude with `Fin.lt_def.2 (by omega)`. Rewrite using `[hB (show id j < id k from this), zero_smul]`.
-/
theorem par_col_one {M : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)} {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)}
    (hB : B.BlockTriangular id) (e : M * adMat F X = adMat F X * B) {j : Fin (r + 1)} (hj : j.val = 1) :
    M *ᵥ ratV F (Xᵀ j) = B 0 j • ratV F (Xᵀ 0) + B j j • ratV F (Xᵀ j) := by
  have hj0 : (0 : Fin (r + 1)) ≠ j := fun h => by rw [← h] at hj; simp at hj
  rw [mulVec_col e j, ← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : Fin (r + 1))),
    Finset.sum_eq_single_of_mem j (Finset.mem_erase.2 ⟨hj0.symm, Finset.mem_univ _⟩)]
  intro k hk hkj
  have hk0 : k ≠ 0 := (Finset.mem_erase.1 hk).1
  have : j < k := by
    have h1 : k.val ≠ 0 := fun h => hk0 (Fin.ext h)
    have h2 : k.val ≠ 1 := fun h => hkj (Fin.ext (h.trans hj.symm))
    exact Fin.lt_def.2 (by omega)
  rw [hB (show id j < id k from this), zero_smul]

/- English proof (translation)
Take `⟨B, hB, eB⟩` from `hω`. Establish `h1` using `par_col_zero hB eB`. Establish `h2` using `torus_col ha (-s) 0`. Establish `e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹`. Rewrite using `[← torus_inv ha]`.

Use `group`. Establish `e2 : (ω * κ)⁻¹ = κ⁻¹ * ω⁻¹` using `by group`. Unfold `hgt`. Rewrite using `[← hv_rId, e1, e2, matHom_mul_val, matHom_mul_val, matHom_mul_val, ratV_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, h2, Matrix.mulVec_smul, Matrix.mulVec_smul, Ma …`. Simplify using `only [Pi.neg_apply]`.

Simplify using `only [smul_smul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hgt_line [IsTotallyReal F] (ha : IsTorus σ J X Y a) {ω : GAd σ J} (hω : ω⁻¹ ∈ minPar σ J X)
    (s : Fin (r + 1) → ℝ) (κ : GAd σ J) (e : E) :
    hgt σ J (ω * a s * κ) (e • Xᵀ 0) =
      Real.exp (Module.finrank ℚ F * (-s 0)) * hgt σ J (ω * κ) (e • Xᵀ 0) := by
  obtain ⟨B, hB, eB⟩ := hω
  have h1 := par_col_zero hB eB
  have h2 := torus_col ha (-s) 0
  have e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹ := by
    rw [← torus_inv ha]; group
  have e2 : (ω * κ)⁻¹ = κ⁻¹ * ω⁻¹ := by group
  unfold hgt
  rw [← hv_rId, e1, e2, matHom_mul_val, matHom_mul_val, matHom_mul_val, ratV_smul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, h2, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Pi.neg_apply]
  simp only [smul_smul]
  congr 1
  ring

/- English proof (translation)
Establish `h1` using `par_col_zero hB eB`. Establish `h2` using `par_col_one hB eB hj`. Establish `h3` using `torus_col ha (-s) 0`. Establish `h4` using `torus_col ha (-s) j`. Establish `e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹`.

Rewrite using `[← torus_inv ha]`. Use `group`. Establish `hq : inclR (F` using `F) (AF F) (q : E) = (q : AF F ⊗[F] E) := map_natCast _ q`. Establish `hR : ∀ x y : ℝ, algebraMap (AF F) (AF F ⊗[F] E) (rId F (x + y)) = algebraMap (AF F) (AF F ⊗[F] E) (rId F x) * algebraMap (AF F) (AF F ⊗[F] E) (rId F y)` using `fun x y => by`. Rewrite using `[rId_add, map_mul]`.

Establish `r0 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) = algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0 - t))`. Rewrite using `[← hR]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `r1 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j)) = algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j - t))`.

Rewrite using `[← hR]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Establish `s1 : (matHom _ σ J ω⁻¹).1 *ᵥ ratV F ((q : E) • Xᵀ j - c • Xᵀ 0) = (B 0 0 * ((q : AF F ⊗[F] E) * b - inclR (F` using `F) (AF F) c)) • ratV F (Xᵀ 0) + ((q : AF F ⊗[F] E) * B j j) • ratV F (Xᵀ j) := by`. Rewrite using `[ratV_sub, ratV_smul, ratV_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, hq, ← hb]`.

Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Unfold `hgt`. Rewrite using `[← hv_rId, e1, matHom_mul_val, matHom_mul_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h3, h4, ← Matrix.mulVec_smul]`.

Use `congr 2`. Simplify using `only [Pi.neg_apply, r0, r1, map_mul, map_natCast]`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hgt_pair [IsTotallyReal F] (ha : IsTorus σ J X Y a) {ω : GAd σ J}
    {B : Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E)} (hB : B.BlockTriangular id)
    (eB : (matHom _ σ J ω⁻¹).1 * adMat F X = adMat F X * B) (s : Fin (r + 1) → ℝ) (κ : GAd σ J)
    {j : Fin (r + 1)} (hj : j.val = 1) (q : ℕ) (c : E) {b : AF F ⊗[F] E} (hb : B 0 0 * b = B 0 j) (t : ℝ) :
    hgt σ J (ω * a s * κ) ((q : E) • Xᵀ j - c • Xᵀ 0) =
      Real.exp (Module.finrank ℚ F * t) * hv ((matHom _ σ J κ⁻¹).1 *ᵥ
        ((B 0 0 * (algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0 - t)) *
            ((q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c))) • ratV F (Xᵀ 0) +
          (B j j * algebraMap (AF F) (AF F ⊗[F] E) ((q : AF F) * rId F (-s j - t))) • ratV F (Xᵀ j))) := by
  have h1 := par_col_zero hB eB
  have h2 := par_col_one hB eB hj
  have h3 := torus_col ha (-s) 0
  have h4 := torus_col ha (-s) j
  have e1 : (ω * a s * κ)⁻¹ = κ⁻¹ * a (-s) * ω⁻¹ := by
    rw [← torus_inv ha]; group
  have hq : inclR (F := F) (AF F) (q : E) = (q : AF F ⊗[F] E) := map_natCast _ q
  have hR : ∀ x y : ℝ, algebraMap (AF F) (AF F ⊗[F] E) (rId F (x + y)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F x) * algebraMap (AF F) (AF F ⊗[F] E) (rId F y) := fun x y => by
    rw [rId_add, map_mul]
  have r0 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s 0 - t)) := by
    rw [← hR]; congr 2; ring
  have r1 : algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j)) =
      algebraMap (AF F) (AF F ⊗[F] E) (rId F t) * algebraMap (AF F) (AF F ⊗[F] E) (rId F (-s j - t)) := by
    rw [← hR]; congr 2; ring
  have s1 : (matHom _ σ J ω⁻¹).1 *ᵥ ratV F ((q : E) • Xᵀ j - c • Xᵀ 0) =
      (B 0 0 * ((q : AF F ⊗[F] E) * b - inclR (F := F) (AF F) c)) • ratV F (Xᵀ 0) +
        ((q : AF F ⊗[F] E) * B j j) • ratV F (Xᵀ j) := by
    rw [ratV_sub, ratV_smul, ratV_smul, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2, hq, ← hb]
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  unfold hgt
  rw [← hv_rId, e1, matHom_mul_val, matHom_mul_val, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, s1, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, h3, h4, ← Matrix.mulVec_smul]
  congr 2
  simp only [Pi.neg_apply, r0, r1, map_mul, map_natCast]
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (rId F c * y).1 w = (rId F c).1 w * y.1 w` using `rfl`. Rewrite using `[e, norm_mul, show ‖(rId F c).1 w‖ = Real.exp c from norm_evInf_rId w c]`. Conclude with `(mul_le_mul_of_nonneg_left (hy.1 w) (Real.exp_pos c).le).trans h`. Establish `e : (rId F c * y).2 = y.2`.

Rewrite using `[show (rId F c * y).2 = (rId F c).2 * y.2 from rfl, rId_snd, one_mul]`. Rewrite using `[e]`. Conclude with `hy.2`.
-/
theorem rId_mul_mem_boxF [IsTotallyReal F] {c ε ρ : ℝ} (h : Real.exp c * ε ≤ ρ) {y : AF F} (hy : y ∈ boxF F ε) :
    rId F c * y ∈ boxF F ρ := by
  refine ⟨fun w => ?_, ?_⟩
  · have e : (rId F c * y).1 w = (rId F c).1 w * y.1 w := rfl
    rw [e, norm_mul, show ‖(rId F c).1 w‖ = Real.exp c from norm_evInf_rId w c]
    exact (mul_le_mul_of_nonneg_left (hy.1 w) (Real.exp_pos c).le).trans h
  · have e : (rId F c * y).2 = y.2 := by
      rw [show (rId F c * y).2 = (rId F c).2 * y.2 from rfl, rId_snd, one_mul]
    rw [e]
    exact hy.2

/- English proof (translation)
Introduce `k` and use `by rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul] exact rId_mul_mem_boxF h (hy k)`.
-/
theorem rId_mul_mem_boxE [IsTotallyReal F] {c ε ρ : ℝ} (h : Real.exp c * ε ≤ ρ) {y : AF F ⊗[F] E} (hy : y ∈ boxE F E ε) :
    algebraMap (AF F) (AF F ⊗[F] E) (rId F c) * y ∈ boxE F E ρ := fun k => by
  rw [← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact rId_mul_mem_boxF h (hy k)

/- English proof (translation)
Use `⟨fun w => ?_, ?_⟩` and prove the remaining obligations. Establish `e : (q : AF F).1 w = (q : w.Completion)` using `rfl`. Rewrite using `[e, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast]`. Simplify using the standard rewrite rules. Conclude with `natCast_mem _ q`.
-/
theorem natCast_mem_boxF (q : ℕ) : (q : AF F) ∈ boxF F q := by
  refine ⟨fun w => ?_, ?_⟩
  · have e : (q : AF F).1 w = (q : w.Completion) := rfl
    rw [e, ← (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _), map_natCast]
    simp
  · exact natCast_mem _ q

/- English proof (translation)
Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Use `continuous_pi fun p => ?_` and prove the remaining obligations. Conclude with `(IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).coord _)).comp (continuous_apply _)`.
-/
theorem continuous_coordVec : Continuous fun ξ : Fin n → AF F ⊗[F] E =>
    (fun p : Fin (Fintype.card (Fin n × Fin (Module.finrank F E))) =>
      (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr
        (ξ ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
        ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  refine continuous_pi fun p => ?_
  exact (IsModuleTopology.continuous_of_linearMap
    ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).coord _)).comp (continuous_apply _)

/- English proof (translation)
Use `GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)` as an intermediate fact. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Take `⟨hbF, hbE⟩` from `GlobalTheory.T.adelic_box_compact F E`. Establish `hcA : Continuous (algebraMap (AF F) (AF F ⊗[F] E))` using `IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))`. Set `Φ : GAd σ J × (AF F ⊗[F] E) × (AF F ⊗[F] E) × (AF F ⊗[F] E) × AF F → Fin n → AF F ⊗[F] E` to `fun t => (matHom _ σ J t.1⁻¹).1 *ᵥ ((t.2.1 * t.2.2.2.1) • ratV F x₁ + (t.2.2.1 * algebraMap (AF F) (AF F ⊗[F] E) t.2.2.2.2) • ratV F x₂)`.

Establish `hΦ : Continuous Φ`. Use `((continuous_matHom_val (σ := σ) (J := J)).comp (continuous_inv.comp continuous_fst)).matrix_mulVec ?_` and prove the remaining obligations. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `fun_prop`.

Establish `hK` using `(hC.prod (hA₁.prod (hA₂.prod (hbE.prod hbF)))).image (continuous_coordVec.comp hΦ)`. Take `⟨P, hP, hle⟩` from `GlobalTheory.T.compact_adelic_norm_bounded F _ _ hK`. Conclude with `⟨P, hP, fun κ hκ α₁ h₁ α₂ h₂ ζ hζ z hz => hle _ ⟨(κ, α₁, α₂, ζ, z), ⟨hκ, h₁, h₂, hζ, hz⟩, rfl⟩⟩`.
-/
theorem upper_bound (h : IsCMExt F E σ) (x₁ x₂ : Fin n → E) {A₁ A₂ : Set (AF F ⊗[F] E)} (hA₁ : IsCompact A₁)
    (hA₂ : IsCompact A₂) {C : Set (GAd σ J)} (hC : IsCompact C) :
    ∃ P : ℝ, 0 < P ∧ ∀ κ ∈ C, ∀ α₁ ∈ A₁, ∀ α₂ ∈ A₂, ∀ ζ ∈ boxE F E 1, ∀ z ∈ boxF F 1,
      hv ((matHom _ σ J κ⁻¹).1 *ᵥ ((α₁ * ζ) • ratV F x₁ + (α₂ * algebraMap (AF F) (AF F ⊗[F] E) z) • ratV F x₂)) ≤ P := by
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨hbF, hbE⟩ := GlobalTheory.T.adelic_box_compact F E
  have hcA : Continuous (algebraMap (AF F) (AF F ⊗[F] E)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap (AF F) (AF F ⊗[F] E))
  let Φ : GAd σ J × (AF F ⊗[F] E) × (AF F ⊗[F] E) × (AF F ⊗[F] E) × AF F → Fin n → AF F ⊗[F] E := fun t =>
    (matHom _ σ J t.1⁻¹).1 *ᵥ ((t.2.1 * t.2.2.2.1) • ratV F x₁ + (t.2.2.1 * algebraMap (AF F) (AF F ⊗[F] E) t.2.2.2.2) • ratV F x₂)
  have hΦ : Continuous Φ := by
    refine ((continuous_matHom_val (σ := σ) (J := J)).comp (continuous_inv.comp continuous_fst)).matrix_mulVec ?_
    refine continuous_pi fun i => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hK := (hC.prod (hA₁.prod (hA₂.prod (hbE.prod hbF)))).image (continuous_coordVec.comp hΦ)
  obtain ⟨P, hP, hle⟩ := GlobalTheory.T.compact_adelic_norm_bounded F _ _ hK
  exact ⟨P, hP, fun κ hκ α₁ h₁ α₂ h₂ ζ hζ z hz =>
    hle _ ⟨(κ, α₁, α₂, ζ, z), ⟨hκ, h₁, h₂, hζ, hz⟩, rfl⟩⟩

open scoped Pointwise in
/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩ1 hC`. Use `haveI := h.1`. Distinguish the cases in `hr : ∃ j : Fin (r + 1), j.val = 1`. Use `swap`. Conclude with `⟨1, one_pos, fun ω _ s κ _ e _ _ j hj => absurd ⟨j, hj⟩ hr⟩`.

Take `⟨j, hj⟩` from `hr`. Establish `hF` using `pfrA h hJ hW`. Use `GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)` as an intermediate fact. Establish `hBc : Continuous fun p : GAd σ J => Bm σ J X Y p⁻¹` using `continuous_Bm.comp continuous_inv`. Establish `hA₁ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ 0 0) '' Ω)` using `hΩ.image (hBc.matrix_elem 0 0)`.

Establish `hA₂ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ j j) '' Ω)` using `hΩ.image (hBc.matrix_elem j j)`. Take `⟨P, hP, hlow⟩` from `GlobalTheory.T.compact_height_lower_bound F E σ h n J (Ω * C) (hΩ.mul hC)`. Take `⟨P₄, hP₄, hup⟩` from `upper_bound h (Xᵀ 0) (Xᵀ j) hA₁ hA₂ hC`. Take `⟨K, hKdef⟩ : ∃ K, K = 2 * P * P₄` from `⟨_, rfl⟩`. Establish `hK : 0 < K` using `by rw [hKdef]; positivity`.

Take `⟨ε, hεdef⟩ : ∃ ε, ε = 1 / (K + 1)` from `⟨_, rfl⟩`. Establish `hε : 0 < ε` using `by rw [hεdef]; positivity`. Establish `hε1 : ε ≤ 1`. Rewrite using `[hεdef, div_le_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨d, hd⟩ : ∃ d, d = Module.finrank ℚ F` from `⟨_, rfl⟩`. Establish `hd0 : d ≠ 0` using `by rw [hd]; exact Module.finrank_pos.ne'`. Establish `hKε : K * ε ^ d < 1`. Establish `h1 : ε ^ d ≤ ε` using `pow_le_of_le_one hε.le hε1 hd0`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨N, hN1, hN⟩` from `GlobalTheory.T.adelic_tensor_rational_approximation F E ε hε`. Establish `hN0 : (0 : ℝ) < N` using `by exact_mod_cast hN1`. Use `⟨(K + 1) * N, by positivity, ?_⟩` and prove the remaining obligations. Introduce `ω hω s κ hκ e he hNM j' hj'`. Rewrite using `[show j' = j from Fin.ext (hj'.trans hj.symm)]`.

Establish `m1 : ω ∈ minPar σ J X` using `minParOne_subset (hΩ1 hω)`. Establish `m2 : ω⁻¹ ∈ minPar σ J X` using `inv_mem_minPar h hJ hW m1`. Take `⟨hBt, eB⟩` from `(mem_minPar_iff hF).1 m2`. Take `⟨hBt', -⟩` from `(mem_minPar_iff hF).1 m1`. Establish `hu1 : Bm σ J X Y ω⁻¹ 0 0 * Bm σ J X Y ω 0 0 = 1`.

Rewrite using `[← diag_mul_bt hBt hBt', ← Bm_mul hF m2 m1, inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]`. Establish `hb : Bm σ J X Y ω⁻¹ 0 0 * (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0) = Bm σ J X Y ω⁻¹ 0 j`. Rewrite using `[mul_left_comm, hu1, mul_one]`. Take `⟨q, hq1, hqN, c, hc⟩` from `hN (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0)`. Establish `hq0 : (q : E) ≠ 0` using `by exact_mod_cast (by omega : q ≠ 0)`.

Establish `hj0 : j ≠ 0` using `fun e0 => by rw [e0] at hj; simp at hj`. Establish `hyx : cT (σ : E →+* E) Y * J * X = 1` using `PFr.yx (s := (σ : E →+* E)) (Jm := J) (Xm := X) (Ym := Y) ⟨fun x => sigma_sigma h x, Matrix.ext fun i k => hJ.1 i k, hW.xx, hW.yy, hW.xy⟩`. Establish `hcol : ∀ i k, ((cT (σ : E →+* E) Y * J) *ᵥ Xᵀ i) k = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) k i` using `fun i k => by`. Rewrite using `[← hyx]`. Both sides reduce to the same expression.

Establish `hu0 : (q : E) • Xᵀ j - c • Xᵀ 0 ≠ 0` using `fun h0 => by`. Establish `e1` using `congrFun (congrArg (fun v => (cT (σ : E →+* E) Y * J) *ᵥ v) h0) j`. Simplify using `only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero, Pi.sub_apply, Pi.smul_apply, hcol, smul_eq_mul, Matrix.one_apply_eq, Matrix.one_apply_ne hj0, mul_one, mul_zero, sub_zero, Pi.zero_apply] at e1`. Conclude with `hq0 e1`. Set `Bf` to `toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J`.

Establish `hBf : ∀ u v, Bf u v = ∑ i, ∑ j, σ (u i) * J i j * v j` using `fun u v => by`. Simplify using `only [Bf, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`. Establish `hg : ∀ i k, Bf (Xᵀ i) (Xᵀ k) = 0` using `fun i k => by`. Establish `e1` using `gram_apply (σ := σ) (J := J) X X i k`.

Rewrite `e1` using `[hW.xx]`. Conclude with `e1.symm`. Establish `hiso : hE σ J ((q : E) • Xᵀ j - c • Xᵀ 0) ((q : E) • Xᵀ j - c • Xᵀ 0) = 0`. Use `(hBf _ _).symm.trans ?_` and prove the remaining obligations. Simplify using `only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, hg, smul_zero, mul_zero, sub_zero]`.

Establish `hNM'` using `hNM.2.2 _ hu0 hiso`. Take `⟨A, hAdef⟩ : ∃ A, A = Real.exp (-s 0)` from `⟨_, rfl⟩`. Take `⟨D, hDdef⟩ : ∃ D, D = Real.exp (-s j)` from `⟨_, rfl⟩`. Establish `hA : 0 < A` using `hAdef ▸ Real.exp_pos _`. Establish `hD : 0 < D` using `hDdef ▸ Real.exp_pos _`.

Take `⟨T, hTdef⟩ : ∃ T, T = max (ε * A) (N * D)` from `⟨_, rfl⟩`. Establish `hT1 : ε * A ≤ T` using `hTdef ▸ le_max_left _ _`. Establish `hT2 : N * D ≤ T` using `hTdef ▸ le_max_right _ _`. Establish `hT : 0 < T` using `lt_of_lt_of_le (by positivity) hT1`. Establish `hexp : ∀ x : ℝ, Real.exp (x - Real.log T) = Real.exp x / T` using `fun x => by`.

Rewrite using `[Real.exp_sub, Real.exp_log hT]`. Establish `hζ` using `rId_mul_mem_boxE (c := -s 0 - Real.log T) (ρ := 1) (by`. Rewrite using `[hexp, ← hAdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]`. Conclude with `hT1) hc`. Establish `hz : (q : AF F) * rId F (-s j - Real.log T) ∈ boxF F 1`.

Rewrite using `[mul_comm]`. Use `rId_mul_mem_boxF ?_ (natCast_mem_boxF q)` and prove the remaining obligations. Rewrite using `[hexp, ← hDdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]`. Conclude with `(mul_le_mul_of_nonneg_right (by exact_mod_cast hqN) hD.le).trans hT2`. Establish `hup'` using `hup κ hκ _ ⟨ω, hω, rfl⟩ _ ⟨ω, hω, rfl⟩ _ hζ _ hz`.

Establish `e1` using `hgt_pair ha hBt eB s κ hj q c hb (Real.log T)`. Establish `e2` using `hgt_line ha m2 s κ e`. Establish `hl` using `hlow (ω * κ) (Set.mul_mem_mul hω hκ) (e • Xᵀ 0) hNM.1`. Rewrite `e1`, `e2` using `[← hd]`. Establish `eT : Real.exp (d * Real.log T) = T ^ d` using `by rw [Real.exp_nat_mul, Real.exp_log hT]`.

Establish `eA : Real.exp (d * (-s 0)) = A ^ d` using `by rw [Real.exp_nat_mul, hAdef]`. Rewrite `e1` using `[eT]`. Rewrite `e2` using `[eA]`. Establish `hmain : A ^ d ≤ K * T ^ d`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[e1]`. Conclude with `mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup' (by positivity)) (by norm_num)) hP.le`. Use `_ = K * T ^ d := by rw [hKdef]; ring`. Break down `le_total (N * D) (ε * A) with hc1 | hc1` into its components or cases. It suffices to derive a contradiction.

Establish `eT' : T = ε * A` using `by rw [hTdef, max_eq_left hc1]`. Rewrite `hmain` using `[eT', mul_pow]`. Establish `hAd : 0 < A ^ d` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `eT' : T = N * D` using `by rw [hTdef, max_eq_right hc1]`.

Establish `h3 : A ≤ (K + 1) * N * D`. Establish `h4 : K ≤ (K + 1) ^ d`. Establish `: K + 1 ≤ (K + 1) ^ d` using `le_self_pow₀ (by linarith) hd0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : A ^ d ≤ ((K + 1) * N * D) ^ d`.

Rewrite `hmain` using `[eT']`. Rewrite using `[mul_assoc, mul_pow]`. Conclude with `hmain.trans (mul_le_mul_of_nonneg_right h4 (by positivity))`. Conclude with `(pow_le_pow_iff_left₀ hA.le (by positivity) hd0).1 h5`. Establish `e3 : A * Real.exp (s 0) = 1` using `by rw [hAdef, ← Real.exp_add]; simp`.

Establish `e4 : D * Real.exp (s j) = 1` using `by rw [hDdef, ← Real.exp_add]; simp`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem simple_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y → ∀ a, IsTorus σ J X Y a → ∀ (Ω C : Set (GAd σ J)), IsCompact Ω → Ω ⊆ minParOne σ J X → IsCompact C → ∃ M : ℝ, 0 < M ∧ ∀ ω ∈ Ω, ∀ s : Fin (r + 1) → ℝ, ∀ κ ∈ C, ∀ e : E, e ≠ 0 → NearMin σ J (ω * a s * κ) (e • Xᵀ 0) → ∀ j : Fin (r + 1), j.val = 1 → Real.exp (s j) ≤ M * Real.exp (s 0) := by
  intro F E _ _ _ _ _ σ h n J hJ r X Y hW a ha Ω C hΩ hΩ1 hC
  haveI := h.1
  by_cases hr : ∃ j : Fin (r + 1), j.val = 1
  swap
  · exact ⟨1, one_pos, fun ω _ s κ _ e _ _ j hj => absurd ⟨j, hj⟩ hr⟩
  obtain ⟨j, hj⟩ := hr
  have hF := pfrA h hJ hW
  have := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hBc : Continuous fun p : GAd σ J => Bm σ J X Y p⁻¹ := continuous_Bm.comp continuous_inv
  have hA₁ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ 0 0) '' Ω) := hΩ.image (hBc.matrix_elem 0 0)
  have hA₂ : IsCompact ((fun p : GAd σ J => Bm σ J X Y p⁻¹ j j) '' Ω) := hΩ.image (hBc.matrix_elem j j)
  obtain ⟨P, hP, hlow⟩ := GlobalTheory.T.compact_height_lower_bound F E σ h n J (Ω * C) (hΩ.mul hC)
  obtain ⟨P₄, hP₄, hup⟩ := upper_bound h (Xᵀ 0) (Xᵀ j) hA₁ hA₂ hC
  obtain ⟨K, hKdef⟩ : ∃ K, K = 2 * P * P₄ := ⟨_, rfl⟩
  have hK : 0 < K := by rw [hKdef]; positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε, ε = 1 / (K + 1) := ⟨_, rfl⟩
  have hε : 0 < ε := by rw [hεdef]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one (by positivity)]
    linarith
  obtain ⟨d, hd⟩ : ∃ d, d = Module.finrank ℚ F := ⟨_, rfl⟩
  have hd0 : d ≠ 0 := by rw [hd]; exact Module.finrank_pos.ne'
  have hKε : K * ε ^ d < 1 := by
    have h1 : ε ^ d ≤ ε := pow_le_of_le_one hε.le hε1 hd0
    calc K * ε ^ d ≤ K * ε := mul_le_mul_of_nonneg_left h1 hK.le
      _ = K / (K + 1) := by rw [hεdef]; ring
      _ < 1 := by rw [div_lt_one (by positivity)]; linarith
  obtain ⟨N, hN1, hN⟩ := GlobalTheory.T.adelic_tensor_rational_approximation F E ε hε
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  refine ⟨(K + 1) * N, by positivity, ?_⟩
  intro ω hω s κ hκ e he hNM j' hj'
  rw [show j' = j from Fin.ext (hj'.trans hj.symm)]
  have m1 : ω ∈ minPar σ J X := minParOne_subset (hΩ1 hω)
  have m2 : ω⁻¹ ∈ minPar σ J X := inv_mem_minPar h hJ hW m1
  obtain ⟨hBt, eB⟩ := (mem_minPar_iff hF).1 m2
  obtain ⟨hBt', -⟩ := (mem_minPar_iff hF).1 m1
  have hu1 : Bm σ J X Y ω⁻¹ 0 0 * Bm σ J X Y ω 0 0 = 1 := by
    rw [← diag_mul_bt hBt hBt', ← Bm_mul hF m2 m1, inv_mul_cancel, Bm_one hF, Matrix.one_apply_eq]
  have hb : Bm σ J X Y ω⁻¹ 0 0 * (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0) = Bm σ J X Y ω⁻¹ 0 j := by
    rw [mul_left_comm, hu1, mul_one]
  obtain ⟨q, hq1, hqN, c, hc⟩ := hN (Bm σ J X Y ω⁻¹ 0 j * Bm σ J X Y ω 0 0)
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)

  have hj0 : j ≠ 0 := fun e0 => by rw [e0] at hj; simp at hj
  have hyx : cT (σ : E →+* E) Y * J * X = 1 :=
    PFr.yx (s := (σ : E →+* E)) (Jm := J) (Xm := X) (Ym := Y)
      ⟨fun x => sigma_sigma h x, Matrix.ext fun i k => hJ.1 i k, hW.xx, hW.yy, hW.xy⟩
  have hcol : ∀ i k, ((cT (σ : E →+* E) Y * J) *ᵥ Xᵀ i) k = (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) k i := fun i k => by
    rw [← hyx]; rfl
  have hu0 : (q : E) • Xᵀ j - c • Xᵀ 0 ≠ 0 := fun h0 => by
    have e1 := congrFun (congrArg (fun v => (cT (σ : E →+* E) Y * J) *ᵥ v) h0) j
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_zero, Pi.sub_apply, Pi.smul_apply, hcol, smul_eq_mul,
      Matrix.one_apply_eq, Matrix.one_apply_ne hj0, mul_one, mul_zero, sub_zero, Pi.zero_apply] at e1
    exact hq0 e1
  let Bf := toLinearMapₛₗ₂' E (σ : E →+* E) (RingHom.id E) J
  have hBf : ∀ u v, Bf u v = ∑ i, ∑ j, σ (u i) * J i j * v j := fun u v => by
    simp only [Bf, toLinearMapₛₗ₂'_apply, smul_eq_mul, RingHom.id_apply, RingHom.coe_coe]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hg : ∀ i k, Bf (Xᵀ i) (Xᵀ k) = 0 := fun i k => by
    have e1 := gram_apply (σ := σ) (J := J) X X i k
    rw [hW.xx] at e1
    exact e1.symm
  have hiso : hE σ J ((q : E) • Xᵀ j - c • Xᵀ 0) ((q : E) • Xᵀ j - c • Xᵀ 0) = 0 := by
    refine (hBf _ _).symm.trans ?_
    simp only [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, hg, smul_zero, mul_zero, sub_zero]
  have hNM' := hNM.2.2 _ hu0 hiso

  obtain ⟨A, hAdef⟩ : ∃ A, A = Real.exp (-s 0) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ D, D = Real.exp (-s j) := ⟨_, rfl⟩
  have hA : 0 < A := hAdef ▸ Real.exp_pos _
  have hD : 0 < D := hDdef ▸ Real.exp_pos _
  obtain ⟨T, hTdef⟩ : ∃ T, T = max (ε * A) (N * D) := ⟨_, rfl⟩
  have hT1 : ε * A ≤ T := hTdef ▸ le_max_left _ _
  have hT2 : N * D ≤ T := hTdef ▸ le_max_right _ _
  have hT : 0 < T := lt_of_lt_of_le (by positivity) hT1
  have hexp : ∀ x : ℝ, Real.exp (x - Real.log T) = Real.exp x / T := fun x => by
    rw [Real.exp_sub, Real.exp_log hT]
  have hζ := rId_mul_mem_boxE (c := -s 0 - Real.log T) (ρ := 1) (by
    rw [hexp, ← hAdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]; exact hT1) hc
  have hz : (q : AF F) * rId F (-s j - Real.log T) ∈ boxF F 1 := by
    rw [mul_comm]
    refine rId_mul_mem_boxF ?_ (natCast_mem_boxF q)
    rw [hexp, ← hDdef, div_mul_eq_mul_div, div_le_one hT, mul_comm]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hqN) hD.le).trans hT2
  have hup' := hup κ hκ _ ⟨ω, hω, rfl⟩ _ ⟨ω, hω, rfl⟩ _ hζ _ hz
  have e1 := hgt_pair ha hBt eB s κ hj q c hb (Real.log T)
  have e2 := hgt_line ha m2 s κ e
  have hl := hlow (ω * κ) (Set.mul_mem_mul hω hκ) (e • Xᵀ 0) hNM.1
  rw [← hd] at e1 e2
  have eT : Real.exp (d * Real.log T) = T ^ d := by rw [Real.exp_nat_mul, Real.exp_log hT]
  have eA : Real.exp (d * (-s 0)) = A ^ d := by rw [Real.exp_nat_mul, hAdef]
  rw [eT] at e1
  rw [eA] at e2
  have hmain : A ^ d ≤ K * T ^ d := by
    calc A ^ d ≤ A ^ d * (P * hgt σ J (ω * κ) (e • Xᵀ 0)) := le_mul_of_one_le_right (by positivity) hl
      _ = P * hgt σ J (ω * a s * κ) (e • Xᵀ 0) := by rw [e2]; ring
      _ ≤ P * (2 * hgt σ J (ω * a s * κ) ((q : E) • Xᵀ j - c • Xᵀ 0)) := mul_le_mul_of_nonneg_left hNM' hP.le
      _ ≤ P * (2 * (T ^ d * P₄)) := by
          rw [e1]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hup' (by positivity))
            (by norm_num)) hP.le
      _ = K * T ^ d := by rw [hKdef]; ring
  rcases le_total (N * D) (ε * A) with hc1 | hc1
  · exfalso
    have eT' : T = ε * A := by rw [hTdef, max_eq_left hc1]
    rw [eT', mul_pow] at hmain
    have hAd : 0 < A ^ d := by positivity
    nlinarith
  · have eT' : T = N * D := by rw [hTdef, max_eq_right hc1]
    have h3 : A ≤ (K + 1) * N * D := by
      have h4 : K ≤ (K + 1) ^ d := by
        have : K + 1 ≤ (K + 1) ^ d := le_self_pow₀ (by linarith) hd0
        linarith
      have h5 : A ^ d ≤ ((K + 1) * N * D) ^ d := by
        rw [eT'] at hmain
        rw [mul_assoc, mul_pow]
        exact hmain.trans (mul_le_mul_of_nonneg_right h4 (by positivity))
      exact (pow_le_pow_iff_left₀ hA.le (by positivity) hd0).1 h5
    have e3 : A * Real.exp (s 0) = 1 := by rw [hAdef, ← Real.exp_add]; simp
    have e4 : D * Real.exp (s j) = 1 := by rw [hDdef, ← Real.exp_add]; simp
    calc Real.exp (s j) = Real.exp (s j) * (A * Real.exp (s 0)) := by rw [e3, mul_one]
      _ ≤ Real.exp (s j) * ((K + 1) * N * D * Real.exp (s 0)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le) (Real.exp_pos _).le
      _ = (K + 1) * N * Real.exp (s 0) * (D * Real.exp (s j)) := by ring
      _ = (K + 1) * N * Real.exp (s 0) := by rw [e4, mul_one]

end GlobalTheory.CompanionTheory.RedCov.Simple

end
