import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FactorBounds
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeightedNormSquareRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OrthogonalNormSquareSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGramPosSemidefAndNormAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorBoundAtEmbeddingOfComplexOpNormSq

open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder Matrix

noncomputable section

namespace GlobalTheory.LastPeriod

open GlobalTheory.IndefiniteRowSideFullHecke.OrthogonalNormSquareSum GlobalTheory.ColNorms GlobalTheory.PeriodClassSum

/- English proof (translation)
Use extensionality with `a b`. Establish `ha` using `a.2`. Establish `hb` using `b.2`. Simplify using `only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem gramSum_one {K : Type} [Field K] {N n : ℕ} (hN : N = n + 1) :
    gramSum hN (1 : Matrix (Fin n) (Fin n) K) 1 = 1 := by
  ext a b
  have ha := a.2
  have hb := b.2
  simp only [gramSum, Matrix.of_apply, Matrix.one_apply, Fin.ext_iff, Br.iL]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Introduce `x`. Establish `h` using `(hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1) (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ)) (fun τ => by simpa using ht τ)).2.2.1 ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam …`. Simplify using `only [gramSum_one] at h`. Rewrite using `[GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]`. Use `le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h` and prove the remaining obligations.

Simplify using `only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply, Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]`. Rewrite using `[MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]`. Use `congr 2`. Conclude with `Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm`.
-/
theorem coefOpLe_brAt (hL : LastMapNorm) {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι]
    {N n : ℕ} (hN : N = n + 1) (lam : ι → DomWeight N) (sg : ι → DomWeight n)
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (T : ℝ) (hT : 0 < T) (t : ι → K)
    (ht : ∀ τ, star (σ (t τ)) * σ (t τ) = (T : ℂ)) :
    CoefOpLe σ lam sg (Br.brAt hN lam sg t) (T ^ (-∑ τ, Br.nBr (lam τ) (sg τ)) * orthNormSq hN lam sg) := by
  intro x
  have h := (hL ℂ (RingHom.id ℂ) (fun _ => rfl) ι N n hN lam sg hI hS (fun _ => 1)
    (fun _ => by simpa using Matrix.PosDef.one) T hT (fun _ => 1) (fun τ => σ (t τ))
    (fun τ => by simpa using ht τ)).2.2.1
    ⟨MvPolynomial.map σ (x : Pol K ι N), GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩
  simp only [gramSum_one] at h
  rw [GlobalTheory.JetBase.sqAt_eq σ lam x ⟨_, GlobalTheory.Proof.TensorMapDescent.map_mem_VV σ lam _ x.2⟩ rfl]
  refine le_of_eq_of_le (GlobalTheory.JetBase.sqAt_eq σ sg _ _ ?_) h
  simp only [Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

/- English proof (translation)
Simplify using `only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply, mul_assoc]`.
-/
theorem sqAt_eq_dot {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (x : Formalism.L2.DIV.VV K lam) :
    sqAt σ lam x = (star (fun i => σ ((bVV K lam).repr x i)) ⬝ᵥ (GlobalTheory.TestLat.Compare.gramB K lam).map σ *ᵥ
      fun i => σ ((bVV K lam).repr x i)).re := by
  simp only [sqAt, pairK_one_basis, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply,
    starRingEnd_apply, mul_assoc]

/- English proof (translation)
Establish `hG` using `(gramB_posDef sg σ).posSemidef`. Establish `hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ) (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re = ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c)` using `fun z => by`. Rewrite using `[wForm, Complex.re_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[sqAt_eq_dot, ← Complex.re_ofReal_mul]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ) (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))`. Rewrite using `[map_sum, wForm]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_inv₀, map_natCast, star_star, map_pairBK]`. Establish `h` using `wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))`. Rewrite `h` using `[wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3]`. Establish `h0` using `(Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1`. Rewrite `h0` using `[hre]`.

Rewrite `h` using `[hre fun c => B (x c), hre]`. Use `h.trans (mul_le_mul_of_nonneg_right ?_ h0)` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_le_sum fun c _ => ?_` and prove the remaining obligations. Rewrite using `[mul_left_comm]`.

Conclude with `mul_le_mul_of_nonneg_left (hB _) (by positivity)`.
-/
theorem sum_pair_le {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {N n : ℕ}
    (lam : ι → DomWeight N) (sg : ι → DomWeight n) (B : Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K sg) (t : ℝ)
    (hB : CoefOpLe σ lam sg B t) {C : Type} [Fintype C] (w : C → ℕ) (x : C → Formalism.L2.DIV.VV K lam)
    (y : C → Formalism.L2.DIV.VV K sg) :
    ‖σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c))‖ ^ 2 ≤
      t * (∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ lam (x c)) * ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (y c) := by
  have hG := (gramB_posDef sg σ).posSemidef
  have hre : ∀ z : C → Formalism.L2.DIV.VV K sg, (wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c i => σ ((bVV K sg).repr (z c) i)) (fun c i => σ ((bVV K sg).repr (z c) i))).re =
      ∑ c, ((w c : ℕ) : ℝ)⁻¹ * sqAt σ sg (z c) := fun z => by
    rw [wForm, Complex.re_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [sqAt_eq_dot, ← Complex.re_ofReal_mul]
    push_cast
    rfl
  have e3 : σ (∑ c, ((w c : ℕ) : K)⁻¹ * pairBK sg (B (x c)) (y c)) = wForm w ((GlobalTheory.TestLat.Compare.gramB K sg).map σ)
      (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i)) := by
    rw [map_sum, wForm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, map_inv₀, map_natCast, star_star, map_pairBK]
  have h := wForm_le w hG (fun c => star fun i => σ ((bVV K sg).repr (B (x c)) i)) (fun c i => σ ((bVV K sg).repr (y c) i))
  rw [wForm_star w (by rw [← Matrix.transpose_map, GlobalTheory.TestLat.Compare.gramB_transpose]), ← e3] at h
  have h0 := (Complex.nonneg_iff.1 (wForm_nonneg w hG (fun c i => σ ((bVV K sg).repr (y c) i)))).1
  rw [hre] at h0
  rw [hre fun c => B (x c), hre] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ h0)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hB _) (by positivity)

/- English proof (translation)
Rewrite using `[sqAt_eq_dot]`. Conclude with `(Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1`.
-/
theorem sqAt_nonneg {K : Type} [Field K] [CharZero K] [StarRing K] (σ : K →+* ℂ) {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (x : Formalism.L2.DIV.VV K lam) : 0 ≤ sqAt σ lam x := by
  rw [sqAt_eq_dot]
  exact (Complex.nonneg_iff.1 ((gramB_posDef lam σ).posSemidef.dotProduct_mulVec_nonneg _)).1

/- English proof (translation)
Rewrite using `[← Complex.re_ofReal_mul]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem re_inv_mul (w : ℕ) (z : ℂ) : ((w : ℂ)⁻¹ * z).re = (w : ℝ)⁻¹ * z.re := by
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

end GlobalTheory.LastPeriod

end
