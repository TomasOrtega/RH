import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.ContinuousPair

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL LineDeriv
open scoped Real RealInnerProductSpace FourierTransform

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

/- English proof (translation)
Simplify using `[Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem J_mul_transpose_inl (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inl a) j = -s j (.inr a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/- English proof (translation)
Simplify using `[Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem J_mul_transpose_inr (s : Mat l) (a : l) (j : l ⊕ l) :
    (Matrix.J l ℝ * sᵀ) (.inr a) j = s j (.inl a) := by
  simp [Matrix.J, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/- English proof (translation)
Establish `h` using `congrFun (congrFun (SymplecticGroup.mem_iff.1 s.2) i) j`. Rewrite `h` using `[Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type]`. Simplify using `only [J_mul_transpose_inl, J_mul_transpose_inr] at h`. Rewrite using `[← h, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun a _ => by ring`.
-/
theorem sp_rel (s : Sp l) (i j : l ⊕ l) :
    ∑ a, (s.1 i (.inr a) * s.1 j (.inl a) - s.1 i (.inl a) * s.1 j (.inr a)) = Matrix.J l ℝ i j := by
  have h := congrFun (congrFun (SymplecticGroup.mem_iff.1 s.2) i) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type] at h
  simp only [J_mul_transpose_inl, J_mul_transpose_inr] at h
  rw [← h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/- English proof (translation)
Introduce `s`. Set `N : Matrix l (l ⊕ l) ℝ` to `Matrix.of fun a k => s.1 (.inl a) k`. Set `K : Matrix (l ⊕ l) l ℝ` to `Matrix.of fun k b => Sum.elim (fun c => s.1 (.inr b) (.inr c)) (fun c => -s.1 (.inr b) (.inl c)) k`. Establish `hNK : N * K = 1`. Use extensionality with `a b`.

Establish `h` using `sp_rel s (.inl a) (.inr b)`. Rewrite using `[Matrix.mul_apply, Fintype.sum_sum_type]`. Simplify using `only [N, K, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]`.

Conclude with `Finset.sum_congr rfl fun c _ => by ring`. Use `_ = _ := by rw [h]; simp [Matrix.J, Matrix.one_apply]`. Establish `hM : (N * Nᵀ).det ≠ 0`. Introduce `hd`. Take `⟨v, hv, hvM⟩` from `Matrix.exists_vecMul_eq_zero_iff.2 hd`.

Establish `h1 : (v ᵥ* N) ⬝ᵥ (v ᵥ* N) = 0`. Establish `: (v ᵥ* (N * Nᵀ)) ⬝ᵥ v = 0` using `by rw [hvM, zero_dotProduct]`. Rewrite `this` using `[← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]`. Then use the resulting hypothesis. Establish `h2 : v ᵥ* N = 0` using `dotProduct_self_eq_zero.1 h1`. Apply `hv` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Set `W : Matrix l l ℂ` to `Matrix.of fun c b => (s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)`. Establish `hPW : upperParabolic s.1 * W = (N * Nᵀ).map ofReal`. Use extensionality with `a b`. Establish `hs` using `sp_rel s (.inl a) (.inl b)`.

Simplify using `only [Matrix.J, fromBlocks_apply₁₁, Matrix.zero_apply] at hs`. Establish `e : ∀ c, ((s.1 (.inl a) (.inl c) : ℂ) - I * s.1 (.inl a) (.inr c)) * ((s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)) = ((s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inl c) + s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) - I * ((s.1 (.inl a) (.inr c) * s.1 (.inl b) …` using `fun c => by`. Use `push_cast`. Take the linear combination `(-((s.1 (.inl a) (.inr c) : ℂ) * (s.1 (.inl b) (.inr c) : ℂ))) * I_sq`. Simplify using `only [Matrix.mul_apply, upperParabolic, W, Matrix.of_apply, Matrix.map_apply, N, Matrix.transpose_apply, Fintype.sum_sum_type]`.

Rewrite using `[Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ofReal_sum, ← ofReal_sum, hs]`. Use `push_cast`. Rewrite using `[Finset.sum_add_distrib]`. Simplify using the standard rewrite rules. Establish `e : ((N * Nᵀ).map ofReal).det = ((N * Nᵀ).det : ℂ)`.

Rewrite using `[show (N * Nᵀ).map ofReal = ofRealHom.mapMatrix (N * Nᵀ) from rfl, ← RingHom.map_det]`. Both sides reduce to the same expression. Introduce `h0`. Use `congrArg Matrix.det hPW` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, e]`.

Unfold `dd at h0`. Rewrite `this` using `[h0, zero_mul]`. Conclude with `hM (ofReal_eq_zero.1 this.symm)`.
-/
theorem ddNe : DdNe l := by
  intro s
  let N : Matrix l (l ⊕ l) ℝ := Matrix.of fun a k => s.1 (.inl a) k
  let K : Matrix (l ⊕ l) l ℝ := Matrix.of fun k b =>
    Sum.elim (fun c => s.1 (.inr b) (.inr c)) (fun c => -s.1 (.inr b) (.inl c)) k
  have hNK : N * K = 1 := by
    ext a b
    have h := sp_rel s (.inl a) (.inr b)
    rw [Matrix.mul_apply, Fintype.sum_sum_type]
    simp only [N, K, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
    calc _ = -∑ c, (s.1 (.inl a) (.inr c) * s.1 (.inr b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inr b) (.inr c)) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ = _ := by rw [h]; simp [Matrix.J, Matrix.one_apply]
  have hM : (N * Nᵀ).det ≠ 0 := by
    intro hd
    obtain ⟨v, hv, hvM⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hd
    have h1 : (v ᵥ* N) ⬝ᵥ (v ᵥ* N) = 0 := by
      have : (v ᵥ* (N * Nᵀ)) ⬝ᵥ v = 0 := by rw [hvM, zero_dotProduct]
      rwa [← Matrix.vecMul_vecMul, ← Matrix.dotProduct_mulVec, Matrix.mulVec_transpose] at this
    have h2 : v ᵥ* N = 0 := dotProduct_self_eq_zero.1 h1
    apply hv
    calc v = v ᵥ* (N * K) := by rw [hNK, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, h2, Matrix.zero_vecMul]
  let W : Matrix l l ℂ := Matrix.of fun c b => (s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)
  have hPW : upperParabolic s.1 * W = (N * Nᵀ).map ofReal := by
    ext a b
    have hs := sp_rel s (.inl a) (.inl b)
    simp only [Matrix.J, fromBlocks_apply₁₁, Matrix.zero_apply] at hs
    have e : ∀ c, ((s.1 (.inl a) (.inl c) : ℂ) - I * s.1 (.inl a) (.inr c)) *
        ((s.1 (.inl b) (.inl c) : ℂ) + I * s.1 (.inl b) (.inr c)) =
        ((s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inl c) + s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) -
        I * ((s.1 (.inl a) (.inr c) * s.1 (.inl b) (.inl c) - s.1 (.inl a) (.inl c) * s.1 (.inl b) (.inr c) : ℝ) : ℂ) :=
      fun c => by
        push_cast
        linear_combination (-((s.1 (.inl a) (.inr c) : ℂ) * (s.1 (.inl b) (.inr c) : ℂ))) * I_sq
    simp only [Matrix.mul_apply, upperParabolic, W, Matrix.of_apply, Matrix.map_apply, N, Matrix.transpose_apply,
      Fintype.sum_sum_type]
    rw [Finset.sum_congr rfl fun c _ => e c, Finset.sum_sub_distrib, ← Finset.mul_sum, ← ofReal_sum, ← ofReal_sum, hs]
    push_cast
    rw [Finset.sum_add_distrib]
    simp
  have e : ((N * Nᵀ).map ofReal).det = ((N * Nᵀ).det : ℂ) := by
    rw [show (N * Nᵀ).map ofReal = ofRealHom.mapMatrix (N * Nᵀ) from rfl, ← RingHom.map_det]
    rfl
  intro h0
  have := congrArg Matrix.det hPW
  rw [Matrix.det_mul, e] at this
  unfold dd at h0
  rw [h0, zero_mul] at this
  exact hM (ofReal_eq_zero.1 this.symm)

def nn (S : Matrix l l ℝ) (t : ℝ) : Mat l := fromBlocks 1 (t • S) 0 1

/- English proof (translation)
Rewrite using `[SymplecticGroup.mem_iff, nn, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]`. Simplify using `[hS.eq]`.
-/
theorem nn_mem {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) : nn S t ∈ Matrix.symplecticGroup l ℝ := by
  rw [SymplecticGroup.mem_iff, nn, Matrix.J, fromBlocks_transpose, fromBlocks_multiply, fromBlocks_multiply]
  simp [hS.eq]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [upperParabolic, loQ, nn, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁, fromBlocks_apply₁₂, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ofReal_add …`. Establish `e : ∀ u v : l → ℝ, ∑ c, (t : ℂ) * (S a c : ℂ) * (u c : ℂ) - I * ∑ c, (t : ℂ) * (S a c : ℂ) * (v c : ℂ) = (t : ℂ) * ∑ c, (S a c : ℂ) * ((u c : ℂ) - I * (v c : ℂ))` using `fun u v => by`. Simplify using `only [Finset.mul_sum]`. Rewrite using `[← Finset.sum_sub_distrib]`.

Conclude with `Finset.sum_congr rfl fun c _ => by ring`. Rewrite using `[← e]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem upperPart_unipotent_mul (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) :
    upperParabolic (nn S t * s) = upperParabolic s + (t : ℂ) • (S.map ofReal * loQ s) := by
  ext a b
  simp only [upperParabolic, loQ, nn, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_sum_type, fromBlocks_apply₁₁,
    fromBlocks_apply₁₂, Matrix.one_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, ofReal_add, ofReal_sum, ofReal_mul]
  have e : ∀ u v : l → ℝ, ∑ c, (t : ℂ) * (S a c : ℂ) * (u c : ℂ) - I * ∑ c, (t : ℂ) * (S a c : ℂ) * (v c : ℂ) =
      (t : ℂ) * ∑ c, (S a c : ℂ) * ((u c : ℂ) - I * (v c : ℂ)) := fun u v => by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [← e]
  ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `[loQ, nn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]`.
-/
theorem loQ_nn (S : Matrix l l ℝ) (t : ℝ) (s : Mat l) : loQ (nn S t * s) = loQ s := by
  ext a b
  simp [loQ, nn, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tc_apply (M : Matrix l l ℝ) (x : Eu l) (a : l) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) M x a = ∑ b, M a b * x b := rfl

/- English proof (translation)
Use extensionality with `x a`. Simplify using `[bl_apply, nn, Matrix.one_apply]`.
-/
theorem metaplectic_unipotent_block_first_diag (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inl Sum.inl (nn S t) = 1 := by
  ext x a
  simp [bl_apply, nn, Matrix.one_apply]

/- English proof (translation)
Use extensionality with `x a`. Simplify using `[bl_apply, nn, tc_apply, Finset.mul_sum, mul_assoc]`.
-/
theorem metaplectic_unipotent_block_upper (S : Matrix l l ℝ) (t : ℝ) :
    bl Sum.inl Sum.inr (nn S t) = t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S := by
  ext x a
  simp [bl_apply, nn, tc_apply, Finset.mul_sum, mul_assoc]

/- English proof (translation)
Use extensionality with `x a`. Simplify using `[bl_apply, nn]`.
-/
theorem metaplectic_unipotent_block_lower (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inr Sum.inl (nn S t) = 0 := by
  ext x a
  simp [bl_apply, nn]

/- English proof (translation)
Use extensionality with `x a`. Simplify using `[bl_apply, nn, Matrix.one_apply]`.
-/
theorem metaplectic_unipotent_block_second_diag (S : Matrix l l ℝ) (t : ℝ) : bl Sum.inr Sum.inr (nn S t) = 1 := by
  ext x a
  simp [bl_apply, nn, Matrix.one_apply]

def UU (S : Matrix l l ℝ) (t : ℝ) : Sch l →L[ℂ] Sch l :=
  fou l * (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) * fouInv l)

/- English proof (translation)
Establish `hS' : ∀ a b, S a b = S b a` using `fun a b => by`. Simplify using `using (congrFun (congrFun hS.eq b) a)`. Simplify using `only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]`. Use `congr 2`. Simplify using `only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hS']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem inner_sym {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (x y : Eu l) :
    ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) y⟫ =
      ⟪y, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ := by
  have hS' : ∀ a b, S a b = S b a := fun a b => by
    simpa using (congrFun (congrFun hS.eq b) a)
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]
  congr 2
  simp only [PiLp.inner_apply, tc_apply, RCLike.inner_apply, conj_trivial, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hS']
  ring

/- English proof (translation)
Establish `h` using `(intw_fou _ _).mul ((intw_ph (inner_sym hS t) _ _).mul (intw_fouInv p q))`. Rewrite using `[show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q = -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by`. Rewrite using `[ContinuousLinearMap.neg_apply, neg_add, neg_neg, neg_neg]]`. Conclude with `h`.
-/
theorem intw_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (p q : Eu l) :
    Intw (UU S t) p q (p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q) q := by
  have h := (intw_fou _ _).mul ((intw_ph (inner_sym hS t) _ _).mul (intw_fouInv p q))
  rw [show p + (t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S) q =
    -(-p + (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) q) by
      rw [ContinuousLinearMap.neg_apply, neg_add, neg_neg, neg_neg]]
  exact h

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun f => (iso_fou.mul ((iso_ph _).mul iso_fouInv)) f, fun w f g hg => by have := intw_UU hS t (pPart w) (qPart w) f g hg rw [rhoFun_eq, pPart_mulVec, qPart_mulVec, metaplectic_unipotent_block_first_diag, metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metap …`.
-/
theorem impl_UU {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) :
    Impl (fun w => nn S t *ᵥ w) (UU S t).toLinearMap :=
  ⟨fun f => (iso_fou.mul ((iso_ph _).mul iso_fouInv)) f, fun w f g hg => by
    have := intw_UU hS t (pPart w) (qPart w) f g hg
    rw [rhoFun_eq, pPart_mulVec, qPart_mulVec, metaplectic_unipotent_block_first_diag,
      metaplectic_unipotent_block_upper, metaplectic_unipotent_block_lower, metaplectic_unipotent_block_second_diag]
    simpa using this⟩

/- English proof (translation)
The claim follows from `isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)`.
-/
theorem isUnit_UU (S : Matrix l l ℝ) (t : ℝ) : IsUnit (UU S t) :=
  isUnit_fou.mul ((isUnit_ph _).mul isUnit_fouInv)

/- English proof (translation)
Establish `hs : Function.Surjective (UU S t).toLinearMap` using `fun f => ⟨Ring.inverse (UU S t) f, by show (UU S t * Ring.inverse (UU S t)) f = f`. Rewrite using `[Ring.mul_inverse_cancel _ (isUnit_UU S t), ContinuousLinearMap.one_apply]⟩`. Conclude with `Impl.dRho (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f`.
-/
theorem UU_dRho {S : Matrix l l ℝ} (hS : S.IsSymm) (t : ℝ) (w : l ⊕ l → ℝ) (f : Sch l) :
    UU S t (dRho w f) = dRho (nn S t *ᵥ w) (UU S t f) := by
  have hs : Function.Surjective (UU S t).toLinearMap := fun f => ⟨Ring.inverse (UU S t) f, by
    show (UU S t * Ring.inverse (UU S t)) f = f
    rw [Ring.mul_inverse_cancel _ (isUnit_UU S t), ContinuousLinearMap.one_apply]⟩
  exact Impl.dRho (s := Matrix.mulVecLin (nn S t)) (impl_UU hS t) hs w f

/- English proof (translation)
Simplify using `[UU, ph_zero, fou_mul_fouInv]`.
-/
theorem UU_zero (S : Matrix l l ℝ) : UU S 0 = 1 := by
  simp [UU, ph_zero, fou_mul_fouInv]

/- English proof (translation)
Rewrite using `[fou_apply, fourier_coe, Real.fourier_eq]`. Simplify using the standard rewrite rules.
-/
theorem fou_zero (h : Sch l) : fou l h 0 = ∫ x, h x := by
  rw [fou_apply, fourier_coe, Real.fourier_eq]
  simp

/- English proof (translation)
Establish `e1 : ∀ t, UU S t f 0 = ∫ x, ph (-(t • Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) (fouInv l f) x := fun t => by`. Rewrite using `[UU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fou_zero]`. Establish `e2 : fouInv l (UU S t₀ f) = ph (-(t₀ • Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) (fouInv l f) := by`. Rewrite using `[UU, ← ContinuousLinearMap.mul_apply, ← mul_assoc, fouInv_mul_fou, one_mul, ContinuousLinearMap.mul_apply]`. Establish `hq : ∀ x : Eu l, |⟪x, Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S x⟫| ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2 := fun x => (abs_real_inner_le_norm _ _).trans (by`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S).le_opNorm x`. Use `_ = _ := by ring)`. Establish `ph_eq : ∀ (t : ℝ) (x : Eu l), ph (-(t • Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) (fouInv l f) x = exp (((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ) * I) * fouInv l f x := fun t x => by`. Establish `: -π * ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) x⟫ = π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t := by`.

Simplify using `only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right, real_inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[ph_apply, this]`. Establish `mq_eq : ∀ (h : Sch l) (x : Eu l), mq (-(Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) h x = ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) * I * h x := fun h x => by`. Establish `: -π * ⟪x, (-(Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) x⟫ = π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ := by`.

Simplify using `only [ContinuousLinearMap.neg_apply, inner_neg_right]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[mq_apply, this]`. Establish `key` using `hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀) (F := fun t x => ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x) (F' := fun t x => mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) …`. Rewrite using `[mq_eq, ph_eq, norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]`.

Establish `h1` using `hq x`. Establish `h2` using `norm_nonneg (fouInv l f x)`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(((fouInv l f).integrable_pow_mul volume 2).const_mul _)`. Use the proof step `(.of_forall fun x t _ => by`.

Simplify using `only [ph_eq, mq_eq]`. Establish `h1 : HasDerivAt (fun t : ℝ => ((π * ⟪x, Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S x⟫ * t : ℝ) : ℂ)) ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) t := by`. Use `((hasDerivAt_id t).const_mul (π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫)).ofReal_comp` as an intermediate fact. Simplify using `using this`. Conclude with `((h1.mul_const I).cexp.mul_const (fouInv l f x)).congr_deriv (by ring))`.

Rewrite using `[e2, fou_zero]`. Conclude with `key.2.congr_of_eventuallyEq (.of_forall e1)`.
-/
theorem hasDerivAt_UU (S : Matrix l l ℝ) (f : Sch l) (t₀ : ℝ) :
    HasDerivAt (fun t => UU S t f 0)
      (fou l (mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l (UU S t₀ f))) 0) t₀ := by
  have e1 : ∀ t, UU S t f 0 = ∫ x, ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x := fun t => by
    rw [UU, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, fou_zero]
  have e2 : fouInv l (UU S t₀ f) = ph (-(t₀ • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) := by
    rw [UU, ← ContinuousLinearMap.mul_apply, ← mul_assoc, fouInv_mul_fou, one_mul, ContinuousLinearMap.mul_apply]
  have hq : ∀ x : Eu l, |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2 := fun x =>
    (abs_real_inner_le_norm _ _).trans (by
      calc ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x‖
          ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖) := by
            gcongr
            exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S).le_opNorm x
        _ = _ := by ring)
  have ph_eq : ∀ (t : ℝ) (x : Eu l), ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x =
      exp (((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ) * I) * fouInv l f x := fun t x => by
    have : -π * ⟪x, (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t := by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.smul_apply, inner_neg_right,
        real_inner_smul_right]
      ring
    rw [ph_apply, this]
  have mq_eq : ∀ (h : Sch l) (x : Eu l), mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) h x =
      ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) * I * h x := fun h x => by
    have : -π * ⟪x, (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) x⟫ =
        π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ := by
      simp only [ContinuousLinearMap.neg_apply, inner_neg_right]
      ring
    rw [mq_apply, this]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t₀)
    (F := fun t x => ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f) x)
    (F' := fun t x => mq (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S))
      (ph (-(t • Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) x)
    (bound := fun x => π * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * (‖x‖ ^ 2 * ‖fouInv l f x‖))
    Filter.univ_mem (.of_forall fun t => (ph _ (fouInv l f)).continuous.aestronglyMeasurable)
    ((ph _ (fouInv l f)).integrable) ((mq _ _).continuous.aestronglyMeasurable)
    (.of_forall fun x t _ => by
      rw [mq_eq, ph_eq, norm_mul, norm_mul, norm_mul, norm_I, norm_exp_ofReal_mul_I, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos Real.pi_pos]
      have h1 := hq x
      have h2 := norm_nonneg (fouInv l f x)
      calc π * |⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * 1 * (1 * ‖fouInv l f x‖)
          = π * (|⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫| * ‖fouInv l f x‖) := by ring
        _ ≤ π * ((‖Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S‖ * ‖x‖ ^ 2) * ‖fouInv l f x‖) := by gcongr
        _ = _ := by ring)
    (((fouInv l f).integrable_pow_mul volume 2).const_mul _)
    (.of_forall fun x t _ => by
      simp only [ph_eq, mq_eq]
      have h1 : HasDerivAt (fun t : ℝ => ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ * t : ℝ) : ℂ))
          ((π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫ : ℝ) : ℂ) t := by
        have := ((hasDerivAt_id t).const_mul (π * ⟪x, Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S x⟫)).ofReal_comp
        simpa using this
      exact ((h1.mul_const I).cexp.mul_const (fouInv l f x)).congr_deriv (by ring))
  rw [e2, fou_zero]
  exact key.2.congr_of_eventuallyEq (.of_forall e1)

/- English proof (translation)
Rewrite using `[dRho_eq_sum w]`. Simplify using `[Fintype.sum_sum_type, dRho_single_inl, dRho_single_inr]`.
-/
theorem dRho_eval_zero (w : l ⊕ l → ℝ) (h : Sch l) :
    dRho w h 0 = ∑ a, (w (.inl a) : ℂ) * (∂_{(EuclideanSpace.single a 1 : Eu l)} h) 0 := by
  rw [dRho_eq_sum w]
  simp [Fintype.sum_sum_type, dRho_single_inl, dRho_single_inr]

/- English proof (translation)
Establish `comm : ∀ w, dRho (Pi.single (.inl k) 1) (dRho w H) = dRho w (∂_{(EuclideanSpace.single k 1 : Eu l)} H) + (2 * π * I * sympl (Pi.single (.inl k) 1) w : ℂ) • H` using `fun w => by`. Use `congrArg (fun T : Sch l →L[ℂ] Sch l => T H) (dRho_comm (Pi.single (.inl k) 1) w)` as an intermediate fact. Simplify using `only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this`. Rewrite using `[← dRho_single_inl, ← this]`. Normalize the expressions using the abelian group laws.

Establish `hsy : ∀ w : l ⊕ l → ℝ, sympl (Pi.single (.inl k) 1) w = w (.inr k)` using `fun w => by`. Simplify using `[sympl, pPart, qPart, PiLp.inner_apply, Pi.single_apply]`. Establish `hcol : ∀ b c, (s *ᵥ Pi.single b 1) c = s c b` using `fun b c => by`. Simplify using `[mulVec, dotProduct, Pi.single_apply]`. Establish `e` using `congrArg (fun u : Sch l => dRho (Pi.single (.inl k) 1) u 0) (hA j)`.

Simplify using `only [map_smul, SchwartzMap.smul_apply, smul_eq_mul, comm, SchwartzMap.add_apply, dRho_eval_zero, hsy, hcol] at e`. Simplify using `only [upperParabolic, loQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]`. Take the linear combination `e`.
-/
theorem hess {s : Mat l} {H : Sch l} (hA : Ann s H) (j k : l) :
    ∑ a, upperParabolic s a j * (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} H)) 0 =
      -(2 * π * I) * loQ s k j * H 0 := by
  have comm : ∀ w, dRho (Pi.single (.inl k) 1) (dRho w H) =
      dRho w (∂_{(EuclideanSpace.single k 1 : Eu l)} H) + (2 * π * I * sympl (Pi.single (.inl k) 1) w : ℂ) • H :=
    fun w => by
      have := congrArg (fun T : Sch l →L[ℂ] Sch l => T H) (dRho_comm (Pi.single (.inl k) 1) w)
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply] at this
      rw [← dRho_single_inl, ← this]
      abel
  have hsy : ∀ w : l ⊕ l → ℝ, sympl (Pi.single (.inl k) 1) w = w (.inr k) := fun w => by
    simp [sympl, pPart, qPart, PiLp.inner_apply, Pi.single_apply]
  have hcol : ∀ b c, (s *ᵥ Pi.single b 1) c = s c b := fun b c => by
    simp [mulVec, dotProduct, Pi.single_apply]
  have e := congrArg (fun u : Sch l => dRho (Pi.single (.inl k) 1) u 0) (hA j)
  simp only [map_smul, SchwartzMap.smul_apply, smul_eq_mul, comm, SchwartzMap.add_apply, dRho_eval_zero, hsy,
    hcol] at e
  simp only [upperParabolic, loQ, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  linear_combination e

/- English proof (translation)
Establish `h1 : Pᵀ * M = c • Qᵀ`. Use extensionality with `j k`. Simplify using `[Matrix.mul_apply, h]`. Establish `hu : IsUnit Pᵀ.det`. Rewrite using `[det_transpose]`.

Conclude with `hP.isUnit`. Establish `h2 : M = Pᵀ⁻¹ * (c • Qᵀ)`. Rewrite using `[← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]`. Establish `h3 : ∑ j, ∑ k, S j k * M j k = (S * Mᵀ).trace`. Simplify using `[Matrix.trace, Matrix.mul_apply]`.

Establish `h4 : S * (Pᵀ⁻¹ * (c • Qᵀ))ᵀ = c • (S * Q * P⁻¹)`. Rewrite using `[transpose_mul, transpose_smul, transpose_transpose, transpose_nonsing_inv, transpose_transpose, Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]`. Rewrite using `[h3, h2, h4, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]`.
-/
theorem trace_eq {P Q : Matrix l l ℂ} (hP : P.det ≠ 0) (S M : Matrix l l ℂ) (c : ℂ)
    (h : ∀ j k, ∑ a, P a j * M a k = c * Q k j) : ∑ j, ∑ k, S j k * M j k = c * (P⁻¹ * (S * Q)).trace := by
  have h1 : Pᵀ * M = c • Qᵀ := by
    ext j k
    simp [Matrix.mul_apply, h]
  have hu : IsUnit Pᵀ.det := by
    rw [det_transpose]
    exact hP.isUnit
  have h2 : M = Pᵀ⁻¹ * (c • Qᵀ) := by
    rw [← h1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have h3 : ∑ j, ∑ k, S j k * M j k = (S * Mᵀ).trace := by
    simp [Matrix.trace, Matrix.mul_apply]
  have h4 : S * (Pᵀ⁻¹ * (c • Qᵀ))ᵀ = c • (S * Q * P⁻¹) := by
    rw [transpose_mul, transpose_smul, transpose_transpose, transpose_nonsing_inv, transpose_transpose,
      Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc]
  rw [h3, h2, h4, trace_smul, smul_eq_mul, Matrix.trace_mul_comm]

/- English proof (translation)
Establish `hu : IsUnit (P + (t₀ : ℂ) • K).det` using `hP.isUnit`. Establish `e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det * (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) + (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2)` using `fun t => by`. Rewrite using `[← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]`. Use `congr 1`. Normalize the expressions using the abelian group laws.

Establish `hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z + (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2) ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ)`. Use `(((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))` as an intermediate fact. Rewrite using `[sub_self, ofReal_zero]`. Conclude with `(this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)`. Establish `hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀`.

Simplify using `using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp`. Use `(hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det` as an intermediate fact. Rewrite `this` using `[mul_one]`. Conclude with `this.congr_of_eventuallyEq (.of_forall e)`.
-/
theorem hasDerivAt_det (P K : Matrix l l ℂ) (t₀ : ℝ) (hP : (P + (t₀ : ℂ) • K).det ≠ 0) :
    HasDerivAt (fun t : ℝ => (P + (t : ℂ) • K).det)
      ((P + (t₀ : ℂ) • K).det * ((P + (t₀ : ℂ) • K)⁻¹ * K).trace) t₀ := by
  have hu : IsUnit (P + (t₀ : ℂ) • K).det := hP.isUnit
  have e : ∀ t : ℝ, (P + (t : ℂ) • K).det = (P + (t₀ : ℂ) • K).det *
      (1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * ((t - t₀ : ℝ) : ℂ) +
        (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval
          ((t - t₀ : ℝ) : ℂ) * ((t - t₀ : ℝ) : ℂ) ^ 2) := fun t => by
    rw [← Matrix.det_one_add_smul, ← Matrix.det_mul, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
      ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul, ofReal_sub, sub_smul]
    congr 1
    abel
  have hφ : HasDerivAt (fun z : ℂ => 1 + ((P + (t₀ : ℂ) • K)⁻¹ * K).trace * z +
      (det (1 + (Polynomial.X : Polynomial ℂ) • ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX.eval z * z ^ 2)
      ((P + (t₀ : ℂ) • K)⁻¹ * K).trace ((t₀ - t₀ : ℝ) : ℂ) := by
    have := (((hasDerivAt_id (0 : ℂ)).const_mul ((P + (t₀ : ℂ) • K)⁻¹ * K).trace).const_add 1).add
      ((Polynomial.hasDerivAt (det (1 + (Polynomial.X : Polynomial ℂ) •
        ((P + (t₀ : ℂ) • K)⁻¹ * K).map Polynomial.C)).divX.divX (0 : ℂ)).mul ((hasDerivAt_id (0 : ℂ)).pow 2))
    rw [sub_self, ofReal_zero]
    exact (this.congr_deriv (by simp)).congr_of_eventuallyEq (.of_forall fun z => by simp)
  have hh : HasDerivAt (fun t : ℝ => ((t - t₀ : ℝ) : ℂ)) 1 t₀ := by
    simpa using ((hasDerivAt_id t₀).sub_const t₀).ofReal_comp
  have := (hφ.comp t₀ hh).const_mul (P + (t₀ : ℂ) • K).det
  rw [mul_one] at this
  exact this.congr_of_eventuallyEq (.of_forall e)

/- English proof (translation)
Introduce `S hS s' f hf`. Establish `hPt : ∀ t : ℝ, upperParabolic (nn S t * s'.1) = upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)` using `fun t => upperPart_unipotent_mul S t s'.1`. Establish `hdet : ∀ t : ℝ, (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det ≠ 0` using `fun t => by`. Rewrite using `[← hPt]`. Conclude with `ddNe ⟨_, mul_mem (nn_mem hS t) s'.2⟩`.

Establish `hAnn : ∀ t, Ann (nn S t * s'.1) (UU S t f)` using `fun t => hf.map (UU_dRho hS t)`. Establish `hF : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0) (-(1 / 2 : ℂ) * UU S t f 0 * ((upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1))⁻¹ * (S.map ofReal * loQ s'.1)).trace) t` using `fun t => by`. Establish `h1` using `hasDerivAt_UU S f t`. Rewrite `h1` using `[fou_mq_fouInv]`. Simplify using `only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul] at h1`.

Establish `h2` using `trace_eq (hdet t) (S.map ofReal) (Matrix.of fun a k => (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)} (UU S t f))) 0) (-(2 * π * I) * UU S t f 0) (fun j k => by`. Use `hess (hAnn t) j k` as an intermediate fact. Rewrite `this` using `[hPt, loQ_nn]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[this]`.

Use the proof step `ring)`. Simplify using `only [Matrix.of_apply, Matrix.map_apply] at h2`. Rewrite `h1` using `[h2]`. Use `h1 using 1` and compare the differences between its conclusion and the goal. Establish `hπ : (π : ℂ) ≠ 0` using `by simp [Real.pi_ne_zero]`.

Establish `hI : (I : ℂ) ≠ 0` using `I_ne_zero`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hh : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0 * UU S t f 0 * (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det) 0 t` using `fun t => by`. Conclude with `(((hF t).fun_mul (hF t)).fun_mul (hasDerivAt_det _ _ t (hdet t))).congr_deriv (by ring)`.

Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) 1 0`. Establish `e0 : UU S 0 f = f` using `by rw [UU_zero]; rfl`. Establish `e1 : UU S 1 f = fou l (ph (-(Matrix.toEuclideanCLM (𝕜` using `ℝ) (n := l) S)) (fouInv l f)) := by`. Simplify using `[UU]`. Simplify using `only [e0, e1, ofReal_zero, ofReal_one, zero_smul, add_zero, one_smul] at hc`.

Rewrite using `[sq, sq]`. Conclude with `hc`.
-/
theorem nrmUp : NrmUp l := by
  intro S hS s' f hf
  have hPt : ∀ t : ℝ, upperParabolic (nn S t * s'.1) = upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1) := fun t => upperPart_unipotent_mul S t s'.1
  have hdet : ∀ t : ℝ, (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det ≠ 0 := fun t => by
    rw [← hPt]
    exact ddNe ⟨_, mul_mem (nn_mem hS t) s'.2⟩
  have hAnn : ∀ t, Ann (nn S t * s'.1) (UU S t f) := fun t => hf.map (UU_dRho hS t)
  have hF : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0) (-(1 / 2 : ℂ) * UU S t f 0 *
      ((upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1))⁻¹ * (S.map ofReal * loQ s'.1)).trace) t := fun t => by
    have h1 := hasDerivAt_UU S f t
    rw [fou_mq_fouInv] at h1
    simp only [SchwartzMap.smul_apply, SchwartzMap.sum_apply, smul_eq_mul] at h1
    have h2 := trace_eq (hdet t) (S.map ofReal)
      (Matrix.of fun a k => (∂_{(EuclideanSpace.single a 1 : Eu l)} (∂_{(EuclideanSpace.single k 1 : Eu l)}
        (UU S t f))) 0) (-(2 * π * I) * UU S t f 0) (fun j k => by
          have := hess (hAnn t) j k
          rw [hPt, loQ_nn] at this
          simp only [Matrix.of_apply]
          rw [this]
          ring)
    simp only [Matrix.of_apply, Matrix.map_apply] at h2
    rw [h2] at h1
    convert h1 using 1
    have hπ : (π : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
    ring
  have hh : ∀ t : ℝ, HasDerivAt (fun t => UU S t f 0 * UU S t f 0 *
      (upperParabolic s'.1 + (t : ℂ) • (S.map ofReal * loQ s'.1)).det) 0 t := fun t => by
    exact (((hF t).fun_mul (hF t)).fun_mul (hasDerivAt_det _ _ t (hdet t))).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hh t).differentiableAt) (fun t => (hh t).deriv) 1 0
  have e0 : UU S 0 f = f := by rw [UU_zero]; rfl
  have e1 : UU S 1 f = fou l (ph (-(Matrix.toEuclideanCLM (𝕜 := ℝ) (n := l) S)) (fouInv l f)) := by
    simp [UU]
  simp only [e0, e1, ofReal_zero, ofReal_one, zero_smul, add_zero, one_smul] at hc
  rw [sq, sq]
  exact hc

end PositivityTheory.ThKR.Mp
