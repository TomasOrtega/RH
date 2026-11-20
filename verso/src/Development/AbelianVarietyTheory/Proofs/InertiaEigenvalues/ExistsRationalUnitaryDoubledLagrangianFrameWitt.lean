import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameOfFst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open GlobalTheory.RawLift GlobalTheory.SWLagTerms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LagWitt

open Matrix Formalism.UG

variable {K : Type} [Field K] (σ : K →+* K)

/- English proof (translation)
Unfold `cT`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem cT_sub {m p : Type} (M N : Matrix m p K) : cT σ (M - N) = cT σ M - cT σ N := by
  unfold cT; ext i j; simp

/- English proof (translation)
Unfold `cT`. Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem cT_smul {m p : Type} (c : K) (M : Matrix m p K) : cT σ (c • M) = σ c • cT σ M := by
  unfold cT; ext i j; simp

/- English proof (translation)
Unfold `cT`. Use extensionality with `i j`. Simplify using `[hσ]`.
-/
theorem cT_cT (hσ : ∀ x, σ (σ x) = x) {m p : Type} (M : Matrix m p K) : cT σ (cT σ M) = M := by
  unfold cT; ext i j; simp [hσ]

/- English proof (translation)
Apply the tactic sequence `unfold cT; ext (i | i) j <;> simp`.
-/
theorem cT_fromCols {m p q : Type} (M : Matrix m p K) (N : Matrix m q K) :
    cT σ (fromCols M N) = fromRows (cT σ M) (cT σ N) := by
  unfold cT; ext (i | i) j <;> simp

/- English proof (translation)
Apply the tactic sequence `unfold cT; ext i (j | j) <;> simp`.
-/
theorem cT_fromRows {m p q : Type} (M : Matrix p m K) (N : Matrix q m K) :
    cT σ (fromRows M N) = fromCols (cT σ M) (cT σ N) := by
  unfold cT; ext i (j | j) <;> simp

/- English proof (translation)
Apply the tactic sequence `unfold cT; ext (i | i) (j | j) <;> simp`.
-/
theorem cT_fromBlocks {m n p q : Type} (A : Matrix m p K) (B : Matrix m q K) (C : Matrix n p K) (D : Matrix n q K) :
    cT σ (fromBlocks A B C D) = fromBlocks (cT σ A) (cT σ C) (cT σ B) (cT σ D) := by
  unfold cT; ext (i | i) (j | j) <;> simp

/- English proof (translation)
Rewrite using `[cT_mul, cT_mul, cT_cT σ hσ, hJ, Matrix.mul_assoc]`.
-/
theorem cT_form (hσ : ∀ x, σ (σ x) = x) {m ι κ : Type} [Fintype m] (J : Matrix m m K) (hJ : cT σ J = J)
    (Z : Matrix m ι K) (X : Matrix m κ K) : cT σ (cT σ Z * J * X) = cT σ X * J * Z := by
  rw [cT_mul, cT_mul, cT_cT σ hσ, hJ, Matrix.mul_assoc]

/- English proof (translation)
Take `⟨X, hX⟩ : ∃ X : Matrix m ι K, cT σ Z * J * X = 1` from `⟨J⁻¹ * cT σ L, by`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, ← cT_mul, hL, cT_one]⟩`. Establish `hX' : cT σ X * J * Z = 1`. Rewrite using `[← cT_form σ hσ J hJ, hX, cT_one]`. Choose the witnesses or unpack the hypotheses as in `⟨T, hT, h2T⟩ : ∃ T : Matrix ι ι K, cT σ T = T ∧ T + T = cT σ X * J * X := by`.

Use `⟨(2 : K)⁻¹ • (cT σ X * J * X), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[cT_smul, cT_form σ hσ J hJ, map_inv₀, map_ofNat]`. Rewrite using `[← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]`. Use `⟨X - Z * T, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_sub, ← Matrix.mul_assoc, hZ, Matrix.zero_mul, sub_zero, hX]`.

Rewrite using `[cT_sub, cT_mul, hT, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]`. Establish `e1 : cT σ X * J * (Z * T) = T` using `by rw [← Matrix.mul_assoc, hX', Matrix.one_mul]`. Establish `e2 : T * cT σ Z * J * X = T`. Rewrite using `[Matrix.mul_assoc T, Matrix.mul_assoc T, hX, Matrix.mul_one]`. Establish `e3 : T * cT σ Z * J * (Z * T) = 0`.

Rewrite using `[Matrix.mul_assoc T, Matrix.mul_assoc T, ← Matrix.mul_assoc (cT σ Z * J), hZ]`. Simplify using the standard rewrite rules. Rewrite using `[e1, e2, e3, ← h2T]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_hyperbolic_complement (hσ : ∀ x, σ (σ x) = x) (h2 : (2 : K) ≠ 0) {m ι : Type} [Fintype m] [DecidableEq m]
    [Fintype ι] [DecidableEq ι] (J : Matrix m m K) (hJ : cT σ J = J) (hJu : IsUnit J.det) (Z : Matrix m ι K)
    (L : Matrix ι m K) (hL : L * Z = 1) (hZ : cT σ Z * J * Z = 0) :
    ∃ Z' : Matrix m ι K, cT σ Z * J * Z' = 1 ∧ cT σ Z' * J * Z' = 0 := by
  obtain ⟨X, hX⟩ : ∃ X : Matrix m ι K, cT σ Z * J * X = 1 := ⟨J⁻¹ * cT σ L, by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc J, Matrix.mul_nonsing_inv _ hJu, Matrix.one_mul, ← cT_mul, hL, cT_one]⟩
  have hX' : cT σ X * J * Z = 1 := by
    rw [← cT_form σ hσ J hJ, hX, cT_one]
  obtain ⟨T, hT, h2T⟩ : ∃ T : Matrix ι ι K, cT σ T = T ∧ T + T = cT σ X * J * X := by
    refine ⟨(2 : K)⁻¹ • (cT σ X * J * X), ?_, ?_⟩
    · rw [cT_smul, cT_form σ hσ J hJ, map_inv₀, map_ofNat]
    · rw [← add_smul, ← two_mul, mul_inv_cancel₀ h2, one_smul]
  refine ⟨X - Z * T, ?_, ?_⟩
  · rw [Matrix.mul_sub, ← Matrix.mul_assoc, hZ, Matrix.zero_mul, sub_zero, hX]
  · rw [cT_sub, cT_mul, hT, Matrix.sub_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
    have e1 : cT σ X * J * (Z * T) = T := by rw [← Matrix.mul_assoc, hX', Matrix.one_mul]
    have e2 : T * cT σ Z * J * X = T := by
      rw [Matrix.mul_assoc T, Matrix.mul_assoc T, hX, Matrix.mul_one]
    have e3 : T * cT σ Z * J * (Z * T) = 0 := by
      rw [Matrix.mul_assoc T, Matrix.mul_assoc T, ← Matrix.mul_assoc (cT σ Z * J), hZ]
      simp
    rw [e1, e2, e3, ← h2T]; abel

/- English proof (translation)
Establish `c : cT σ Z' * J * Z = 1` using `by rw [← cT_form σ hσ J hJ, a, cT_one]`. Rewrite using `[cT_fromCols, fromRows_mul, fromRows_mul_fromCols, h, a, b, c]`.
-/
theorem hyperbolic_fromCols (hσ : ∀ x, σ (σ x) = x) {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (hJ : cT σ J = J) (Z Z' : Matrix (ι ⊕ ι) ι K) (h : cT σ Z * J * Z = 0)
    (a : cT σ Z * J * Z' = 1) (b : cT σ Z' * J * Z' = 0) :
    cT σ (fromCols Z Z') * J * fromCols Z Z' = fromBlocks 0 1 1 0 := by
  have c : cT σ Z' * J * Z = 1 := by rw [← cT_form σ hσ J hJ, a, cT_one]
  rw [cT_fromCols, fromRows_mul, fromRows_mul_fromCols, h, a, b, c]

/- English proof (translation)
Take `⟨Z₁', a₁, b₁⟩` from `exists_hyperbolic_complement σ hσ h2 J hJ hJu Z₁ L₁ hL₁ h₁`. Take `⟨Z₂', a₂, b₂⟩` from `exists_hyperbolic_complement σ hσ h2 J hJ hJu Z₂ L₂ hL₂ h₂`. Establish `k₁` using `hyperbolic_fromCols σ hσ J hJ Z₁ Z₁' h₁ a₁ b₁`. Establish `k₂` using `hyperbolic_fromCols σ hσ J hJ Z₂ Z₂' h₂ a₂ b₂`. Establish `HH : (fromBlocks 0 1 1 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * fromBlocks 0 1 1 0 = 1`.

Rewrite using `[fromBlocks_multiply]`. Simplify using `[fromBlocks_one]`. Take `⟨Q, QP⟩ : ∃ Q, Q * fromCols Z₁ Z₁' = 1` from `⟨fromBlocks 0 1 1 0 * cT σ (fromCols Z₁ Z₁') * J, by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _) J, k₁, HH]⟩`. Establish `PQ : fromCols Z₁ Z₁' * Q = 1` using `mul_eq_one_comm.1 QP`. Use `⟨fromCols Z₂ Z₂' * Q, ?_, ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = cT σ Q * (cT σ (fromCols Z₁ Z₁') * J * fromCols Z₁ Z₁') * Q := by rw [k₁, k₂]`. Use `_ = cT σ (fromCols Z₁ Z₁' * Q) * J * (fromCols Z₁ Z₁' * Q) := by`.

Rewrite using `[cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = J := by rw [PQ, cT_one, Matrix.one_mul, Matrix.mul_one]`. Establish `e₁ : Z₁ = (fromCols Z₁ Z₁' : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * (fromRows (1 : Matrix ι ι K) (0 : Matrix ι ι K))`. Rewrite using `[fromCols_mul_fromRows]`.

Simplify using the standard rewrite rules. Establish `e₂ : Z₂ = (fromCols Z₂ Z₂' : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * (fromRows (1 : Matrix ι ι K) (0 : Matrix ι ι K))`. Rewrite using `[fromCols_mul_fromRows]`. Simplify using the standard rewrite rules. Use `conv_lhs => rw [e₁]`.

Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc Q, QP, Matrix.one_mul, ← e₂]`.
-/
theorem exists_unitary_mul_eq (hσ : ∀ x, σ (σ x) = x) (h2 : (2 : K) ≠ 0) {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (ι ⊕ ι) (ι ⊕ ι) K) (hJ : cT σ J = J) (hJu : IsUnit J.det) (Z₁ Z₂ : Matrix (ι ⊕ ι) ι K)
    (L₁ L₂ : Matrix ι (ι ⊕ ι) K) (hL₁ : L₁ * Z₁ = 1) (hL₂ : L₂ * Z₂ = 1)
    (h₁ : cT σ Z₁ * J * Z₁ = 0) (h₂ : cT σ Z₂ * J * Z₂ = 0) :
    ∃ g : Matrix (ι ⊕ ι) (ι ⊕ ι) K, cT σ g * J * g = J ∧ g * Z₁ = Z₂ := by
  obtain ⟨Z₁', a₁, b₁⟩ := exists_hyperbolic_complement σ hσ h2 J hJ hJu Z₁ L₁ hL₁ h₁
  obtain ⟨Z₂', a₂, b₂⟩ := exists_hyperbolic_complement σ hσ h2 J hJ hJu Z₂ L₂ hL₂ h₂
  have k₁ := hyperbolic_fromCols σ hσ J hJ Z₁ Z₁' h₁ a₁ b₁
  have k₂ := hyperbolic_fromCols σ hσ J hJ Z₂ Z₂' h₂ a₂ b₂
  have HH : (fromBlocks 0 1 1 0 : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * fromBlocks 0 1 1 0 = 1 := by
    rw [fromBlocks_multiply]; simp [fromBlocks_one]
  obtain ⟨Q, QP⟩ : ∃ Q, Q * fromCols Z₁ Z₁' = 1 :=
    ⟨fromBlocks 0 1 1 0 * cT σ (fromCols Z₁ Z₁') * J, by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT σ _) J, k₁, HH]⟩
  have PQ : fromCols Z₁ Z₁' * Q = 1 := mul_eq_one_comm.1 QP
  refine ⟨fromCols Z₂ Z₂' * Q, ?_, ?_⟩
  · calc cT σ (fromCols Z₂ Z₂' * Q) * J * (fromCols Z₂ Z₂' * Q)
          = cT σ Q * (cT σ (fromCols Z₂ Z₂') * J * fromCols Z₂ Z₂') * Q := by
            rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ Q * (cT σ (fromCols Z₁ Z₁') * J * fromCols Z₁ Z₁') * Q := by rw [k₁, k₂]
      _ = cT σ (fromCols Z₁ Z₁' * Q) * J * (fromCols Z₁ Z₁' * Q) := by
            rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = J := by rw [PQ, cT_one, Matrix.one_mul, Matrix.mul_one]
  · have e₁ : Z₁ = (fromCols Z₁ Z₁' : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * (fromRows (1 : Matrix ι ι K) (0 : Matrix ι ι K)) := by
      rw [fromCols_mul_fromRows]; simp
    have e₂ : Z₂ = (fromCols Z₂ Z₂' : Matrix (ι ⊕ ι) (ι ⊕ ι) K) * (fromRows (1 : Matrix ι ι K) (0 : Matrix ι ι K)) := by
      rw [fromCols_mul_fromRows]; simp
    conv_lhs => rw [e₁]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q, QP, Matrix.one_mul, ← e₂]

end GlobalTheory.LagWitt

namespace GlobalTheory.SWLagTerms

open Matrix Formalism.UG GlobalTheory.LagWitt

variable {D : D7}

/- English proof (translation)
Simplify using `only [cT, Matrix.mul_apply, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum, Pi.star_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Both sides reduce to the same expression.
-/
theorem cT_mul_mul_apply {n ι : Type} [Fintype n] (M : Matrix n n D.host.E) (X : Matrix n ι D.host.E) (j k : ι) :
    (cT (D.sp.cm.sig : D.host.E →+* D.host.E) X * M * X) j k = star (fun i => X i j) ⬝ᵥ M *ᵥ (fun i => X i k) := by
  simp only [cT, Matrix.mul_apply, dotProduct, mulVec, transpose_apply, map_apply, Finset.sum_mul, Finset.mul_sum,
    Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_assoc]; rfl

/- English proof (translation)
Establish `hf : LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2) = Fintype.linearCombination D.host.E (fun j => ((fun a => C.1 a j), (fun a => C.2 a j)))`. Apply the tactic sequence `refine LinearMap.ext fun v => Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;>`. Simplify using `[Fintype.linearCombination_apply, mulVec, dotProduct, Finset.sum_apply, mul_comm, Prod.fst_sum, Prod.snd_sum]`. Establish `hr : LinearMap.range (LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)) = Y.1`. Rewrite using `[hf, Fintype.range_linearCombination]`.

Conclude with `h`. Use `LinearMap.finrank_range_add_finrank_ker (LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2))` as an intermediate fact. Rewrite `this` using `[hr, Y.2.1, Module.finrank_fin_fun]`. Conclude with `Submodule.finrank_eq_zero.1 (by omega)`.
-/
theorem frame_ker_eq_bot (W : HSp D) (Y : Lag W)
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    (LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)).ker = ⊥ := by
  have hf : LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2) =
      Fintype.linearCombination D.host.E (fun j => ((fun a => C.1 a j), (fun a => C.2 a j))) := by
    refine LinearMap.ext fun v => Prod.ext (funext fun a => ?_) (funext fun a => ?_) <;>
      simp [Fintype.linearCombination_apply, mulVec, dotProduct, Finset.sum_apply, mul_comm, Prod.fst_sum, Prod.snd_sum]
  have hr : LinearMap.range (LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2)) = Y.1 := by
    rw [hf, Fintype.range_linearCombination]; exact h
  have := LinearMap.finrank_range_add_finrank_ker (LinearMap.prod (Matrix.mulVecLin C.1) (Matrix.mulVecLin C.2))
  rw [hr, Y.2.1, Module.finrank_fin_fun] at this
  exact Submodule.finrank_eq_zero.1 (by omega)

end GlobalTheory.SWLagTerms

namespace GlobalTheory.SWLagTerms

open Matrix Formalism.UG GlobalTheory.LagWitt

variable {D : D7}

/- English proof (translation)
Establish `hk` using `frame_ker_eq_bot W Y C h`. Establish `hker : (Matrix.mulVecLin (fromRows C.2 C.1)).ker = ⊥`. Rewrite `hk`, the goal using `[LinearMap.ker_eq_bot']`. Introduce `v hv`. Apply `hk v` to reduce the goal to its premises.

Use `Prod.ext (funext fun a => ?_) (funext fun a => ?_)` and prove the remaining obligations. Use `congrFun hv (Sum.inr a)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct]`. Use `congrFun hv (Sum.inl a)` as an intermediate fact. Simplify `this` using `[mulVec, dotProduct]`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective _ hker`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Use `congrArg LinearMap.toMatrix' hg` as an intermediate fact. Rewrite `this` using `[LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']`. Then use the resulting hypothesis.
-/
theorem exists_left_inv_fromRows (W : HSp D) (Y : Lag W)
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    ∃ L : Matrix (Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E, L * fromRows C.2 C.1 = 1 := by
  have hk := frame_ker_eq_bot W Y C h
  have hker : (Matrix.mulVecLin (fromRows C.2 C.1)).ker = ⊥ := by
    rw [LinearMap.ker_eq_bot'] at hk ⊢
    intro v hv
    apply hk v
    refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
    · have := congrFun hv (Sum.inr a)
      simpa [mulVec, dotProduct] using this
    · have := congrFun hv (Sum.inl a)
      simpa [mulVec, dotProduct] using this
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective _ hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have := congrArg LinearMap.toMatrix' hg
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin'] at this

end GlobalTheory.SWLagTerms

namespace GlobalTheory.SWLagTerms

open Matrix Formalism.UG GlobalTheory.LagWitt

variable {D : D7}

/- English proof (translation)
Establish `hG` using `(GlobalTheory.Doubling.isHermND_gram W).1`. Apply the tactic sequence `unfold cT; ext (i | i) (j | j) <;> simp [hG]`.
-/
theorem dbl_herm (W : HSp D) :
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) (fromBlocks W.gram 0 0 (-W.gram)) = fromBlocks W.gram 0 0 (-W.gram) := by
  have hG := (GlobalTheory.Doubling.isHermND_gram W).1
  unfold cT; ext (i | i) (j | j) <;> simp [hG]

/- English proof (translation)
Establish `hG` using `(GlobalTheory.Doubling.isHermND_gram W).2`. Rewrite using `[det_fromBlocks_zero₂₁, det_neg, isUnit_iff_ne_zero]`. Simplify using `[hG]`.
-/
theorem dbl_det (W : HSp D) : IsUnit (fromBlocks W.gram 0 0 (-W.gram) : Matrix (Fin W.rank ⊕ Fin W.rank) _ D.host.E).det := by
  have hG := (GlobalTheory.Doubling.isHermND_gram W).2
  rw [det_fromBlocks_zero₂₁, det_neg, isUnit_iff_ne_zero]
  simp [hG]

/- English proof (translation)
Establish `hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x` using `fun x => star_star x`. Take `⟨L₁, hL₁⟩` from `exists_left_inv_fromRows W Y C h`. Use `exists_unitary_mul_eq _ hσ two_ne_zero _ (dbl_herm W) (dbl_det W) _ _ L₁ (fromCols 1 0) hL₁ (by rw [fromCols_mul_fromRows]; simp) ?_ ?_` and prove the remaining obligations. Establish `hY` using `Y.2.2`. Use extensionality with `j k`.

Rewrite using `[cT_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]`. Establish `e1` using `cT_mul_mul_apply W.gram C.1 j k`. Establish `e2` using `cT_mul_mul_apply W.gram C.2 j k`. Establish `hm` using `hY (((fun a => C.1 a j), (fun a => C.2 a j))) (h ▸ Submodule.subset_span ⟨j, rfl⟩) (((fun a => C.1 a k), (fun a => C.2 a k))) (h ▸ Submodule.subset_span ⟨k, rfl⟩)`. Simplify using `only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.add_apply, Matrix.neg_apply, Matrix.zero_apply] at *`.

Rewrite using `[e1, e2, hm]`. Simplify using the standard rewrite rules. Rewrite using `[cT_fromRows, cT_one, fromCols_mul_fromBlocks, fromCols_mul_fromRows]`. Simplify using the standard rewrite rules.
-/
theorem exists_unitary_frame (W : HSp D) (Y : Lag W)
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : IsLagFrame W Y C) :
    ∃ g : Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E,
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) g * fromBlocks W.gram 0 0 (-W.gram) * g = fromBlocks W.gram 0 0 (-W.gram) ∧
      g * fromRows C.2 C.1 = fromRows 1 1 := by
  have hσ : ∀ x : D.host.E, (D.sp.cm.sig : D.host.E →+* D.host.E) ((D.sp.cm.sig : D.host.E →+* D.host.E) x) = x :=
    fun x => star_star x
  obtain ⟨L₁, hL₁⟩ := exists_left_inv_fromRows W Y C h
  refine exists_unitary_mul_eq _ hσ two_ne_zero _ (dbl_herm W) (dbl_det W) _ _ L₁ (fromCols 1 0) hL₁
    (by rw [fromCols_mul_fromRows]; simp) ?_ ?_
  · have hY := Y.2.2
    ext j k
    rw [cT_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
    have e1 := cT_mul_mul_apply W.gram C.1 j k
    have e2 := cT_mul_mul_apply W.gram C.2 j k
    have hm := hY (((fun a => C.1 a j), (fun a => C.2 a j))) (h ▸ Submodule.subset_span ⟨j, rfl⟩)
      (((fun a => C.1 a k), (fun a => C.2 a k))) (h ▸ Submodule.subset_span ⟨k, rfl⟩)
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg, Matrix.neg_mul, Matrix.add_apply, Matrix.neg_apply,
      Matrix.zero_apply] at *
    rw [e1, e2, hm]; simp
  · rw [cT_fromRows, cT_one, fromCols_mul_fromBlocks, fromCols_mul_fromRows]; simp

end GlobalTheory.SWLagTerms

namespace GlobalTheory.SWLagTerms

open Matrix Formalism.UG GlobalTheory.LagWitt

variable {D : D7}

/- English proof (translation)
Simplify using `[blk, submatrix_submatrix]`.
-/
theorem blk_submatrix (W : HSp D) (g : Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E) :
    blk W (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = g := by
  simp [blk, submatrix_submatrix]

/- English proof (translation)
Establish `hG` using `(GlobalTheory.Doubling.isHermND_gram W).2`. Establish `key : fromBlocks W.gram 0 0 (-W.gram) * fromRows C.2 C.1 = cT (D.sp.cm.sig : D.host.E →+* D.host.E) g * fromBlocks W.gram 0 0 (-W.gram) * (fromRows (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) 1 : Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank) D.host.E)`. Rewrite using `[← hg, ← Matrix.mul_assoc]`. Use `conv_lhs => rw [← hu]`. Rewrite using `[frameOf, blk_submatrix]`.

Rewrite `key` using `[← fromBlocks_toBlocks g, cT_fromBlocks, fromBlocks_multiply, fromBlocks_mul_fromRows, fromBlocks_mul_fromRows]`. Simplify using `only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at key`. Take `⟨k1, k2⟩` from `fromRows_inj key`. Establish `a1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₂₂ - g.toBlocks₁₂) * W.gram = W.gram * C.1`. Rewrite using `[cT_sub, Matrix.sub_mul, ← neg_neg (W.gram * C.1), k2]`.

Normalize the expressions using the abelian group laws. Establish `a2 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₁₁ - g.toBlocks₂₁) * W.gram = W.gram * C.2`. Rewrite using `[cT_sub, Matrix.sub_mul, k1, sub_eq_add_neg]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W.gram)⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₂₂ - g.toBlocks₁₂) * W.gram = C.1`.

Rewrite using `[Matrix.mul_assoc, a1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul]`. Express the relevant statement in the definitionally equal form `(W.gram)⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₁₁ - g.toBlocks₂₁) * W.gram = C.2`. Rewrite using `[Matrix.mul_assoc, a2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul]`.
-/
theorem frameOf_submatrix (W : HSp D)
    (C : Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (g : Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank ⊕ Fin W.rank) D.host.E)
    (hu : cT (D.sp.cm.sig : D.host.E →+* D.host.E) g * fromBlocks W.gram 0 0 (-W.gram) * g = fromBlocks W.gram 0 0 (-W.gram))
    (hg : g * fromRows C.2 C.1 = fromRows 1 1) :
    frameOf W (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = C := by
  have hG := (GlobalTheory.Doubling.isHermND_gram W).2
  have key : fromBlocks W.gram 0 0 (-W.gram) * fromRows C.2 C.1 =
      cT (D.sp.cm.sig : D.host.E →+* D.host.E) g * fromBlocks W.gram 0 0 (-W.gram) *
        (fromRows (1 : Matrix (Fin W.rank) (Fin W.rank) D.host.E) 1 : Matrix (Fin W.rank ⊕ Fin W.rank) (Fin W.rank) D.host.E) := by
    rw [← hg, ← Matrix.mul_assoc]; conv_lhs => rw [← hu]
  rw [frameOf, blk_submatrix]
  rw [← fromBlocks_toBlocks g, cT_fromBlocks, fromBlocks_multiply, fromBlocks_mul_fromRows,
    fromBlocks_mul_fromRows] at key
  simp only [toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₁, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul] at key
  obtain ⟨k1, k2⟩ := fromRows_inj key
  have a1 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₂₂ - g.toBlocks₁₂) * W.gram = W.gram * C.1 := by
    rw [cT_sub, Matrix.sub_mul, ← neg_neg (W.gram * C.1), k2]; abel
  have a2 : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₁₁ - g.toBlocks₂₁) * W.gram = W.gram * C.2 := by
    rw [cT_sub, Matrix.sub_mul, k1, sub_eq_add_neg]
  refine Prod.ext ?_ ?_
  · change (W.gram)⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₂₂ - g.toBlocks₁₂) * W.gram = C.1
    rw [Matrix.mul_assoc, a1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul]
  · change (W.gram)⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.toBlocks₁₁ - g.toBlocks₂₁) * W.gram = C.2
    rw [Matrix.mul_assoc, a2, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hG), Matrix.one_mul]

end GlobalTheory.SWLagTerms

namespace GlobalTheory.SWLagTerms

open Matrix Formalism.UG GlobalTheory.LagWitt

/- English proof (translation)
Introduce `D W Y`. Take `⟨C, hC⟩` from `exists_lagFrame W Y`. Take `⟨g, hu, hg⟩` from `exists_unitary_frame W Y C hC`. Establish `hJ : (GlobalTheory.Doubling.dblSp W).gram = (fromBlocks W.gram 0 0 (-W.gram)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm`. Rewrite using `[GlobalTheory.Doubling.gram_hdbl]`.

Both sides reduce to the same expression. Establish `hu₀ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) * (GlobalTheory.Doubling.dblSp W).gram * g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (GlobalTheory.Doubling.dblSp W).gram`. Establish `e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) g).submatrix finSumFinEquiv.symm finSumFinEquiv.symm` using `rfl`. Rewrite using `[hJ, e, submatrix_mul_equiv, submatrix_mul_equiv, hu]`. Establish `hdet : IsUnit (GlobalTheory.Doubling.dblSp W).gram.det`.

Rewrite using `[hJ, det_submatrix_equiv_self]`. Conclude with `dbl_det W`. Establish `hQ : ((GlobalTheory.Doubling.dblSp W).gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) * (GlobalTheory.Doubling.dblSp W).gram) * g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _), hu₀, Matrix.nonsing_inv_mul _ hdet]`. Set `u : GL (Fin (W.rank + W.rank)) D.host.E` to `⟨_, _, mul_eq_one_comm.1 hQ, hQ⟩`.

Establish `hu' : u ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.Doubling.dblSp W).gram` using `hu₀`. Establish `hmem : bc (inclR (F` using `D.host.F) (E := D.host.E) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.Doubling.dblSp W).gram := by show cT _ _ * _ * _ = _`. Establish `e1 : (bc (inclR (F` using `D.host.F) (E := D.host.E) (AF D.host.F)) u).val = (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := rfl`. Establish `e2 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) ((g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (inclR (F` using `D.host.F) (E := D.host.E) (AF D.host.F))) = (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := by`. Unfold `cT`.

Use extensionality with `i j`. Simplify using `[Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]`. Rewrite using `[e1, e2, JR, ← Matrix.map_mul, ← Matrix.map_mul, hu₀]`. Set `γ : GA D (GlobalTheory.Doubling.dblSp W)` to `(⟨bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) u, hmem⟩ : HR (AF D.host.F) D.sp.cm.sig _)`. Establish `hmt : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (incA D)` using `rfl`.

Use `⟨γ, ?_, g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, hmt, ?_⟩` and prove the remaining obligations. Conclude with `Subgroup.mem_subgroupOf.2 ⟨u, hu', rfl⟩`. Rewrite using `[frameOf_submatrix W C g hu hg]`. Conclude with `hC`.
-/
theorem exists_rat_unitary_lagFrame : ∀ (D : D7) (W : HSp D) (Y : Lag W), ∃ γ : GA D (GlobalTheory.Doubling.dblSp W),
    γ ∈ GQ (GlobalTheory.Doubling.dblSp W) ∧ ∃ (g₀ : Matrix (Fin (W.rank + W.rank)) (Fin (W.rank + W.rank)) D.host.E),
      Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ = g₀.map (incA D) ∧ IsLagFrame W Y (frameOf W g₀) := by
  intro D W Y
  obtain ⟨C, hC⟩ := exists_lagFrame W Y
  obtain ⟨g, hu, hg⟩ := exists_unitary_frame W Y C hC
  have hJ : (GlobalTheory.Doubling.dblSp W).gram =
      (fromBlocks W.gram 0 0 (-W.gram)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [GlobalTheory.Doubling.gram_hdbl]; rfl
  have hu₀ : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) *
      (GlobalTheory.Doubling.dblSp W).gram * g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = (GlobalTheory.Doubling.dblSp W).gram := by
    have e : cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) g).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl
    rw [hJ, e, submatrix_mul_equiv, submatrix_mul_equiv, hu]
  have hdet : IsUnit (GlobalTheory.Doubling.dblSp W).gram.det := by
    rw [hJ, det_submatrix_equiv_self]; exact dbl_det W
  have hQ : ((GlobalTheory.Doubling.dblSp W).gram⁻¹ * cT (D.sp.cm.sig : D.host.E →+* D.host.E)
      (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) * (GlobalTheory.Doubling.dblSp W).gram) *
      g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ _), hu₀, Matrix.nonsing_inv_mul _ hdet]
  let u : GL (Fin (W.rank + W.rank)) D.host.E := ⟨_, _, mul_eq_one_comm.1 hQ, hQ⟩
  have hu' : u ∈ UJ (D.sp.cm.sig : D.host.E →+* D.host.E) (GlobalTheory.Doubling.dblSp W).gram := hu₀
  have hmem : bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) u ∈ HR (AF D.host.F) D.sp.cm.sig (GlobalTheory.Doubling.dblSp W).gram := by
    show cT _ _ * _ * _ = _
    have e1 : (bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) u).val =
        (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := rfl
    have e2 : cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig)
        ((g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F))) =
        (cT (D.sp.cm.sig : D.host.E →+* D.host.E) (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)).map
          (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) := by
      unfold cT; ext i j; simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, inclR]
    rw [e1, e2, JR, ← Matrix.map_mul, ← Matrix.map_mul, hu₀]
  let γ : GA D (GlobalTheory.Doubling.dblSp W) := (⟨bc (inclR (F := D.host.F) (E := D.host.E) (AF D.host.F)) u, hmem⟩ : HR (AF D.host.F) D.sp.cm.sig _)
  have hmt : Formalism.L2.Theta.mt (GlobalTheory.Doubling.dblSp W) γ =
      (g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm).map (incA D) := rfl
  refine ⟨γ, ?_, g.submatrix finSumFinEquiv.symm finSumFinEquiv.symm, hmt, ?_⟩
  · exact Subgroup.mem_subgroupOf.2 ⟨u, hu', rfl⟩
  · rw [frameOf_submatrix W C g hu hg]; exact hC

end GlobalTheory.SWLagTerms

end
