import Formalism.HarderNarasimhan.StatementPl
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar

open Module NumberField

noncomputable section

namespace Formalism.HN

namespace PlaceOperatorNorms

variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
  {W κ : Type} [AddCommGroup W] [Module K W] [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]`.
-/
theorem realize_apply0 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 0) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).re := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]`.
-/
theorem realize_apply1 (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (v : InfinitePlace K) (i : ι) :
    (Formalism.HermitianLatticesTheory.realize b X x) (v, i, 1) = (Formalism.HermitianLatticesTheory.fcoord b X v x i).im := by
  simp [Formalism.HermitianLatticesTheory.realize, Formalism.HermitianLatticesTheory.realizeRaw]

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]`. Simplify using `only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]`. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Fintype.sum_prod_type]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_two, realize_apply0, realize_apply1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_two, realize_apply0, realize_apply1, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]`.
-/
theorem cnorm_eq (u : κ → ℂ) : Formalism.HermitianLatticesTheory.cnorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℂ κ)‖ := by
  simp [Formalism.HermitianLatticesTheory.cnorm, EuclideanSpace.norm_eq]

/- English proof (translation)
Establish `hv : Formalism.HermitianLatticesTheory.vecAt b' v (φ x) = ((LinearMap.toMatrix b b' φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x)`. Use function extensionality and compare the values at `i`. Simplify using `only [Formalism.HermitianLatticesTheory.vecAt]`. Rewrite using `[← LinearMap.toMatrix_mulVec_repr b b' φ x]`. Use `first`.

Consider the case `simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]`. Consider the case `simp [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]`. Simplify using `only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]`.
-/
theorem fcoord_map (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (φ : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.fcoord b' X' v (φ x) =
      ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v).mulVec
        (Formalism.HermitianLatticesTheory.fcoord b X v x) := by
  have hv : Formalism.HermitianLatticesTheory.vecAt b' v (φ x) =
      ((LinearMap.toMatrix b b' φ).map v.embedding).mulVec (Formalism.HermitianLatticesTheory.vecAt b v x) := by
    funext i
    simp only [Formalism.HermitianLatticesTheory.vecAt]
    rw [← LinearMap.toMatrix_mulVec_repr b b' φ x]
    first
      | simp [Matrix.mulVec, dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]
      | simp [Matrix.mulVec, Matrix.dotProduct, map_sum, map_mul, Formalism.HermitianLatticesTheory.vecAt]
  simp only [Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v),
    Matrix.mul_one]

/- English proof (translation)
Rewrite using `[Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.normAt, fcoord_map b X b' X' hX v φ x, cnorm_eq, cnorm_eq, opNormAt]`. Use `(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))).le_opNorm (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`.

Consider the case `simp [Matrix.toEuclideanLin_apply]`. Consider the case `(congr 1; simp [Matrix.toEuclideanLin_apply])`.
-/
theorem normAt_map_le (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (φ : V →ₗ[K] W) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b' X' v (φ x) ≤ opNormAt b X b' X' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := by
  rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.normAt, fcoord_map b X b' X' hX v φ x, cnorm_eq, cnorm_eq, opNormAt]
  have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
    ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v))).le_opNorm
      (WithLp.toLp 2 (Formalism.HermitianLatticesTheory.fcoord b X v x))
  convert this using 1
  all_goals first
    | rfl
    | simp [Matrix.toEuclideanLin_apply]
    | (congr 1; simp [Matrix.toEuclideanLin_apply])

/- English proof (translation)
Establish `hc0 : ((c v : ℂ)) ≠ 0` using `by exact_mod_cast (hc v).ne'`. Establish `hi : ((c v : ℂ) • X' v)⁻¹ = ((c v : ℂ))⁻¹ • (X' v)⁻¹`. Apply `Matrix.inv_eq_left_inv` to reduce the goal to its premises. Rewrite using `[Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul, Matrix.nonsing_inv_mul _ (hX' v)]`. Simplify using `only [opNormAt, hi, Matrix.smul_mul, map_smul, norm_smul]`.

Use `first`. Consider the case `rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hc v).le]`. Consider the case `simp [norm_inv, abs_of_pos (hc v)]`.
-/
theorem opNormAt_smul (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX' : ∀ v, IsUnit (X' v).det) (c : InfinitePlace K → ℝ)
    (hc : ∀ v, 0 < c v) (v : InfinitePlace K) (φ : V →ₗ[K] W) :
    opNormAt b X b' (fun w => ((c w : ℂ)) • X' w) v φ = (c v)⁻¹ * opNormAt b X b' X' v φ := by
  have hc0 : ((c v : ℂ)) ≠ 0 := by exact_mod_cast (hc v).ne'
  have hi : ((c v : ℂ) • X' v)⁻¹ = ((c v : ℂ))⁻¹ • (X' v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hc0, one_smul,
      Matrix.nonsing_inv_mul _ (hX' v)]
  simp only [opNormAt, hi, Matrix.smul_mul, map_smul, norm_smul]
  first
    | rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (hc v).le]
    | simp [norm_inv, abs_of_pos (hc v)]

/- English proof (translation)
Rewrite using `[opNormAt, norm_pos_iff]`. Introduce `h0`. Apply `hφ` to reduce the goal to its premises. Establish `hA` using `(Matrix.toEuclideanLin.map_eq_zero_iff).mp ((LinearMap.toContinuousLinearMap.map_eq_zero_iff).mp h0)`. Establish `hΦ : (LinearMap.toMatrix b b' φ).map v.embedding = 0`.

Establish `e : (LinearMap.toMatrix b b' φ).map v.embedding = X' v * ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) * (X v)⁻¹`. Simplify using `only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul]`. Rewrite using `[e, hA, Matrix.mul_zero, Matrix.zero_mul]`. Establish `hM : LinearMap.toMatrix b b' φ = 0`.

Use extensionality with `i j`. Use `congrFun (congrFun hΦ i) j` as an intermediate fact. Simplify using `using this`. Conclude with `(LinearMap.toMatrix b b').map_eq_zero_iff.mp hM`.
-/
theorem opNormAt_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (b' : Basis κ K W)
    (X' : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (hX' : ∀ v, IsUnit (X' v).det) (v : InfinitePlace K) (φ : V →ₗ[K] W) (hφ : φ ≠ 0) :
    0 < opNormAt b X b' X' v φ := by
  rw [opNormAt, norm_pos_iff]
  intro h0
  apply hφ
  have hA := (Matrix.toEuclideanLin.map_eq_zero_iff).mp
    ((LinearMap.toContinuousLinearMap.map_eq_zero_iff).mp h0)
  have hΦ : (LinearMap.toMatrix b b' φ).map v.embedding = 0 := by
    have e : (LinearMap.toMatrix b b' φ).map v.embedding =
        X' v * ((X' v)⁻¹ * (LinearMap.toMatrix b b' φ).map v.embedding * X v) * (X v)⁻¹ := by
      simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX v), Matrix.mul_one]
      rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (hX' v), Matrix.one_mul]
    rw [e, hA, Matrix.mul_zero, Matrix.zero_mul]
  have hM : LinearMap.toMatrix b b' φ = 0 := by
    ext i j
    have := congrFun (congrFun hΦ i) j
    simpa using this
  exact (LinearMap.toMatrix b b').map_eq_zero_iff.mp hM

end PlaceOperatorNorms

open PlaceOperatorNorms in
/- English proof (translation)
Introduce `K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA hφA`. Establish `hφ : φ ≠ 0`. Introduce and unpack `rfl`. Apply `hφA` to reduce the goal to its premises. Rewrite using `[LinearMap.restrictScalars_zero, Submodule.map_zero]`.

Establish `hpos : ∀ v, 0 < opNormAt b X b' X' v φ` using `fun v => opNormAt_pos b X b' X' hX hX' v φ hφ`. Establish `hf : (nPl K : ℝ) ≠ 0`. Unfold `nPl`. Conclude with `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Take `⟨s, hs⟩ : ∃ s : ℝ, s = htMap b X b' X' φ / 2` from `⟨_, rfl⟩`.

Establish `hs' : s = (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ)`. Rewrite using `[hs, htMap, Finset.sum_congr rfl (fun v _ => Real.log_pow (opNormAt b X b' X' v φ) 2), ← Finset.mul_sum]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨c, hc_def⟩ : ∃ c : InfinitePlace K → ℝ, c = fun v => opNormAt b X b' X' v φ * Real.exp (-s)` from `⟨_, rfl⟩`.

Establish `hc : ∀ v, 0 < c v` using `fun v => by`. Rewrite using `[hc_def]`. Conclude with `mul_pos (hpos v) (Real.exp_pos _)`. Establish `ht0 : (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) = 0`. Establish `hl : ∀ v, Real.log (c v) = Real.log (opNormAt b X b' X' v φ) - s` using `fun v => by`.

Rewrite using `[hc_def]`. Simplify using `only`. Rewrite using `[Real.log_mul (hpos v).ne' (Real.exp_pos _).ne', Real.log_exp]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`.

Rewrite using `[mul_sub, ← hs']`. Establish `hfs : (1 / (nPl K : ℝ)) * ((Fintype.card (InfinitePlace K) : ℝ) * s) = s`. Unfold `nPl at hf ⊢`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hfs, sub_self]`.

Take `⟨X'', hX''⟩ : ∃ X'' : InfinitePlace K → Matrix κ κ ℂ, X'' = fun v => ((c v : ℂ)) • X' v` from `⟨_, rfl⟩`. Establish `hdet'' : ∀ v, IsUnit (X'' v).det` using `fun v => by`. Rewrite using `[hX'']`. Simplify using `only`. Rewrite using `[Matrix.det_smul]`.

Conclude with `((Complex.ofReal_ne_zero.mpr (hc v).ne').isUnit.pow _).mul (hX' v)`. Establish `htw : ∀ N : Submodule (𝓞 K) W, N.FG → N ≠ ⊥ → muMax (Formalism.HermitianLatticesTheory.realize b' X'') N = muMax (Formalism.HermitianLatticesTheory.realize b' X') N ∧ muMin (Formalism.HermitianLatticesTheory.realize b' X'') N = muMin (Formalism.HermitianLatticesTheory.realize b' …`. Introduce `N hN hN0`. Use `(h1 K W κ b' X' c hX' hc N hN).2.1 hN0` as an intermediate fact. Rewrite `this` using `[ht0, add_zero, add_zero]`.

Rewrite using `[hX'']`. Conclude with `this`. Establish `hC : 0 < Real.exp s` using `Real.exp_pos s`. Establish `hbound : ∀ x : V, ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ≤ Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖`. Introduce `x`.

Establish `hpl : ∀ v, Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x) ≤ Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x`. Introduce `v`. Establish `hop : opNormAt b X b' X'' v φ = Real.exp s`. Rewrite using `[hX'', opNormAt_smul b X b' X' hX' c hc v φ, hc_def]`. Simplify using `only`.

Rewrite using `[mul_inv, Real.exp_neg, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hpos v).ne', one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hsq : ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ^ 2 ≤ (Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2`. Rewrite using `[mul_pow, norm_sq_realize, norm_sq_realize, Finset.mul_sum]`. Use `Finset.sum_le_sum fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_pow]`. Conclude with `pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpl v) 2`. Conclude with `(pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq`. Establish `hAlat` using `(h2 K V ι b X hX A hA).1`. Establish `hA0 : A ≠ ⊥`.

Introduce and unpack `rfl`. Apply `hφA` to reduce the goal to its premises. Conclude with `Submodule.map_bot _`. Establish `key : ∀ M : Submodule (𝓞 K) W, M.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ M → (muMin (Formalism.HermitianLatticesTheory.realize b X) A - s ≤ muMin (Formalism.HermitianLatticesTheory.realize b' X'') (A.map (φ.restrictScalars (𝓞 K))) ∧ muMin (Formalism.HermitianLatticesTheory.realize …`. Introduce `M hM hAM`.

Establish `hMlat` using `(h2 K W κ b' X'' hdet'' M hM).1`. Establish `hmem : ∀ x : A, (φ.restrictScalars (𝓞 K)).domRestrict A x ∈ M` using `fun x => hAM (Submodule.mem_map_of_mem x.2)`. Set `ψ : A →ₗ[𝓞 K] M` to `LinearMap.codRestrict M ((φ.restrictScalars (𝓞 K)).domRestrict A) hmem`. Establish `hψ : ∀ x : A, ((ψ x : M) : W) = φ x` using `fun x => rfl`. Establish `hS` using `h3 (𝓞 K) V W _ _ (Formalism.HermitianLatticesTheory.realize b X) (Formalism.HermitianLatticesTheory.realize b' X'') A M hAlat hMlat ψ (Real.exp s) hC (fun x => by rw [hψ]; exact hbound x)`.

Rewrite `hS` using `[Real.log_exp]`. Establish `hrange : (LinearMap.range ψ).map M.subtype = A.map (φ.restrictScalars (𝓞 K))`. Use extensionality with `y`. Simplify using `only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, ⟨x, rfl⟩, rfl⟩`. Conclude with `⟨x, x.2, rfl⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩`. Establish `hψ0 : ψ ≠ 0`.

Take `⟨y, hy, hy0⟩` from `(Submodule.ne_bot_iff _).mp hφA`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`. Introduce `h`. Apply `hy0` to reduce the goal to its premises. Use `congrArg (fun g : A →ₗ[𝓞 K] M => ((g ⟨x, hx⟩ : M) : W)) h` as an intermediate fact.

Simplify `this` using `[hψ]`. Use `⟨?_, fun hinj => hS.2 ?_ hA0⟩` and prove the remaining obligations. Use `(hS.1 hψ0).1` as an intermediate fact. Rewrite `this` using `[hrange]`. Conclude with `⟨this, (hS.1 hψ0).2⟩`.

Introduce `x y hxy`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `hinj x.2 y.2` to reduce the goal to its premises. Use `congrArg (fun z : M => (z : W)) hxy` as an intermediate fact. Simplify `this` using `[hψ]`.

Establish `hφA_fg : (A.map (φ.restrictScalars (𝓞 K))).FG` using `hA.map _`. Take `⟨⟨k1, -⟩, -⟩` from `key _ hφA_fg le_rfl`. Establish `htφA` using `htw _ hφA_fg hφA`. Rewrite `k1` using `[htφA.2]`. Use `⟨?_, fun B hB hAB => ?_⟩` and prove the remaining obligations.

Unfold `muMinDef`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hB0 : B ≠ ⊥` using `fun h => hφA (le_bot_iff.mp (h ▸ hAB))`. Take `⟨⟨-, k2⟩, k3⟩` from `key B hB hAB`. Establish `htB` using `htw B hB hB0`.

Rewrite `k2`, `k3` using `[htB.1]`. Use `⟨?_, fun hinj => ?_⟩` and prove the remaining obligations. Unfold `muMinDef muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion. Use `k3 hinj` as an intermediate fact.

Unfold `muMaxDef`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem slopeIneqMean_of (h1 : Twist) (h2 : PlLat) (h3 : SlopeIneq.{0, 0, 0, 0, 0}) :
    SlopeIneqMean := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A hA hφA
  have hφ : φ ≠ 0 := by
    rintro rfl
    apply hφA
    rw [LinearMap.restrictScalars_zero, Submodule.map_zero]
  have hpos : ∀ v, 0 < opNormAt b X b' X' v φ := fun v => opNormAt_pos b X b' X' hX hX' v φ hφ
  have hf : (nPl K : ℝ) ≠ 0 := by
    unfold nPl
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = htMap b X b' X' φ / 2 := ⟨_, rfl⟩
  have hs' : s = (1 / (nPl K : ℝ)) * ∑ v, Real.log (opNormAt b X b' X' v φ) := by
    rw [hs, htMap, Finset.sum_congr rfl (fun v _ => Real.log_pow (opNormAt b X b' X' v φ) 2),
      ← Finset.mul_sum]
    push_cast
    ring
  obtain ⟨c, hc_def⟩ : ∃ c : InfinitePlace K → ℝ,
      c = fun v => opNormAt b X b' X' v φ * Real.exp (-s) := ⟨_, rfl⟩
  have hc : ∀ v, 0 < c v := fun v => by
    rw [hc_def]
    exact mul_pos (hpos v) (Real.exp_pos _)
  have ht0 : (1 / (nPl K : ℝ)) * ∑ v, Real.log (c v) = 0 := by
    have hl : ∀ v, Real.log (c v) = Real.log (opNormAt b X b' X' v φ) - s := fun v => by
      rw [hc_def]
      dsimp only
      rw [Real.log_mul (hpos v).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    simp only [hl, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_sub, ← hs']
    have hfs : (1 / (nPl K : ℝ)) * ((Fintype.card (InfinitePlace K) : ℝ) * s) = s := by
      unfold nPl at hf ⊢
      field_simp
    rw [hfs, sub_self]
  obtain ⟨X'', hX''⟩ : ∃ X'' : InfinitePlace K → Matrix κ κ ℂ,
      X'' = fun v => ((c v : ℂ)) • X' v := ⟨_, rfl⟩
  have hdet'' : ∀ v, IsUnit (X'' v).det := fun v => by
    rw [hX'']
    dsimp only
    rw [Matrix.det_smul]
    exact ((Complex.ofReal_ne_zero.mpr (hc v).ne').isUnit.pow _).mul (hX' v)
  have htw : ∀ N : Submodule (𝓞 K) W, N.FG → N ≠ ⊥ →
      muMax (Formalism.HermitianLatticesTheory.realize b' X'') N = muMax (Formalism.HermitianLatticesTheory.realize b' X') N ∧
      muMin (Formalism.HermitianLatticesTheory.realize b' X'') N = muMin (Formalism.HermitianLatticesTheory.realize b' X') N := by
    intro N hN hN0
    have := (h1 K W κ b' X' c hX' hc N hN).2.1 hN0
    rw [ht0, add_zero, add_zero] at this
    rw [hX'']
    exact this
  have hC : 0 < Real.exp s := Real.exp_pos s
  have hbound : ∀ x : V,
      ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ≤ Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖ := by
    intro x
    have hpl : ∀ v, Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x) ≤ Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by
      intro v
      have hop : opNormAt b X b' X'' v φ = Real.exp s := by
        rw [hX'', opNormAt_smul b X b' X' hX' c hc v φ, hc_def]
        dsimp only
        rw [mul_inv, Real.exp_neg, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel₀ (hpos v).ne',
          one_mul]
      calc Formalism.HermitianLatticesTheory.normAt b' X'' v (φ x)
          ≤ opNormAt b X b' X'' v φ * Formalism.HermitianLatticesTheory.normAt b X v x := normAt_map_le b X b' X'' hX v φ x
        _ = Real.exp s * Formalism.HermitianLatticesTheory.normAt b X v x := by rw [hop]
    have hsq : ‖Formalism.HermitianLatticesTheory.realize b' X'' (φ x)‖ ^ 2 ≤
        (Real.exp s * ‖Formalism.HermitianLatticesTheory.realize b X x‖) ^ 2 := by
      rw [mul_pow, norm_sq_realize, norm_sq_realize, Finset.mul_sum]
      refine Finset.sum_le_sum fun v _ => ?_
      rw [← mul_pow]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hpl v) 2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq
  have hAlat := (h2 K V ι b X hX A hA).1
  have hA0 : A ≠ ⊥ := by
    rintro rfl
    apply hφA
    exact Submodule.map_bot _
  have key : ∀ M : Submodule (𝓞 K) W, M.FG → A.map (φ.restrictScalars (𝓞 K)) ≤ M →
      (muMin (Formalism.HermitianLatticesTheory.realize b X) A - s ≤
          muMin (Formalism.HermitianLatticesTheory.realize b' X'') (A.map (φ.restrictScalars (𝓞 K))) ∧
        muMin (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) ∧
      (Set.InjOn φ (A : Set V) →
        muMax (Formalism.HermitianLatticesTheory.realize b X) A ≤ muMax (Formalism.HermitianLatticesTheory.realize b' X'') M + s) := by
    intro M hM hAM
    have hMlat := (h2 K W κ b' X'' hdet'' M hM).1
    have hmem : ∀ x : A, (φ.restrictScalars (𝓞 K)).domRestrict A x ∈ M := fun x =>
      hAM (Submodule.mem_map_of_mem x.2)
    let ψ : A →ₗ[𝓞 K] M := LinearMap.codRestrict M ((φ.restrictScalars (𝓞 K)).domRestrict A) hmem
    have hψ : ∀ x : A, ((ψ x : M) : W) = φ x := fun x => rfl
    have hS := h3 (𝓞 K) V W _ _ (Formalism.HermitianLatticesTheory.realize b X) (Formalism.HermitianLatticesTheory.realize b' X'') A M hAlat hMlat
      ψ (Real.exp s) hC (fun x => by rw [hψ]; exact hbound x)
    rw [Real.log_exp] at hS
    have hrange : (LinearMap.range ψ).map M.subtype = A.map (φ.restrictScalars (𝓞 K)) := by
      ext y
      simp only [Submodule.mem_map, LinearMap.mem_range, Submodule.subtype_apply]
      constructor
      · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨x, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨ψ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
    have hψ0 : ψ ≠ 0 := by
      obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hφA
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
      intro h
      apply hy0
      have := congrArg (fun g : A →ₗ[𝓞 K] M => ((g ⟨x, hx⟩ : M) : W)) h
      simpa [hψ] using this
    refine ⟨?_, fun hinj => hS.2 ?_ hA0⟩
    · have := (hS.1 hψ0).1
      rw [hrange] at this
      exact ⟨this, (hS.1 hψ0).2⟩
    · intro x y hxy
      apply Subtype.ext
      apply hinj x.2 y.2
      have := congrArg (fun z : M => (z : W)) hxy
      simpa [hψ] using this
  have hφA_fg : (A.map (φ.restrictScalars (𝓞 K))).FG := hA.map _
  obtain ⟨⟨k1, -⟩, -⟩ := key _ hφA_fg le_rfl
  have htφA := htw _ hφA_fg hφA
  rw [htφA.2] at k1
  refine ⟨?_, fun B hB hAB => ?_⟩
  · unfold muMinDef
    linarith
  · have hB0 : B ≠ ⊥ := fun h => hφA (le_bot_iff.mp (h ▸ hAB))
    obtain ⟨⟨-, k2⟩, k3⟩ := key B hB hAB
    have htB := htw B hB hB0
    rw [htB.1] at k2 k3
    refine ⟨?_, fun hinj => ?_⟩
    · unfold muMinDef muMaxDef
      linarith
    · have := k3 hinj
      unfold muMaxDef
      linarith

/- English proof (translation)
Conclude with `slopeIneqMean_of (twist_of rescale_covolume_formula place_lattice_structure (shiftInvariance_of slope_characterization slope_characterization polygon_slopes_characterization)) place_lattice_structure slope_inequality_general`.
-/
theorem slope_inequality_mean : SlopeIneqMean := by
  exact slopeIneqMean_of (twist_of rescale_covolume_formula place_lattice_structure
    (shiftInvariance_of slope_characterization slope_characterization polygon_slopes_characterization)) place_lattice_structure slope_inequality_general

end Formalism.HN
