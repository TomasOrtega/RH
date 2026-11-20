import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.MomTw
import Formalism.SharpRestriction.CuspSpanNormBounds.SpanMemOfImage
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB

open Matrix MeasureTheory

noncomputable section

namespace Formalism.MainNotions.S.Pv.Mom

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.FrameBoundFromBesselTorus

variable {k r : ℕ}

def cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twT k r * X * twTi k r

def cjM (x : Mt k r) : Mt k r := fun i j => (twT k r * Matrix.of x * twTi k r) i j

/- English proof (translation)
The claim follows from `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twT_mul_twTi)`.
-/
theorem isUnit_twT : IsUnit (twT k r) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twT_mul_twTi)

/- English proof (translation)
Unfold `cjX`. Rewrite using `[← twT_inv]`. Conclude with `Matrix.exp_conj _ _ isUnit_twT`.
-/
theorem exp_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (cjX X) = cjX (NormedSpace.exp X) := by
  unfold cjX
  rw [← twT_inv]
  exact Matrix.exp_conj _ _ isUnit_twT

/- English proof (translation)
Unfold `cjX`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem cjX_smul (c : ℂ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (c • X) = c • cjX (k := k) (r := r) X := by
  unfold cjX; rw [Matrix.mul_smul, Matrix.smul_mul]

/- English proof (translation)
Unfold `cjX`. Rewrite using `[Matrix.mul_add, Matrix.add_mul]`.
-/
theorem cjX_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (X + Y) = cjX (k := k) (r := r) X + cjX Y := by
  unfold cjX; rw [Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
The claim follows from `twT_conj_apply X i j`.
-/
theorem cjX_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    cjX X i j = twD k r i * X i j * star (twD k r j) := twT_conj_apply X i j

/- English proof (translation)
Introduce `t`. Rewrite using `[← cjX_smul, exp_cjX]`. Conclude with `twT_conj_N (hX t)`.
-/
theorem cjX_mem_lieOf {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hX : X ∈ lieOf (Nset k r)) :
    cjX X ∈ lieOf (Nset k r) := by
  intro t
  rw [← cjX_smul, exp_cjX]
  exact twT_conj_N (hX t)

def cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  twTi k r * X * twT k r

/- English proof (translation)
Unfold `cjX cjXI`. Simplify using `only [← Matrix.mul_assoc, twT_mul_twTi, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, twT_mul_twTi, Matrix.mul_one]`.
-/
theorem cjX_cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjX (cjXI (k := k) (r := r) X) = X := by
  unfold cjX cjXI
  simp only [← Matrix.mul_assoc, twT_mul_twTi, Matrix.one_mul]
  rw [Matrix.mul_assoc, twT_mul_twTi, Matrix.mul_one]

/- English proof (translation)
Unfold `cjX cjXI`. Simplify using `only [← Matrix.mul_assoc, twTi_mul_twT, Matrix.one_mul]`. Rewrite using `[Matrix.mul_assoc, twTi_mul_twT, Matrix.mul_one]`.
-/
theorem cjXI_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : cjXI (cjX (k := k) (r := r) X) = X := by
  unfold cjX cjXI
  simp only [← Matrix.mul_assoc, twTi_mul_twT, Matrix.one_mul]
  rw [Matrix.mul_assoc, twTi_mul_twT, Matrix.mul_one]

/- English proof (translation)
Rewrite `hn`, the goal using `[WeylGroupFacts.nset_iff]`. Use `⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul twTi_mem_UH hn.1) twT_mem_UH, fun i j hj hi => ?_⟩` and prove the remaining obligations. Establish `e : (twTi k r * n * twT k r) i j = star (twD k r i) * n i j * twD k r j`. Unfold `twT twTi`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Rewrite using `[e, hn.2 i j hj hi]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[mul_one, star_twD_mul]`. Simplify using the standard rewrite rules.
-/
theorem twTi_conj_N {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hn : n ∈ Nset k r) :
    twTi k r * n * twT k r ∈ Nset k r := by
  rw [WeylGroupFacts.nset_iff] at hn ⊢
  refine ⟨WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul twTi_mem_UH hn.1) twT_mem_UH, fun i j hj hi => ?_⟩
  have e : (twTi k r * n * twT k r) i j = star (twD k r i) * n i j * twD k r j := by
    unfold twT twTi; rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [e, hn.2 i j hj hi]
  split_ifs with h
  · subst h; rw [mul_one, star_twD_mul]
  · simp

/- English proof (translation)
Unfold `cjXI`. Rewrite using `[← twTi_inv]`. Conclude with `Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twTi_mul_twT))`.
-/
theorem exp_cjXI (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    NormedSpace.exp (cjXI X) = cjXI (k := k) (r := r) (NormedSpace.exp X) := by
  unfold cjXI
  rw [← twTi_inv]
  exact Matrix.exp_conj _ _ ((Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_right_inverse twTi_mul_twT))

/- English proof (translation)
Introduce `t`. Establish `e : cjXI (k` using `k) (r := r) ((t : ℂ) • X) = (t : ℂ) • cjXI X := by`. Unfold `cjXI`. Rewrite using `[Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[← e, exp_cjXI]`.

Conclude with `twTi_conj_N (hX t)`.
-/
theorem cjXI_mem_lieOf {X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hX : X ∈ lieOf (Nset k r)) :
    cjXI X ∈ lieOf (Nset k r) := by
  intro t
  have e : cjXI (k := k) (r := r) ((t : ℂ) • X) = (t : ℂ) • cjXI X := by
    unfold cjXI; rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← e, exp_cjXI]
  exact twTi_conj_N (hX t)

/- English proof (translation)
Apply the tactic sequence `funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]`.
-/
theorem realifyFun_add (X Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun (X + Y) = realifyFun X + realifyFun Y := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

/- English proof (translation)
Apply the tactic sequence `funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]`.
-/
theorem realifyFun_smul (c : ℝ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    realifyFun ((c : ℂ) • X) = c • realifyFun X := by
  funext p; rcases p with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

def rotE (f : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (hadd : ∀ X Y, f (X + Y) = f X + f Y) (hsm : ∀ (c : ℂ) X, f (c • X) = c • f X) :
    EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) where
  toFun y := WithLp.toLp 2 (realifyFun (f (unrealify y)))
  map_add' x y := by
    rw [unrealify_add', hadd, realifyFun_add]; rfl
  map_smul' c x := by
    rw [unrealify_smul', hsm, realifyFun_smul]; rfl

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `apply Complex.ext <;> simp [unrealify, realifyFun]`.
-/
theorem unrealify_toLp (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    unrealify (WithLp.toLp 2 (realifyFun X) : EuclideanSpace ℝ (IxE k r)) = X := by
  ext i j
  apply Complex.ext <;> simp [unrealify, realifyFun]

/- English proof (translation)
Use extensionality with `⟨i, j, b⟩`. Apply the tactic sequence `cases b <;> simp [unrealify, realifyFun]`.
-/
theorem realify_unrealify (y : EuclideanSpace ℝ (IxE k r)) :
    (WithLp.toLp 2 (realifyFun (unrealify y)) : EuclideanSpace ℝ (IxE k r)) = y := by
  ext ⟨i, j, b⟩
  cases b <;> simp [unrealify, realifyFun]

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Fintype.sum_bool]`.

Simplify using `[realifyFun, Complex.normSq_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sumSq_realify (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∑ p : IxE k r, (realifyFun X p) ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_bool]
  simp [realifyFun, Complex.normSq_apply]
  ring

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using the standard rewrite rules.
-/
theorem norm_sq_toLp (f : IxE k r → ℝ) : ‖(WithLp.toLp 2 f : EuclideanSpace ℝ (IxE k r))‖ ^ 2 = ∑ p, f p ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp

/- English proof (translation)
Rewrite using `[cjX_apply, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_eq_norm_sq (twD k r i), Complex.normSq_eq_norm_sq (star (twD k r j)), norm_star, norm_twD, norm_twD]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem normSq_cjX (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) :
    Complex.normSq (cjX X i j) = Complex.normSq (X i j) := by
  rw [cjX_apply, Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_eq_norm_sq (twD k r i),
    Complex.normSq_eq_norm_sq (star (twD k r j)), norm_star, norm_twD, norm_twD]
  ring

def rotC (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjX cjX_add cjX_smul

def rotCI (k r : ℕ) : EuclideanSpace ℝ (IxE k r) →ₗ[ℝ] EuclideanSpace ℝ (IxE k r) :=
  rotE (k := k) (r := r) cjXI
    (fun X Y => by unfold cjXI; rw [Matrix.mul_add, Matrix.add_mul])
    (fun c X => by unfold cjXI; rw [Matrix.mul_smul, Matrix.smul_mul])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rotC_apply (y : EuclideanSpace ℝ (IxE k r)) : rotC k r y = WithLp.toLp 2 (realifyFun (cjX (unrealify y))) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem rotCI_apply (y : EuclideanSpace ℝ (IxE k r)) :
    rotCI k r y = WithLp.toLp 2 (realifyFun (cjXI (unrealify y))) := rfl

/- English proof (translation)
Rewrite using `[rotC_apply, rotCI_apply, unrealify_toLp, cjX_cjXI, realify_unrealify]`.
-/
theorem rotC_rotCI (y : EuclideanSpace ℝ (IxE k r)) : rotC k r (rotCI k r y) = y := by
  rw [rotC_apply, rotCI_apply, unrealify_toLp, cjX_cjXI, realify_unrealify]

/- English proof (translation)
Rewrite using `[rotC_apply, rotCI_apply, unrealify_toLp, cjXI_cjX, realify_unrealify]`.
-/
theorem rotCI_rotC (y : EuclideanSpace ℝ (IxE k r)) : rotCI k r (rotC k r y) = y := by
  rw [rotC_apply, rotCI_apply, unrealify_toLp, cjXI_cjX, realify_unrealify]

/- English proof (translation)
Establish `h1 : ‖rotC k r y‖ ^ 2 = ‖y‖ ^ 2`. Rewrite using `[rotC_apply, norm_sq_toLp, sumSq_realify]`. Use `conv_rhs => rw [← realify_unrealify y, norm_sq_toLp, sumSq_realify]`. Simplify using `only [normSq_cjX]`. Conclude with `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1`.
-/
theorem norm_rotC (y : EuclideanSpace ℝ (IxE k r)) : ‖rotC k r y‖ = ‖y‖ := by
  have h1 : ‖rotC k r y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [rotC_apply, norm_sq_toLp, sumSq_realify]
    conv_rhs => rw [← realify_unrealify y, norm_sq_toLp, sumSq_realify]
    simp only [normSq_cjX]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

/- English proof (translation)
Introduce `x hx`. Use `span_mem_of_image ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨X, hX, rfl⟩, rfl⟩`. Use `⟨cjX X, cjX_mem_lieOf hX, ?_⟩` and prove the remaining obligations. Use `show _ = rotC k r ((WithLp.equiv 2 _).symm (realifyFun X))`.

Rewrite using `[rotC_apply]`. Use `congr 2`.
-/
theorem rotC_mem : ∀ x ∈ lieE (Nset k r), rotC k r x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨cjX X, cjX_mem_lieOf hX, ?_⟩
  show _ = rotC k r ((WithLp.equiv 2 _).symm (realifyFun X))
  rw [rotC_apply]
  congr 2

/- English proof (translation)
Introduce `x hx`. Use `span_mem_of_image ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨X, hX, rfl⟩, rfl⟩`. Use `⟨cjXI X, cjXI_mem_lieOf hX, ?_⟩` and prove the remaining obligations. Use `show _ = rotCI k r ((WithLp.equiv 2 _).symm (realifyFun X))`.

Rewrite using `[rotCI_apply]`. Use `congr 2`.
-/
theorem rotCI_mem : ∀ x ∈ lieE (Nset k r), rotCI k r x ∈ lieE (Nset k r) := by
  intro x hx
  refine span_mem_of_image ?_ hx
  rintro _ ⟨_, ⟨X, hX, rfl⟩, rfl⟩
  refine ⟨cjXI X, cjXI_mem_lieOf hX, ?_⟩
  show _ = rotCI k r ((WithLp.equiv 2 _).symm (realifyFun X))
  rw [rotCI_apply]
  congr 2

def rotLE (k r : ℕ) : lieE (Nset k r) ≃ₗ[ℝ] lieE (Nset k r) :=
  LinearEquiv.ofLinear ((rotC k r).restrict rotC_mem) ((rotCI k r).restrict rotCI_mem)
    (LinearMap.ext fun x => by apply Subtype.ext; exact rotC_rotCI _)
    (LinearMap.ext fun x => by apply Subtype.ext; exact rotCI_rotC _)

def rotIso (k r : ℕ) : lieE (Nset k r) ≃ₗᵢ[ℝ] lieE (Nset k r) :=
  { rotLE k r with norm_map' := fun x => norm_rotC (k := k) (r := r) x.1 }

/- English proof (translation)
Establish `: Continuous (cjM (k` using `k) (r := r)) := by`. Establish `h : Continuous (fun x : Mt k r => (twT k r * Matrix.of x * twTi k r : Matrix _ _ ℂ))` using `(continuous_const.matrix_mul continuous_id).matrix_mul continuous_const`. Conclude with `h`. Conclude with `this.measurable`.
-/
theorem measurable_cjM : Measurable (cjM (k := k) (r := r)) := by
  have : Continuous (cjM (k := k) (r := r)) := by
    have h : Continuous (fun x : Mt k r => (twT k r * Matrix.of x * twTi k r : Matrix _ _ ℂ)) :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    exact h
  exact this.measurable

/- English proof (translation)
Use function extensionality and compare the values at `i j`. Use `show cjX (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r)))) i j = NormedSpace.exp (unrealify ((rotC k r) (x : EuclideanSpace ℝ (IxE k r)))) i j`. Rewrite using `[rotC_apply, unrealify_toLp, exp_cjX]`.
-/
theorem cjM_expL (x : lieE (Nset k r)) : cjM (expL (Nset k r) x) = expL (Nset k r) (rotIso k r x) := by
  funext i j
  show cjX (NormedSpace.exp (unrealify (x : EuclideanSpace ℝ (IxE k r)))) i j =
    NormedSpace.exp (unrealify ((rotC k r) (x : EuclideanSpace ℝ (IxE k r)))) i j
  rw [rotC_apply, unrealify_toLp, exp_cjX]

/- English proof (translation)
Establish `e : cjM ∘ expL (Nset k r) = expL (Nset k r) ∘ (rotIso k r)` using `funext cjM_expL`. Establish `h0 : haarLie (Nset k r) κN = κN • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r))` using `rfl`. Rewrite using `[h0, Measure.map_smul, Measure.map_map measurable_cjM (continuous_expL _).measurable, e, ← Measure.map_map (continuous_expL _).measurable (rotIso k r).continuous.measurable, (rotIso k r).measurePreserving.map_eq]`.
-/
theorem map_haarLie_cjM (κN : ENNReal) : (haarLie (Nset k r) κN).map cjM = haarLie (Nset k r) κN := by
  have e : cjM ∘ expL (Nset k r) = expL (Nset k r) ∘ (rotIso k r) := funext cjM_expL
  have h0 : haarLie (Nset k r) κN = κN • (volume : Measure (lieE (Nset k r))).map (expL (Nset k r)) := rfl
  rw [h0, Measure.map_smul, Measure.map_map measurable_cjM (continuous_expL _).measurable, e,
    ← Measure.map_map (continuous_expL _).measurable (rotIso k r).continuous.measurable,
    (rotIso k r).measurePreserving.map_eq]

/- English proof (translation)
Establish `e` using `twT_comm_block hh`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem twTi_comm_block {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : WeylGroupFacts.block k r h) :
    twTi k r * h = h * twTi k r := by
  have e := twT_comm_block hh
  calc twTi k r * h = twTi k r * h * (twT k r * twTi k r) := by rw [twT_mul_twTi, Matrix.mul_one]
    _ = twTi k r * (h * twT k r) * twTi k r := by simp only [Matrix.mul_assoc]
    _ = twTi k r * (twT k r * h) * twTi k r := by rw [e]
    _ = h * twTi k r := by rw [← Matrix.mul_assoc, twTi_mul_twT, Matrix.one_mul]

/- English proof (translation)
Take `⟨h, hh, m, hm, rfl⟩` from `hs`. Establish `hb` using `WeylGroupFacts.uw_block hh`. Rewrite using `[twT_inv]`. Prove the components needed by the constructor for the conclusion. Use `⟨h, hh, twT k r * m * twTi k r, twT_conj_N hm, ?_⟩` and prove the remaining obligations.

Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, twT_comm_block hb]`. Simplify using `only [Matrix.mul_assoc]`. Use `⟨h, hh, twTi k r * m * twT k r, twTi_conj_N hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, twTi_comm_block hb]`. Simplify using `only [Matrix.mul_assoc]`.
-/
theorem twT_conj_S {z : Fin (2 * r + k + 1) → ℂ} {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hs : s ∈ Sset k r z) :
    twT k r * s * (twT k r)⁻¹ ∈ Sset k r z ∧ (twT k r)⁻¹ * s * twT k r ∈ Sset k r z := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hb := WeylGroupFacts.uw_block hh
  rw [twT_inv]
  constructor
  · refine ⟨h, hh, twT k r * m * twTi k r, twT_conj_N hm, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, twT_comm_block hb]; simp only [Matrix.mul_assoc]
  · refine ⟨h, hh, twTi k r * m * twT k r, twTi_conj_N hm, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, twTi_comm_block hb]; simp only [Matrix.mul_assoc]

/- English proof (translation)
Rewrite using `[twT_inv]`. Establish `: SigmaFinite μW` using `hW.1`. Establish `hsf : SFinite (haarLie (Nset k r) κN)` using `sFinite_haarLie _ _`. Establish `hmul : Measurable (Formalism.MainNotions.BridgeCSB.mulP (k` using `k) (r := r)) := Formalism.MainNotions.BridgeCSB.continuous_mulP.measurable`. Use `show ((μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP).map cjM = (μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP`.

Rewrite using `[Measure.map_map measurable_cjM hmul]`. Establish `hae : cjM ∘ Formalism.MainNotions.BridgeCSB.mulP =ᵐ[μW.prod (haarLie (Nset k r) κN)] Formalism.MainNotions.BridgeCSB.mulP ∘ Prod.map id cjM`. Establish `h0 : (μW.prod (haarLie (Nset k r) κN)) ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ) = 0`. Rewrite using `[Measure.prod_prod, hW.2.2.1, zero_mul]`. Use `Filter.eventuallyEq_of_mem (s := ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ)ᶜ) (measure_eq_zero_iff_ae_notMem.mp h0 |> fun h => by` and prove the remaining obligations.

Rewrite `h` using `[Filter.Eventually]`. Simplify `h) ?_` using `[Set.compl_def]`. Introduce `p hp`. Establish `hp1 : Matrix.of p.1 ∈ UWset k r z`. Assume the negation of the conclusion as `hc`.

Conclude with `hp ⟨hc, Set.mem_univ _⟩`. Establish `hb` using `WeylGroupFacts.uw_block hp1`. Use function extensionality and compare the values at `i j`. Use `show (twT k r * Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) * twTi k r) i j = (Matrix.of p.1 * Matrix.of (cjM p.2)) i j`. Establish `e1 : (Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) : Matrix _ _ ℂ) = Matrix.of p.1 * Matrix.of p.2` using `rfl`.

Establish `e2 : (Matrix.of (cjM p.2) : Matrix _ _ ℂ) = twT k r * Matrix.of p.2 * twTi k r` using `rfl`. Rewrite using `[e1, e2, ← Matrix.mul_assoc, twT_comm_block hb]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[Measure.map_congr hae, ← Measure.map_map hmul (measurable_id.prodMap measurable_cjM)]`. Establish `hmp : MeasurePreserving (Prod.map id cjM) (μW.prod (haarLie (Nset k r) κN)) (μW.prod (haarLie (Nset k r) κN))` using `(MeasurePreserving.id μW).prod ⟨measurable_cjM, map_haarLie_cjM κN⟩`.

Rewrite using `[hmp.map_eq]`.
-/
theorem map_muS_cjM {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)} (κN : ENNReal)
    (hW : IsHaarOn (UWset k r z) μW) :
    (muS μW (haarLie (Nset k r) κN)).map (fun x => fun i j => (twT k r * Matrix.of x * (twT k r)⁻¹) i j) =
      muS μW (haarLie (Nset k r) κN) := by
  rw [twT_inv]
  have : SigmaFinite μW := hW.1
  have hsf : SFinite (haarLie (Nset k r) κN) := sFinite_haarLie _ _
  have hmul : Measurable (Formalism.MainNotions.BridgeCSB.mulP (k := k) (r := r)) := Formalism.MainNotions.BridgeCSB.continuous_mulP.measurable
  show ((μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP).map cjM =
    (μW.prod (haarLie (Nset k r) κN)).map Formalism.MainNotions.BridgeCSB.mulP
  rw [Measure.map_map measurable_cjM hmul]
  have hae : cjM ∘ Formalism.MainNotions.BridgeCSB.mulP =ᵐ[μW.prod (haarLie (Nset k r) κN)]
      Formalism.MainNotions.BridgeCSB.mulP ∘ Prod.map id cjM := by
    have h0 : (μW.prod (haarLie (Nset k r) κN)) ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hW.2.2.1, zero_mul]
    refine Filter.eventuallyEq_of_mem (s := ({x | Matrix.of x ∉ UWset k r z} ×ˢ Set.univ)ᶜ)
      (measure_eq_zero_iff_ae_notMem.mp h0 |> fun h => by
        rw [Filter.Eventually] at h; simpa [Set.compl_def] using h) ?_
    intro p hp
    have hp1 : Matrix.of p.1 ∈ UWset k r z := by
      by_contra hc
      exact hp ⟨hc, Set.mem_univ _⟩
    have hb := WeylGroupFacts.uw_block hp1
    funext i j
    show (twT k r * Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) * twTi k r) i j =
      (Matrix.of p.1 * Matrix.of (cjM p.2)) i j
    have e1 : (Matrix.of (Formalism.MainNotions.BridgeCSB.mulP p) : Matrix _ _ ℂ) = Matrix.of p.1 * Matrix.of p.2 := rfl
    have e2 : (Matrix.of (cjM p.2) : Matrix _ _ ℂ) = twT k r * Matrix.of p.2 * twTi k r := rfl
    rw [e1, e2, ← Matrix.mul_assoc, twT_comm_block hb]
    simp only [Matrix.mul_assoc]
  rw [Measure.map_congr hae, ← Measure.map_map hmul (measurable_id.prodMap measurable_cjM)]
  have hmp : MeasurePreserving (Prod.map id cjM) (μW.prod (haarLie (Nset k r) κN)) (μW.prod (haarLie (Nset k r) κN)) :=
    (MeasurePreserving.id μW).prod ⟨measurable_cjM, map_haarLie_cjM κN⟩
  rw [hmp.map_eq]

end Formalism.MainNotions.S.Pv.Mom
