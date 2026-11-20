import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne

noncomputable section

namespace GlobalTheory.DefPt.Model

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.DualWeyl MvPolynomial GlobalTheory.DefPt
open scoped Matrix

section Adelic

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i => HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun w => h w i, fun h w i => by obtain ⟨a, ha⟩ := h i; rw [← ha]; exact w.valuation_le_one a⟩`.
-/
theorem mem_locLat_const (g : Matrix ι ι K) (x : ι → K) :
    x ∈ locLat (fun _ : HeightOneSpectrum (𝓞 K) => g) ↔ ∀ i, (g *ᵥ x) i ∈ (algebraMap (𝓞 K) K).range :=
  ⟨fun h i => HeightOneSpectrum.mem_integers_of_valuation_le_one K _ fun w => h w i,
   fun h w i => by obtain ⟨a, ha⟩ := h i; rw [← ha]; exact w.valuation_le_one a⟩

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Simplify using `[ha]`. Use `(GlobalTheory.FlatLine.finite_vAdd ha).subset fun w hw h0 => hw ?_` and prove the remaining obligations. Establish `h1 : vAdd w a = 0` using `Int.cast_eq_zero.1 h0`. Establish `h2 : w.valuation K a ≠ 0` using `(Valuation.ne_zero_iff _).2 ha`.

Rewrite `h1` using `[vAdd, neg_eq_zero]`. Rewrite using `[← WithZero.exp_log h2, h1]`. Simplify using the standard rewrite rules.
-/
theorem finite_not_le (a : K) : {w : HeightOneSpectrum (𝓞 K) | ¬ w.valuation K a ≤ 1}.Finite := by
  by_cases ha : a = 0
  · simp [ha]
  refine (GlobalTheory.FlatLine.finite_vAdd ha).subset fun w hw h0 => hw ?_
  have h1 : vAdd w a = 0 := Int.cast_eq_zero.1 h0
  have h2 : w.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  rw [vAdd, neg_eq_zero] at h1
  rw [← WithZero.exp_log h2, h1]; simp

/- English proof (translation)
Use `(Set.finite_iUnion fun p : ι × ι => finite_not_le (g p.1 p.2)).subset fun w hw => ?_` and prove the remaining obligations. Simplify using `only [IntAt, Set.mem_setOf_eq, not_forall] at hw`. Take `⟨i, j, h⟩` from `hw`. Conclude with `Set.mem_iUnion.2 ⟨(i, j), h⟩`.
-/
theorem finite_not_intAt (g : Matrix ι ι K) : {w : HeightOneSpectrum (𝓞 K) | ¬ IntAt w g}.Finite := by
  refine (Set.finite_iUnion fun p : ι × ι => finite_not_le (g p.1 p.2)).subset fun w hw => ?_
  simp only [IntAt, Set.mem_setOf_eq, not_forall] at hw
  obtain ⟨i, j, h⟩ := hw
  exact Set.mem_iUnion.2 ⟨(i, j), h⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun _ => hg, ((finite_not_intAt g).union (finite_not_intAt g⁻¹)).subset fun w hw => by simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hw ⊢; exact hw⟩`.
-/
theorem isAdelic_const {g : Matrix ι ι K} (hg : g.det ≠ 0) : IsAdelic (fun _ : HeightOneSpectrum (𝓞 K) => g) :=
  ⟨fun _ => hg, ((finite_not_intAt g).union (finite_not_intAt g⁻¹)).subset fun w hw => by
    simp only [Set.mem_setOf_eq, Set.mem_union, not_and_or] at hw ⊢; exact hw⟩

open Classical in

/- English proof (translation)
Apply the tactic sequence `refine ⟨fun w => by by_cases h : w = v <;> simp [h, hg], (Set.finite_singleton v).subset fun w hw => ?_⟩`. Assume the negation of the conclusion as `h`. Establish `h' : w ≠ v` using `h`. Establish `h1 : IntAt w (1 : Matrix ι ι K)` using `fun i j => by`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.

Conclude with `hw (by simp [h', h1])`.
-/
theorem isAdelic_single (v : HeightOneSpectrum (𝓞 K)) {g : Matrix ι ι K} (hg : g.det ≠ 0) :
    IsAdelic (fun w : HeightOneSpectrum (𝓞 K) => if w = v then g else 1) := by
  refine ⟨fun w => by by_cases h : w = v <;> simp [h, hg], (Set.finite_singleton v).subset fun w hw => ?_⟩
  by_contra h
  have h' : w ≠ v := h
  have h1 : IntAt w (1 : Matrix ι ι K) := fun i j => by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  exact hw (by simp [h', h1])

/- English proof (translation)
Introduce `h` and use `h.1 v (by simp)`.
-/
theorem not_isAdelic_zero [Nonempty ι] (v : HeightOneSpectrum (𝓞 K)) :
    ¬ IsAdelic (fun _ : HeightOneSpectrum (𝓞 K) => (0 : Matrix ι ι K)) := fun h => h.1 v (by simp)

/- English proof (translation)
Use `GlobalTheory.FlatLine.lineDeg_num hg` as an intermediate fact. Simplify `this` using `only [detDeg, RingHom.map_det, RingHom.mapMatrix_apply]`.
-/
theorem detDeg_const {g : Matrix ι ι K} (hg : g.det ≠ 0) :
    detDeg (fun _ : HeightOneSpectrum (𝓞 K) => g) (fun σ => g.map σ) = 0 := by
  have := GlobalTheory.FlatLine.lineDeg_num hg
  simpa only [detDeg, RingHom.map_det, RingHom.mapMatrix_apply] using this

/- English proof (translation)
Simplify using `only [matNorm, Matrix.one_mulVec]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mulVec]`. Both sides reduce to the same expression.
-/
theorem matNorm_map (g : Matrix ι ι K) (σ : K →+* ℂ) (x : ι → K) :
    matNorm (fun σ => g.map σ) σ x = matNorm (fun _ => 1) σ (g *ᵥ x) := by
  simp only [matNorm, Matrix.one_mulVec]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mulVec]; rfl

/- English proof (translation)
Simplify using `[detDeg, GlobalTheory.FlatLine.lineDeg, GlobalTheory.FlatLine.sum_vAdd_nat hn]`.
-/
theorem detDeg_nat {n : ℕ} (hn : n ≠ 0) :
    detDeg (fun _ : HeightOneSpectrum (𝓞 K) => !![(n : K)]) (fun _ => 1) = Real.log n := by
  simp [detDeg, GlobalTheory.FlatLine.lineDeg, GlobalTheory.FlatLine.sum_vAdd_nat hn]

/- English proof (translation)
Introduce `w i` and use `by have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn fin_cases i simp [Matrix.mulVec, dotProduct, this]`.
-/
theorem inv_mem {n : ℕ} (hn : n ≠ 0) :
    ![(n : K)⁻¹] ∈ locLat (fun _ : HeightOneSpectrum (𝓞 K) => !![(n : K)]) := fun w i => by
  have : (n : K) ≠ 0 := Nat.cast_ne_zero.2 hn
  fin_cases i
  simp [Matrix.mulVec, dotProduct, this]

end Adelic

section Tensor

variable {T : Type} [Fintype T] [DecidableEq T] {N : T → ℕ} {n : ℕ}

/- English proof (translation)
Simplify using `[rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]`.
-/
theorem rhoMat_one (la : Fin n → ℕ) (K : Type) [Field K] [CharZero K] : rhoMat la (1 : Matrix _ _ K) = 1 := by
  simp [rhoMat, ← Module.End.one_eq_id, LinearMap.toMatrix_one]

/- English proof (translation)
Simplify using `[rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]`.
-/
theorem rhoMat_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g h : Matrix (Fin n) (Fin n) K) :
    rhoMat la (g * h) = rhoMat la h * rhoMat la g := by
  simp [rhoMat, Matrix.transpose_mul, LinearMap.toMatrix_mul]

/- English proof (translation)
Establish `: rho la K (t • 1) = t ^ size la • LinearMap.id` using `LinearMap.ext fun f => rho_scalar t f`. Simplify using `[rhoMat, this]`.
-/
theorem rhoMat_scalar (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (t : K) :
    rhoMat la (t • (1 : Matrix _ _ K)) = t ^ size la • 1 := by
  have : rho la K (t • 1) = t ^ size la • LinearMap.id := LinearMap.ext fun f => rho_scalar t f
  simp [rhoMat, this]

/- English proof (translation)
Establish `h` using `congrArg (fun f : nabla la K => evalAt y f.1) ((basis la K).sum_repr f)`. Simplify using `only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul, coe_basis] at h`. Conclude with `h.symm`.
-/
theorem evalAt_eq_sum (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (y : Matrix (Fin n) (Fin n) K) (f : nabla la K) :
    evalAt y f.1 = ∑ i, (basis la K).repr f i * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h := congrArg (fun f : nabla la K => evalAt y f.1) ((basis la K).sum_repr f)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul, coe_basis] at h
  exact h.symm

/- English proof (translation)
Establish `h1` using `evalAt_rho y gᵀ (basis la K j)`. Rewrite `h1` using `[Matrix.transpose_transpose, coe_basis]`. Rewrite using `[← h1, evalAt_eq_sum]`. Simplify using `only [rhoMat, LinearMap.toMatrix_apply]`.
-/
theorem evalAt_mul (la : Fin n → ℕ) {K : Type} [Field K] [CharZero K] (g y : Matrix (Fin n) (Fin n) K) (j : Idx la) :
    evalAt (g * y) (map (Int.castRingHom K) (intVec la j)) =
      ∑ i, rhoMat la g i j * evalAt y (map (Int.castRingHom K) (intVec la i)) := by
  have h1 := evalAt_rho y gᵀ (basis la K j)
  rw [Matrix.transpose_transpose, coe_basis] at h1
  rw [← h1, evalAt_eq_sum]
  simp only [rhoMat, LinearMap.toMatrix_apply]

/- English proof (translation)
Simplify using `only [tval, evalAt_mul, fibA, one_smul, Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun I _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun J _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem tval_mul (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (x : TIdx la → K)
    (g y : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) :
    tval la x (fun t => g t * y t) = tval la (fibA la 1 g *ᵥ x) y := by
  simp only [tval, evalAt_mul, fibA, one_smul, Matrix.mulVec, dotProduct, kron, Matrix.of_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib]; ring

/- English proof (translation)
Use extensionality with `I I'`. Simplify using `only [kron, Matrix.mul_apply, Matrix.of_apply]`. Rewrite using `[Finset.prod_univ_sum, Fintype.piFinset_univ]`. Simplify using `[Finset.prod_mul_distrib]`.
-/
theorem kron_mul {J : T → Type} [∀ t, Fintype (J t)] {R : Type} [CommRing R] (M M' : ∀ t, Matrix (J t) (J t) R) :
    kron M * kron M' = kron fun t => M t * M' t := by
  ext I I'
  simp only [kron, Matrix.mul_apply, Matrix.of_apply]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp [Finset.prod_mul_distrib]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Establish `h` using `congrArg (fun f : nabla la ℂ => (onBasis la).repr (toSpace la f) i) ((basis la ℂ).sum_repr f)`. Simplify using `only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h`. Rewrite using `[← h]`. Simplify using `only [onMat, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]`.
-/
theorem onMat_mulVec (la : Fin n → ℕ) (f : nabla la ℂ) :
    onMat la *ᵥ (basis la ℂ).repr f = (onBasis la).repr (toSpace la f) := by
  funext i
  have h := congrArg (fun f : nabla la ℂ => (onBasis la).repr (toSpace la f) i) ((basis la ℂ).sum_repr f)
  simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [← h]
  simp only [onMat, Matrix.mulVec, dotProduct, Matrix.of_apply, mul_comm]

/- English proof (translation)
Establish `h : rhoMat la X *ᵥ (basis la ℂ).repr f = (basis la ℂ).repr (rho la ℂ Xᵀ f)` using `LinearMap.toMatrix_mulVec_repr _ _ _ _`. Rewrite using `[← Matrix.mulVec_mulVec, h, onMat_mulVec, ← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map, norm_toSpace_sq, coe_rho, Matrix.transpose_transpose]`.
-/
theorem sum_sq_onMat (la : Fin n → ℕ) (X : Matrix (Fin n) (Fin n) ℂ) (f : nabla la ℂ) :
    ∑ i, ‖((onMat la * rhoMat la X) *ᵥ (basis la ℂ).repr f) i‖ ^ 2 = normSq la (Formalism.GradedWeylDivisibility.rowAct ℂ X f.1) := by
  have h : rhoMat la X *ᵥ (basis la ℂ).repr f = (basis la ℂ).repr (rho la ℂ Xᵀ f) :=
    LinearMap.toMatrix_mulVec_repr _ _ _ _
  rw [← Matrix.mulVec_mulVec, h, onMat_mulVec, ← EuclideanSpace.norm_sq_eq, LinearIsometryEquiv.norm_map,
    norm_toSpace_sq, coe_rho, Matrix.transpose_transpose]

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun t => (Fintype.card_pos_iff.1 (dim_eq_card (la t) ▸ dim_pos (h t))).some⟩`.
-/
theorem nonempty_tIdx (la : ∀ t, Fin (N t) → ℕ) (h : ∀ t, Antitone (la t)) : Nonempty (TIdx la) :=
  ⟨fun t => (Fintype.card_pos_iff.1 (dim_eq_card (la t) ▸ dim_pos (h t))).some⟩

/- English proof (translation)
Use `⟨fun I => (basis la ℚ).repr ⟨extremal la ℚ, extremal_mem h⟩ (I ()), ?_⟩` and prove the remaining obligations. Establish `h2` using `evalAt_eq_sum la 1 (⟨extremal la ℚ, extremal_mem h⟩ : nabla la ℚ)`. Rewrite `h2` using `[evalAt_one_extremal]`. Rewrite using `[h2, tval, ← (Equiv.funUnique Unit (Idx la)).symm.sum_comp]`. Simplify using the standard rewrite rules.
-/
theorem exists_tval_ne_zero (la : Fin n → ℕ) (h : Antitone la) :
    ∃ x : TIdx (fun _ : Unit => la) → ℚ, tval (fun _ : Unit => la) x (fun _ => 1) = 1 := by
  refine ⟨fun I => (basis la ℚ).repr ⟨extremal la ℚ, extremal_mem h⟩ (I ()), ?_⟩
  have h2 := evalAt_eq_sum la 1 (⟨extremal la ℚ, extremal_mem h⟩ : nabla la ℚ)
  rw [evalAt_one_extremal] at h2
  rw [h2, tval, ← (Equiv.funUnique Unit (Idx la)).symm.sum_comp]
  simp

/- English proof (translation)
Simplify using `only [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, rhoMat_mul, smul_smul, mul_comm]`.
-/
theorem fibA_mul (la : ∀ t, Fin (N t) → ℕ) {K : Type} [Field K] [CharZero K] (a b : K)
    (g h : ∀ t, Matrix (Fin (N t)) (Fin (N t)) K) : fibA la a g * fibA la b h = fibA la (a * b) fun t => h t * g t := by
  simp only [fibA, Matrix.smul_mul, Matrix.mul_smul, kron_mul, rhoMat_mul, smul_smul, mul_comm]

/- English proof (translation)
Simplify using `only [fibY, fibA, rhoMat_one, Matrix.mul_one, one_smul, Matrix.smul_mul, kron_mul]`.
-/
theorem fibY_eq (la : ∀ t, Fin (N t) → ℕ) (s : ℝ) (X : ∀ t, Matrix (Fin (N t)) (Fin (N t)) ℂ) :
    fibY la s X = fibY la s (fun _ => 1) * fibA la 1 X := by
  simp only [fibY, fibA, rhoMat_one, Matrix.mul_one, one_smul, Matrix.smul_mul, kron_mul]

/- English proof (translation)
Use extensionality with `I J`. Simplify using `only [fibA, kron, rhoMat_scalar, one_smul, Matrix.of_apply, Finset.univ_unique, Finset.prod_singleton, Matrix.smul_apply, Matrix.one_apply, size, Fin.sum_univ_two]`. Distinguish the cases in `h : I = J`. Simplify using `[h]`. Establish `: I default ≠ J default` using `fun h' => h (funext fun _ => h')`.

Simplify using `[h, this]`.
-/
theorem fibA_two : fibA (fun _ : Unit => ![1, 0]) (1 : ℚ) (fun _ => (2 : ℚ) • 1) = (2 : ℚ) • 1 := by
  ext I J
  simp only [fibA, kron, rhoMat_scalar, one_smul, Matrix.of_apply, Finset.univ_unique, Finset.prod_singleton,
    Matrix.smul_apply, Matrix.one_apply, size, Fin.sum_univ_two]
  by_cases h : I = J
  · simp [h]
  · have : I default ≠ J default := fun h' => h (funext fun _ => h')
    simp [h, this]

end Tensor

end GlobalTheory.DefPt.Model

end
