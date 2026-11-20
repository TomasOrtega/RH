import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.IsOrth
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfA
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.ExhaustionFrames

namespace GlobalTheory.UpCoordCompare

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.ExhaustionFrames
open scoped Matrix ComplexOrder ContDiff

noncomputable section

/- English proof (translation)
Establish `h` using `(hK.neg).charpoly_eq_X_pow_finrank`. Establish `h2` using `LinearMap.eval_charpoly (-K) 1`. Rewrite `h2` using `[h]`. Simplify using `using h2.symm`.
-/
theorem det_one_add_of_isNilpotent {W : Type} [AddCommGroup W] [Module ℝ W] [Module.Finite ℝ W]
    {K : W →ₗ[ℝ] W} (hK : IsNilpotent K) : LinearMap.det (1 + K) = 1 := by
  have h := (hK.neg).charpoly_eq_X_pow_finrank
  have h2 := LinearMap.eval_charpoly (-K) 1
  rw [h] at h2
  simpa using h2.symm

/- English proof (translation)
Establish `hdet : ∀ z, (fderiv ℝ F z).det = 1`. Introduce `z`. Use `set K : V n →ₗ[ℝ] V n := (fderiv ℝ F z : V n →ₗ[ℝ] V n) - 1 with hK`. Establish `hstep : ∀ (i : Fin n) (h : V n), (∀ j, ρ j < ρ i → h j = 0) → K h i = 0`. Introduce `i h hh`.

Establish `h1 : HasDerivAt (fun t : ℝ => z + t • h) h 0`. Simplify using `using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z`. Establish `h2 : HasDerivAt (fun t : ℝ => F (z + t • h)) (fderiv ℝ F z h) 0`. Conclude with `(hF z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)`. Establish `h3` using `(PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℂ) i).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (h2.sub h1)`.

Establish `h4 : (fun t : ℝ => F (z + t • h) i - (z + t • h) i) = fun _ => F z i - z i`. Use function extensionality and compare the values at `t`. Conclude with `htri i _ _ fun j hj => by simp [hh j hj]`. Establish `h5 : HasDerivAt (fun t : ℝ => F (z + t • h) i - (z + t • h) i) (fderiv ℝ F z h i - h i) 0` using `h3`. Rewrite `h5` using `[h4]`.

Use `h5.unique (hasDerivAt_const _ _)` as an intermediate fact. Simplify `this` using `[hK]`. Establish `hpow : ∀ (m : ℕ) (h : V n) (i : Fin n), ρ i < m → (K ^ m) h i = 0`. Introduce `m`. Proceed by induction on `m with`.

Consider the case `zero => intro h i hi`. Use linear arithmetic over natural numbers and integers. Consider the case `succ m ih`. Introduce `h i hi`. Rewrite using `[pow_succ', Module.End.mul_apply]`.

Conclude with `hstep i _ fun j hj => ih h j (by omega)`. Establish `hnil : IsNilpotent K`. Use `⟨Finset.univ.sup ρ + 1, ?_⟩` and prove the remaining obligations. Use extensionality with `h i`. Establish `: ρ i ≤ Finset.univ.sup ρ` using `Finset.le_sup (Finset.mem_univ i)`.

Simplify using `using hpow _ h i (by omega)`. Use `det_one_add_of_isNilpotent hnil` as an intermediate fact. Rewrite `this` using `[hK, add_sub_cancel]`. Conclude with `this`. Use `⟨hF.continuous.measurable, ?_⟩` and prove the remaining obligations.

Use `map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (V n)) (s := Set.univ) (f := F) (f' := fderiv ℝ F) MeasurableSet.univ.nullMeasurableSet (fun x _ => (hF x).hasFDerivAt.hasFDerivWithinAt) hb.1.injOn` as an intermediate fact. Simplify `this` using `[hdet, hb.2.range_eq]`.
-/
theorem measurePreserving_of_triangular {n : ℕ} (F : V n → V n) (hF : Differentiable ℝ F)
    (hb : Function.Bijective F) (ρ : Fin n → ℕ)
    (htri : ∀ (i : Fin n) (z w : V n), (∀ j, ρ j < ρ i → z j = w j) → F z i - z i = F w i - w i) :
    MeasurePreserving F volume volume := by
  have hdet : ∀ z, (fderiv ℝ F z).det = 1 := by
    intro z
    set K : V n →ₗ[ℝ] V n := (fderiv ℝ F z : V n →ₗ[ℝ] V n) - 1 with hK
    have hstep : ∀ (i : Fin n) (h : V n), (∀ j, ρ j < ρ i → h j = 0) → K h i = 0 := by
      intro i h hh
      have h1 : HasDerivAt (fun t : ℝ => z + t • h) h 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add z
      have h2 : HasDerivAt (fun t : ℝ => F (z + t • h)) (fderiv ℝ F z h) 0 := by
        exact (hF z).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
      have h3 := (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin n => ℂ) i).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (h2.sub h1)
      have h4 : (fun t : ℝ => F (z + t • h) i - (z + t • h) i) = fun _ => F z i - z i := by
        funext t
        exact htri i _ _ fun j hj => by simp [hh j hj]
      have h5 : HasDerivAt (fun t : ℝ => F (z + t • h) i - (z + t • h) i)
          (fderiv ℝ F z h i - h i) 0 := h3
      rw [h4] at h5
      have := h5.unique (hasDerivAt_const _ _)
      simpa [hK] using this
    have hpow : ∀ (m : ℕ) (h : V n) (i : Fin n), ρ i < m → (K ^ m) h i = 0 := by
      intro m
      induction m with
      | zero => intro h i hi; omega
      | succ m ih =>
        intro h i hi
        rw [pow_succ', Module.End.mul_apply]
        exact hstep i _ fun j hj => ih h j (by omega)
    have hnil : IsNilpotent K := by
      refine ⟨Finset.univ.sup ρ + 1, ?_⟩
      ext h i
      have : ρ i ≤ Finset.univ.sup ρ := Finset.le_sup (Finset.mem_univ i)
      simpa using hpow _ h i (by omega)
    have := det_one_add_of_isNilpotent hnil
    rw [hK, add_sub_cancel] at this
    exact this
  refine ⟨hF.continuous.measurable, ?_⟩
  have := map_withDensity_abs_det_fderiv_eq_addHaar (volume : Measure (V n)) (s := Set.univ)
    (f := F) (f' := fderiv ℝ F) MeasurableSet.univ.nullMeasurableSet
    (fun x _ => (hF x).hasFDerivAt.hasFDerivWithinAt) hb.1.injOn
  simpa [hdet, hb.2.range_eq] using this

/- English proof (translation)
Establish `key : ∀ v : EuclideanSpace ℂ n, star v.ofLp ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v.ofLp) = ((‖v‖ ^ 2 - ‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ)`. Introduce `v`. Establish `e1 : star v.ofLp ⬝ᵥ v.ofLp = ((‖v‖ ^ 2 : ℝ) : ℂ)`. Use `EuclideanSpace.inner_eq_star_dotProduct v v` as an intermediate fact. Rewrite `this` using `[inner_self_eq_norm_sq_to_K]`.

Rewrite using `[dotProduct_comm]`. Use `push_cast`. Conclude with `this.symm`. Establish `e2 : star (Z *ᵥ v.ofLp) ⬝ᵥ (Z *ᵥ v.ofLp) = ((‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ)`. Use `EuclideanSpace.inner_eq_star_dotProduct (Matrix.toEuclideanLin Z v) (Matrix.toEuclideanLin Z v)` as an intermediate fact.

Rewrite `this` using `[inner_self_eq_norm_sq_to_K]`. Rewrite using `[dotProduct_comm]`. Use `push_cast`. Conclude with `this.symm`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, e1, e2, ← Complex.ofReal_sub]`.

Use `set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z) with hT`. Prove the components needed by the constructor for the conclusion. Introduce `hn`. Use `Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)) ?_` and prove the remaining obligations. Introduce `x hx`.

Use `set v : EuclideanSpace ℂ _ := WithLp.toLp 2 x with hv`. Establish `hv0 : 0 < ‖v‖`. Rewrite using `[norm_pos_iff]`. Introduce `h`. Apply `hx` to reduce the goal to its premises.

Simplify `congrArg WithLp.ofLp h` using `[hv]`. Establish `h1 : ‖Matrix.toEuclideanLin Z v‖ ≤ _` using `T.le_opNorm v`. Establish `h2 : ‖Matrix.toEuclideanLin Z v‖ < ‖v‖` using `by nlinarith`. Establish `h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v‖` using `norm_nonneg _`. Use `key v` as an intermediate fact.

Rewrite `this` using `[show v.ofLp = x from rfl]`. Rewrite using `[this]`. Conclude with `Complex.zero_lt_real.2 (by nlinarith)`. Introduce `hpd`. Take `⟨v0, hv0, hmax⟩` from `(isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (T.continuous.norm.continuousOn)`.

Establish `hv1 : ‖v0‖ ≤ 1` using `by simpa using hv0`. Establish `hlt : ‖T v0‖ < 1`. Distinguish the cases in `h0 : v0 = 0`. Simplify using `[h0]`. Establish `hne : v0.ofLp ≠ 0` using `fun h => h0 (by ext i; simpa using congrFun h i)`.

Use `hpd.dotProduct_mulVec_pos hne` as an intermediate fact. Rewrite `this` using `[key, Complex.zero_lt_real]`. Establish `h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v0‖` using `norm_nonneg _`. Establish `h4 : ‖T v0‖ = ‖Matrix.toEuclideanLin Z v0‖` using `rfl`. Rewrite using `[h4]`.

Use polynomial arithmetic with `[norm_nonneg v0]`. Use `lt_of_le_of_lt ?_ hlt` and prove the remaining obligations. Use `ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx => ?_` and prove the remaining obligations. Conclude with `hmax (by simp [hx] : x ∈ Metric.closedBall (0 : EuclideanSpace ℂ n) 1)`.
-/
theorem opNorm_lt_one_iff {m n : Type} [Fintype m] [Fintype n] [DecidableEq n] (Z : Matrix m n ℂ) :
    ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z)‖ < 1 ↔ (1 - Zᴴ * Z).PosDef := by
  have key : ∀ v : EuclideanSpace ℂ n, star v.ofLp ⬝ᵥ ((1 - Zᴴ * Z) *ᵥ v.ofLp) =
      ((‖v‖ ^ 2 - ‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ) := by
    intro v
    have e1 : star v.ofLp ⬝ᵥ v.ofLp = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
      have := EuclideanSpace.inner_eq_star_dotProduct v v
      rw [inner_self_eq_norm_sq_to_K] at this
      rw [dotProduct_comm]; push_cast; exact this.symm
    have e2 : star (Z *ᵥ v.ofLp) ⬝ᵥ (Z *ᵥ v.ofLp) = ((‖Matrix.toEuclideanLin Z v‖ ^ 2 : ℝ) : ℂ) := by
      have := EuclideanSpace.inner_eq_star_dotProduct (Matrix.toEuclideanLin Z v)
        (Matrix.toEuclideanLin Z v)
      rw [inner_self_eq_norm_sq_to_K] at this
      rw [dotProduct_comm]; push_cast; exact this.symm
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, ← Matrix.mulVec_mulVec,
      Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, e1, e2, ← Complex.ofReal_sub]
  set T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Z) with hT
  constructor
  · intro hn
    refine Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_conjTranspose_mul_self Z)) ?_
    intro x hx
    set v : EuclideanSpace ℂ _ := WithLp.toLp 2 x with hv
    have hv0 : 0 < ‖v‖ := by
      rw [norm_pos_iff]; intro h; apply hx
      simpa [hv] using congrArg WithLp.ofLp h
    have h1 : ‖Matrix.toEuclideanLin Z v‖ ≤ _ := T.le_opNorm v
    have h2 : ‖Matrix.toEuclideanLin Z v‖ < ‖v‖ := by nlinarith
    have h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v‖ := norm_nonneg _
    have := key v
    rw [show v.ofLp = x from rfl] at this
    rw [this]
    exact Complex.zero_lt_real.2 (by nlinarith)
  · intro hpd
    obtain ⟨v0, hv0, hmax⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
      ⟨0, Metric.mem_closedBall_self zero_le_one⟩ (T.continuous.norm.continuousOn)
    have hv1 : ‖v0‖ ≤ 1 := by simpa using hv0
    have hlt : ‖T v0‖ < 1 := by
      by_cases h0 : v0 = 0
      · simp [h0]
      · have hne : v0.ofLp ≠ 0 := fun h => h0 (by ext i; simpa using congrFun h i)
        have := hpd.dotProduct_mulVec_pos hne
        rw [key, Complex.zero_lt_real] at this
        have h3 : 0 ≤ ‖Matrix.toEuclideanLin Z v0‖ := norm_nonneg _
        have h4 : ‖T v0‖ = ‖Matrix.toEuclideanLin Z v0‖ := rfl
        rw [h4]
        nlinarith [norm_nonneg v0]
    refine lt_of_le_of_lt ?_ hlt
    refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun x hx => ?_
    exact hmax (by simp [hx] : x ∈ Metric.closedBall (0 : EuclideanSpace ℂ n) 1)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def coordOf (x : Frame X.Ψ r) : V (nd X) := WithLp.toLp 2 fun i =>
  x ((Fintype.equivFin (Ent X)).symm i).1 ((Fintype.equivFin (Ent X)).symm i).2.1.1
    ((Fintype.equivFin (Ent X)).symm i).2.1.2

/- English proof (translation)
Simplify using `[nmat, h, coordOf]`.
-/
theorem nmat_coordOf_of_lt (x : Frame X.Ψ r) (τ : X.Ψ) {a b : Fin r} (h : b < a) :
    nmat X (coordOf X x) τ a b = x τ a b := by
  simp [nmat, h, coordOf]

/- English proof (translation)
Simplify using `[nmat, h]`.
-/
theorem nmat_of_not_lt (z w : V (nd X)) (τ : X.Ψ) {a b : Fin r} (h : ¬ b < a) :
    nmat X z τ a b = nmat X w τ a b := by
  simp [nmat, h]

/- English proof (translation)
Establish `h` using `((Fintype.equivFin (Ent X)).symm i).2.2`. Simplify using `only [nmat, dif_pos h]`. Conclude with `congrArg (fun j => z j) ((Fintype.equivFin (Ent X)).apply_symm_apply i)`.
-/
theorem nmat_apply_idx (z : V (nd X)) (i : Fin (nd X)) :
    nmat X z ((Fintype.equivFin (Ent X)).symm i).1 ((Fintype.equivFin (Ent X)).symm i).2.1.1
      ((Fintype.equivFin (Ent X)).symm i).2.1.2 = z i := by
  have h := ((Fintype.equivFin (Ent X)).symm i).2.2
  simp only [nmat, dif_pos h]
  exact congrArg (fun j => z j) ((Fintype.equivFin (Ent X)).apply_symm_apply i)

/- English proof (translation)
Use extensionality with `i`. Conclude with `nmat_apply_idx X z i`.
-/
theorem coordOf_nmat (z : V (nd X)) : coordOf X (nmat X z) = z := by
  ext i
  exact nmat_apply_idx X z i

/- English proof (translation)
Use `show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = _`. Simplify using `only [zFrame, leviFrame]`. Distinguish the cases in `ha : X.p0 ≤ (a : ℕ)`. Distinguish the cases in `hb : (b : ℕ) < X.p0`. Rewrite using `[if_pos ⟨ha, hb⟩]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hc : (c : ℕ) < X.p0`. Establish `: ¬ X.p0 ≤ (c : ℕ)` using `by omega`. Simplify using `[ha, hb, hc, this]`. Establish `: X.p0 ≤ (c : ℕ)` using `by omega`.

Simplify using `[ha, hb, hc, this]`. Rewrite using `[if_neg (fun h => hb h.2), Finset.sum_eq_single a]`. Establish `: ¬ (a : ℕ) < X.p0` using `by omega`. Simplify using `[hb, this]`. Introduce `c _ hca`.

Distinguish the cases in `hc : (c : ℕ) < X.p0`. Establish `h1 : c < b` using `Fin.lt_def.2 (by omega)`. Establish `h2 : nmat X z τ c b = 0` using `ExF.nM_upper X z τ h1`. Simplify using `[hb, h2]`. Simplify using `[hc, hca.symm]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h => ha h.1), Finset.sum_eq_single a]`. Simplify using `[ha]`. Introduce `c _ hca`. Simplify using `[ha, hca.symm]`.

Simplify using the standard rewrite rules.
-/
theorem nFrame_apply (z : V (nd X)) (τ : X.Ψ) (a b : Fin r) :
    nFrame X z τ a b = if X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
      ∑ c : Fin r, if (c : ℕ) < X.p0 then nmat X z τ a c * nmat X z τ c b else 0
    else nmat X z τ a b := by
  show ∑ c, zFrame X z τ a c * leviFrame X z τ c b = _
  simp only [zFrame, leviFrame]
  by_cases ha : X.p0 ≤ (a : ℕ)
  · by_cases hb : (b : ℕ) < X.p0
    · rw [if_pos ⟨ha, hb⟩]
      refine Finset.sum_congr rfl fun c _ => ?_
      by_cases hc : (c : ℕ) < X.p0
      · have : ¬ X.p0 ≤ (c : ℕ) := by omega
        simp [ha, hb, hc, this]
      · have : X.p0 ≤ (c : ℕ) := by omega
        simp [ha, hb, hc, this]
    · rw [if_neg (fun h => hb h.2), Finset.sum_eq_single a]
      · have : ¬ (a : ℕ) < X.p0 := by omega
        simp [hb, this]
      · intro c _ hca
        by_cases hc : (c : ℕ) < X.p0
        · have h1 : c < b := Fin.lt_def.2 (by omega)
          have h2 : nmat X z τ c b = 0 := ExF.nM_upper X z τ h1
          simp [hb, h2]
        · simp [hc, hca.symm]
      · simp
  · rw [if_neg (fun h => ha h.1), Finset.sum_eq_single a]
    · simp [ha]
    · intro c _ hca
      simp [ha, hca.symm]
    · simp

def toEntries (z : V (nd X)) : V (nd X) := coordOf X (nFrame X z)

def ofEntries (w : V (nd X)) : V (nd X) := coordOf X fun τ a b =>
  if h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0 then
    ExF.Zt X w τ ⟨b, h.2⟩ ⟨a - X.p0, by have := a.isLt; omega⟩
  else nmat X w τ a b

/- English proof (translation)
Use function extensionality and compare the values at `τ a b`. Distinguish the cases in `h : b < a`. Conclude with `nmat_coordOf_of_lt X _ τ h`. Establish `: ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0)` using `fun h' => h (Fin.lt_def.2 (by omega))`. Rewrite using `[nFrame_apply, if_neg this]`.

Conclude with `nmat_of_not_lt X _ _ τ h`.
-/
theorem nmat_toEntries (z : V (nd X)) : nmat X (toEntries X z) = nFrame X z := by
  funext τ a b
  by_cases h : b < a
  · exact nmat_coordOf_of_lt X _ τ h
  · have : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0) := fun h' => h (Fin.lt_def.2 (by omega))
    rw [nFrame_apply, if_neg this]
    exact nmat_of_not_lt X _ _ τ h

/- English proof (translation)
Rewrite using `[nmat_toEntries, nFrame_apply, if_neg h]`.
-/
theorem nmat_toEntries_of_not (z : V (nd X)) (τ : X.Ψ) {a b : Fin r}
    (h : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0)) : nmat X (toEntries X z) τ a b = nmat X z τ a b := by
  rw [nmat_toEntries, nFrame_apply, if_neg h]

/- English proof (translation)
Distinguish the cases in `h' : b < a`. Rewrite using `[ofEntries, nmat_coordOf_of_lt X _ τ h', dif_neg h]`. Conclude with `nmat_of_not_lt X _ _ τ h'`.
-/
theorem nmat_ofEntries_of_not (w : V (nd X)) (τ : X.Ψ) {a b : Fin r}
    (h : ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0)) : nmat X (ofEntries X w) τ a b = nmat X w τ a b := by
  by_cases h' : b < a
  · rw [ofEntries, nmat_coordOf_of_lt X _ τ h', dif_neg h]
  · exact nmat_of_not_lt X _ _ τ h'

/- English proof (translation)
Use extensionality with `a b`. Use `nmat_toEntries_of_not X z τ fun h => ?_` and prove the remaining obligations. Use `a.isLt` as an intermediate fact. Establish `h1 : X.p0 ≤ (a : ℕ)` using `h.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem leadingBlock_blockCoordsToLowerEntries (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (toEntries X z) τ = ExF.n1 X z τ := by
  ext a b
  refine nmat_toEntries_of_not X z τ fun h => ?_
  have := a.isLt; have h1 : X.p0 ≤ (a : ℕ) := h.1; omega

/- English proof (translation)
Use extensionality with `a b`. Use `nmat_ofEntries_of_not X z τ fun h => ?_` and prove the remaining obligations. Use `a.isLt` as an intermediate fact. Establish `h1 : X.p0 ≤ (a : ℕ)` using `h.1`. Use linear arithmetic over natural numbers and integers.
-/
theorem leadingBlock_lowerEntriesToBlockCoords (z : V (nd X)) (τ : X.Ψ) : ExF.n1 X (ofEntries X z) τ = ExF.n1 X z τ := by
  ext a b
  refine nmat_ofEntries_of_not X z τ fun h => ?_
  have := a.isLt; have h1 : X.p0 ≤ (a : ℕ) := h.1; omega

/- English proof (translation)
Use extensionality with `m b`. Use `show nmat X (toEntries X z) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _`. Establish `h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0` using `⟨Nat.le_add_right _ _, b.isLt⟩`. Rewrite using `[nmat_toEntries, nFrame_apply, if_pos h, ExF.sum_split X, Matrix.mul_apply]`. Establish `h2 : ∀ k : Fin (r - X.p0), ¬ ((ExF.qI X k : Fin r) : ℕ) < X.p0` using `fun k => not_lt.2 (Nat.le_add_right _ _)`.

Simplify using `only [h2, if_false, Finset.sum_const_zero, add_zero]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos (show ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 from c.isLt)]`. Both sides reduce to the same expression.
-/
theorem Wm_toEntries (z : V (nd X)) (τ : X.Ψ) :
    ExF.Wm X (toEntries X z) τ = ExF.Wm X z τ * ExF.n1 X z τ := by
  ext m b
  show nmat X (toEntries X z) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _
  have h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 :=
    ⟨Nat.le_add_right _ _, b.isLt⟩
  rw [nmat_toEntries, nFrame_apply, if_pos h, ExF.sum_split X, Matrix.mul_apply]
  have h2 : ∀ k : Fin (r - X.p0), ¬ ((ExF.qI X k : Fin r) : ℕ) < X.p0 := fun k =>
    not_lt.2 (Nat.le_add_right _ _)
  simp only [h2, if_false, Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [if_pos (show ((Fin.castLE X.p0_le c : Fin r) : ℕ) < X.p0 from c.isLt)]
  rfl

/- English proof (translation)
Use extensionality with `m b`. Use `show nmat X (ofEntries X w) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _`. Establish `h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0` using `⟨Nat.le_add_right _ _, b.isLt⟩`. Rewrite using `[ofEntries, nmat_coordOf_of_lt X _ τ (Fin.lt_def.2 (by omega)), dif_pos h]`. Establish `: (⟨(ExF.qI X m : ℕ) - X.p0, by have` using `(ExF.qI X m).isLt; omega⟩ : Fin (r - X.p0)) = m := Fin.ext (by simp [ExF.qI])`.

Rewrite using `[this]`. Both sides reduce to the same expression.
-/
theorem Wm_ofEntries (w : V (nd X)) (τ : X.Ψ) :
    ExF.Wm X (ofEntries X w) τ = ExF.Wm X w τ * (ExF.n1 X w τ)⁻¹ := by
  ext m b
  show nmat X (ofEntries X w) τ (ExF.qI X m) (Fin.castLE X.p0_le b) = _
  have h : X.p0 ≤ ((ExF.qI X m : Fin r) : ℕ) ∧ ((Fin.castLE X.p0_le b : Fin r) : ℕ) < X.p0 :=
    ⟨Nat.le_add_right _ _, b.isLt⟩
  rw [ofEntries, nmat_coordOf_of_lt X _ τ (Fin.lt_def.2 (by omega)), dif_pos h]
  have : (⟨(ExF.qI X m : ℕ) - X.p0, by have := (ExF.qI X m).isLt; omega⟩ : Fin (r - X.p0)) = m :=
    Fin.ext (by simp [ExF.qI])
  rw [this]
  rfl

/- English proof (translation)
Rewrite using `[← coordOf_nmat X z, ← coordOf_nmat X w]`. Use `congr 1`. Use function extensionality and compare the values at `τ a b`. Distinguish the cases in `h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0`. Use `congrFun (congrFun (h2 τ) ⟨a - X.p0, by have := a.isLt; omega⟩) ⟨b, h.2⟩` as an intermediate fact.

Establish `e : ExF.qI X ⟨a - X.p0, by have` using `a.isLt; omega⟩ = a := Fin.ext (by simp [ExF.qI]; omega)`. Simplify using `only [ExF.Wm, Matrix.submatrix_apply, e] at this`. Conclude with `this`. Conclude with `h1 τ a b h`.
-/
theorem ext_blocks {z w : V (nd X)}
    (h1 : ∀ τ (a b : Fin r), ¬ (X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0) → nmat X z τ a b = nmat X w τ a b)
    (h2 : ∀ τ, ExF.Wm X z τ = ExF.Wm X w τ) : z = w := by
  rw [← coordOf_nmat X z, ← coordOf_nmat X w]
  congr 1
  funext τ a b
  by_cases h : X.p0 ≤ (a : ℕ) ∧ (b : ℕ) < X.p0
  · have := congrFun (congrFun (h2 τ) ⟨a - X.p0, by have := a.isLt; omega⟩) ⟨b, h.2⟩
    have e : ExF.qI X ⟨a - X.p0, by have := a.isLt; omega⟩ = a := Fin.ext (by simp [ExF.qI]; omega)
    simp only [ExF.Wm, Matrix.submatrix_apply, e] at this
    exact this
  · exact h1 τ a b h

/- English proof (translation)
Rewrite using `[ExF.det_unipotentFrame_eq_one]`. Conclude with `isUnit_one`.
-/
theorem isUnit_det_leadingBlock_lowerEntries (z : V (nd X)) (τ : X.Ψ) : IsUnit (ExF.n1 X z τ).det := by
  rw [ExF.det_unipotentFrame_eq_one]; exact isUnit_one

def coordEquiv : V (nd X) ≃ V (nd X) where
  toFun := toEntries X
  invFun := ofEntries X
  left_inv z := ext_blocks X
    (fun τ a b h => by rw [nmat_ofEntries_of_not X _ τ h, nmat_toEntries_of_not X _ τ h])
    (fun τ => by
      rw [Wm_ofEntries, Wm_toEntries, leadingBlock_blockCoordsToLowerEntries, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ)])
  right_inv z := ext_blocks X
    (fun τ a b h => by rw [nmat_toEntries_of_not X _ τ h, nmat_ofEntries_of_not X _ τ h])
    (fun τ => by
      rw [Wm_toEntries, Wm_ofEntries, leadingBlock_lowerEntriesToBlockCoords, Matrix.nonsing_inv_mul_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ)])

/- English proof (translation)
Rewrite using `[contDiff_piLp]`. Introduce `i`. Conclude with `hf _ _ _`.
-/
theorem contDiff_coordOf {f : V (nd X) → Frame X.Ψ r}
    (hf : ∀ τ a b, ContDiff ℂ ∞ fun z => f z τ a b) : ContDiff ℂ ∞ fun z => coordOf X (f z) := by
  rw [contDiff_piLp]
  intro i
  exact hf _ _ _

/- English proof (translation)
Use `contDiff_coordOf X fun τ a b => ?_` and prove the remaining obligations. Simplify using `only [nFrame_apply]`. Use `split_ifs`. Use `ContDiff.sum fun c _ => ?_ split_ifs` and prove the remaining obligations. Conclude with `(ExF.cd_nM X τ a c).mul (ExF.cd_nM X τ c b)`.

Conclude with `contDiff_const`. Conclude with `ExF.cd_nM X τ a b`.
-/
theorem contDiff_toEntries : ContDiff ℂ ∞ (toEntries X) := by
  refine contDiff_coordOf X fun τ a b => ?_
  simp only [nFrame_apply]
  split_ifs
  · refine ContDiff.sum fun c _ => ?_
    split_ifs
    · exact (ExF.cd_nM X τ a c).mul (ExF.cd_nM X τ c b)
    · exact contDiff_const
  · exact ExF.cd_nM X τ a b

/- English proof (translation)
Use `contDiff_coordOf X fun τ a b => ?_` and prove the remaining obligations. Use `split_ifs`. Conclude with `ExF.cd_Zt X τ _ _`. Conclude with `ExF.cd_nM X τ a b`.
-/
theorem contDiff_ofEntries : ContDiff ℂ ∞ (ofEntries X) := by
  refine contDiff_coordOf X fun τ a b => ?_
  split_ifs
  · exact ExF.cd_Zt X τ _ _
  · exact ExF.cd_nM X τ a b

/- English proof (translation)
Use `measurePreserving_of_triangular _ (((contDiff_toEntries X).restrict_scalars ℝ).differentiable (by simp)) (coordEquiv X).bijective (fun i => (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) - (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ)) ?_` and prove the remaining obligations. Introduce `i z w h`. Rewrite using `[← nmat_apply_idx X z i, ← nmat_apply_idx X w i]`. Simplify using `only [toEntries, coordOf, nFrame_apply]`. Generalize the expression as in `(Fintype.equivFin (Ent X)).symm i = e at h ⊢`.

Take `⟨τ, ⟨a, b⟩, hab⟩` from `e`. Establish `hab' : (b : ℕ) < a` using `hab`. Establish `h' : ∀ c d : Fin r, (c : ℕ) - d < (a : ℕ) - b → nmat X z τ c d = nmat X w τ c d`. Introduce `c d hcd`. Distinguish the cases in `hl : d < c`.

Simplify using `only [nmat, dif_pos hl]`. Apply `h` to reduce the goal to its premises. Simplify using `using hcd`. Conclude with `nmat_of_not_lt X _ _ τ hl`. Simplify using `only`.

Use `split_ifs with hW`. Establish `hs : ∀ y : V (nd X), (∑ c : Fin r, if (c : ℕ) < X.p0 then nmat X y τ a c * nmat X y τ c b else 0) - nmat X y τ a b = ∑ c ∈ Finset.univ.erase b, if (c : ℕ) < X.p0 then nmat X y τ a c * nmat X y τ c b else 0`. Introduce `y`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ b), if_pos hW.2, show nmat X y τ b b = 1 from ExF.nM_diag X y τ b]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hs, hs]`. Use `Finset.sum_congr rfl fun c hc => ?_` and prove the remaining obligations. Use `split_ifs with hcp`. Break down `lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hcb | hcb` into its components or cases. Rewrite using `[show nmat X z τ c b = 0 from ExF.nM_upper X z τ hcb, show nmat X w τ c b = 0 from ExF.nM_upper X w τ hcb, mul_zero, mul_zero]`.

Establish `hcb' : (b : ℕ) < c` using `hcb`. Rewrite using `[h' a c (by omega), h' c b (by omega)]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules.
-/
theorem measurePreserving_toEntries : MeasurePreserving (toEntries X) volume volume := by
  refine measurePreserving_of_triangular _
    (((contDiff_toEntries X).restrict_scalars ℝ).differentiable (by simp)) (coordEquiv X).bijective
    (fun i => (((Fintype.equivFin (Ent X)).symm i).2.1.1 : ℕ) -
      (((Fintype.equivFin (Ent X)).symm i).2.1.2 : ℕ)) ?_
  intro i z w h
  rw [← nmat_apply_idx X z i, ← nmat_apply_idx X w i]
  simp only [toEntries, coordOf, nFrame_apply]
  generalize (Fintype.equivFin (Ent X)).symm i = e at h ⊢
  obtain ⟨τ, ⟨a, b⟩, hab⟩ := e
  have hab' : (b : ℕ) < a := hab
  have h' : ∀ c d : Fin r, (c : ℕ) - d < (a : ℕ) - b → nmat X z τ c d = nmat X w τ c d := by
    intro c d hcd
    by_cases hl : d < c
    · simp only [nmat, dif_pos hl]
      apply h
      simpa using hcd
    · exact nmat_of_not_lt X _ _ τ hl
  dsimp only
  split_ifs with hW
  · have hs : ∀ y : V (nd X), (∑ c : Fin r, if (c : ℕ) < X.p0 then nmat X y τ a c * nmat X y τ c b else 0)
        - nmat X y τ a b = ∑ c ∈ Finset.univ.erase b,
          if (c : ℕ) < X.p0 then nmat X y τ a c * nmat X y τ c b else 0 := by
      intro y
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), if_pos hW.2,
        show nmat X y τ b b = 1 from ExF.nM_diag X y τ b]
      ring
    rw [hs, hs]
    refine Finset.sum_congr rfl fun c hc => ?_
    split_ifs with hcp
    · rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hc) with hcb | hcb
      · rw [show nmat X z τ c b = 0 from ExF.nM_upper X z τ hcb,
          show nmat X w τ c b = 0 from ExF.nM_upper X w τ hcb, mul_zero, mul_zero]
      · have hcb' : (b : ℕ) < c := hcb
        rw [h' a c (by omega), h' c b (by omega)]
    · rfl
  · simp

/- English proof (translation)
Rewrite using `[cpt, nmat_toEntries, point]`.
-/
theorem cpt_toEntries (x0 : Base X) (z : V (nd X)) :
    cpt X x0.1 (toEntries X z) = point X x0 z := by
  rw [cpt, nmat_toEntries, point]

def lowEquiv : Fin X.p0 ≃ {b : Fin r // (b : ℕ) < X.p0} where
  toFun c := ⟨Fin.castLE X.p0_le c, c.isLt⟩
  invFun b := ⟨b.1, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def highEquiv : Fin (r - X.p0) ≃ {a : Fin r // X.p0 ≤ (a : ℕ)} where
  toFun m := ⟨ExF.qI X m, Nat.le_add_right _ _⟩
  invFun a := ⟨a.1 - X.p0, by have := a.1.isLt; have := a.2; omega⟩
  left_inv m := Fin.ext (by simp [ExF.qI])
  right_inv a := Subtype.ext (Fin.ext (by have := a.2; simp [ExF.qI]; omega))

/- English proof (translation)
Establish `hW : ExF.Wm X z τ = (zBlock X z τ).submatrix (highEquiv X) (lowEquiv X)` using `rfl`. Establish `h1 : ((zBlock X z τ)ᴴ * zBlock X z τ).submatrix (lowEquiv X) (lowEquiv X) = (ExF.Wm X z τ)ᴴ * ExF.Wm X z τ`. Rewrite using `[hW, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]`. Rewrite using `[ExF.Am, ExF.Zt, Wm_toEntries, leadingBlock_blockCoordsToLowerEntries, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ), Matrix.submatrix_sub]`. Simplify using `only [Pi.sub_apply, Matrix.submatrix_one_equiv, h1, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul]`.

Both sides reduce to the same expression.
-/
theorem Am_toEntries (z : V (nd X)) (τ : X.Ψ) :
    ExF.Am X (toEntries X z) τ =
      ((1 - (zBlock X z τ)ᴴ * zBlock X z τ).submatrix (lowEquiv X) (lowEquiv X))ᵀ := by
  have hW : ExF.Wm X z τ = (zBlock X z τ).submatrix (highEquiv X) (lowEquiv X) := rfl
  have h1 : ((zBlock X z τ)ᴴ * zBlock X z τ).submatrix (lowEquiv X) (lowEquiv X) =
      (ExF.Wm X z τ)ᴴ * ExF.Wm X z τ := by
    rw [hW, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [ExF.Am, ExF.Zt, Wm_toEntries, leadingBlock_blockCoordsToLowerEntries,
    Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_leadingBlock_lowerEntries X z τ), Matrix.submatrix_sub]
  simp only [Pi.sub_apply, Matrix.submatrix_one_equiv, h1, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_mul]
  rfl

/- English proof (translation)
Rewrite using `[ExF.mem_OmF_iff X x0.1 x0.2]`. Use `forall_congr' fun τ => ?_` and prove the remaining obligations. Rewrite using `[Am_toEntries, zNorm, opNorm_lt_one_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Simplify using `using h.transpose.submatrix (e := (lowEquiv X).symm) (lowEquiv X).symm.injective`. Introduce `h`. Conclude with `(h.submatrix (lowEquiv X).injective).transpose`.
-/
theorem toEntries_mem_OmF_iff (x0 : Base X) (z : V (nd X)) :
    toEntries X z ∈ OmF X x0.1 ↔ z ∈ Om X := by
  rw [ExF.mem_OmF_iff X x0.1 x0.2]
  refine forall_congr' fun τ => ?_
  rw [Am_toEntries, zNorm, opNorm_lt_one_iff]
  constructor
  · intro h
    simpa using h.transpose.submatrix (e := (lowEquiv X).symm) (lowEquiv X).symm.injective
  · intro h
    exact (h.submatrix (lowEquiv X).injective).transpose

/- English proof (translation)
Rewrite using `[ExF.rhF_eq_sum X x0.1 x0.2, rho, ← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `h` using `(ExF.mem_OmF_iff X x0.1 x0.2 _).1 ((toEntries_mem_OmF_iff X x0 z).2 hz) τ`. Rewrite using `[ExF.norm_of_pos h.det_pos, Am_toEntries, Matrix.det_transpose, Matrix.det_submatrix_equiv_self, zDet]`.
-/
theorem rhF_toEntries (x0 : Base X) {z : V (nd X)} (hz : z ∈ Om X) :
    rhF X x0.1 (toEntries X z) = rho X z := by
  rw [ExF.rhF_eq_sum X x0.1 x0.2, rho, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have h := (ExF.mem_OmF_iff X x0.1 x0.2 _).1 ((toEntries_mem_OmF_iff X x0 z).2 hz) τ
  rw [ExF.norm_of_pos h.det_pos, Am_toEntries, Matrix.det_transpose, Matrix.det_submatrix_equiv_self,
    zDet]

/- English proof (translation)
Simplify using `only [densF, density, cpt_toEntries, zpow_neg, zpow_ofNat]`.
-/
theorem densF_toEntries (x0 : Base X) (z : V (nd X)) :
    densF X x0.1 (toEntries X z) = density X x0 z := by
  simp only [densF, density, cpt_toEntries, zpow_neg, zpow_ofNat]

/- English proof (translation)
Set `e : V (nd X) ≃ᵐ V (nd X)` to `{ coordEquiv X with measurable_toFun := (contDiff_toEntries X).continuous.measurable measurable_invFun := (contDiff_ofEntries X).continuous.measurable }`. Establish `hpre : Om X = toEntries X ⁻¹' OmF X x0.1`. Use extensionality with `z`. Conclude with `(toEntries_mem_OmF_iff X x0 z).symm`. Establish `hmp : MeasurePreserving e (volume.restrict (Om X)) (volume.restrict (OmF X x0.1))`.

Rewrite using `[hpre]`. Conclude with `(measurePreserving_toEntries X).restrict_preimage (ExF.isOpen_OmF X x0.1).measurableSet`. Use `show Measure.map e (mu X x0) = _`. Use extensionality with `s hs`. Rewrite using `[e.map_apply, mu, muF, withDensity_apply _ hs, withDensity_apply _ (e.measurable hs), ← (hmp.restrict_preimage hs).lintegral_comp_emb e.measurableEmbedding]`.

Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[← densF_toEntries]`. Both sides reduce to the same expression.
-/
theorem map_mu (x0 : Base X) : Measure.map (toEntries X) (mu X x0) = muF X x0.1 := by
  let e : V (nd X) ≃ᵐ V (nd X) :=
    { coordEquiv X with
      measurable_toFun := (contDiff_toEntries X).continuous.measurable
      measurable_invFun := (contDiff_ofEntries X).continuous.measurable }
  have hpre : Om X = toEntries X ⁻¹' OmF X x0.1 := by
    ext z; exact (toEntries_mem_OmF_iff X x0 z).symm
  have hmp : MeasurePreserving e (volume.restrict (Om X)) (volume.restrict (OmF X x0.1)) := by
    rw [hpre]
    exact (measurePreserving_toEntries X).restrict_preimage (ExF.isOpen_OmF X x0.1).measurableSet
  show Measure.map e (mu X x0) = _
  ext s hs
  rw [e.map_apply, mu, muF, withDensity_apply _ hs, withDensity_apply _ (e.measurable hs),
    ← (hmp.restrict_preimage hs).lintegral_comp_emb e.measurableEmbedding]
  refine lintegral_congr fun z => ?_
  rw [← densF_toEntries]
  rfl

end

end GlobalTheory.UpCoordCompare
