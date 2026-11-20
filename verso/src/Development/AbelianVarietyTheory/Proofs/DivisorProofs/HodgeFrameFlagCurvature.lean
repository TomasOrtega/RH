import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HermitianCurvatureForms

open Matrix Complex ComplexConjugate GlobalTheory.HermFrame GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeHoriz

/- English proof (translation)
Use extensionality with `k l`. Rewrite using `[one_apply, ← h k l, form_eq_sum]`. Simplify using `only [mul_apply, Finset.sum_mul, transpose_apply, conjTranspose_apply, star_def]`. Rewrite using `[Finset.sum_comm]`.
-/
theorem gram_eq_one {n : ℕ} {H e : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ k l, form H (fun a => e a k) (fun a => e a l) = if k = l then 1 else 0) :
    eᵀ * H * eᴴᵀ = 1 := by
  ext k l
  rw [one_apply, ← h k l, form_eq_sum]
  simp only [mul_apply, Finset.sum_mul, transpose_apply, conjTranspose_apply, star_def]
  rw [Finset.sum_comm]

/- English proof (translation)
Establish `h1 : H * eᴴᵀ * eᵀ = 1`. Use `gram_eq_one h` as an intermediate fact. Rewrite `this` using `[Matrix.mul_assoc]`. Conclude with `mul_eq_one_comm.1 this`. Establish `h2 : ∀ i, form H (M *ᵥ fun a => e a i) (fun a => e a i) = ((M * e)ᵀ * H * eᴴᵀ) i i`.

Introduce `i`. Rewrite using `[form_eq_sum]`. Simplify using `only [mul_apply, Finset.sum_mul, transpose_apply, conjTranspose_apply, star_def, mulVec, dotProduct]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [h2]`.

Express the relevant statement in the definitionally equal form `((M * e)ᵀ * H * eᴴᵀ).trace = _`. Rewrite using `[transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, h1, Matrix.mul_one, trace_transpose]`.
-/
theorem sum_form_eq_trace {n : ℕ} {H e : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ k l, form H (fun a => e a k) (fun a => e a l) = if k = l then 1 else 0)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    ∑ i, form H (M *ᵥ fun a => e a i) (fun a => e a i) = M.trace := by
  have h1 : H * eᴴᵀ * eᵀ = 1 := by
    have := gram_eq_one h
    rw [Matrix.mul_assoc] at this
    exact mul_eq_one_comm.1 this
  have h2 : ∀ i, form H (M *ᵥ fun a => e a i) (fun a => e a i) = ((M * e)ᵀ * H * eᴴᵀ) i i := by
    intro i
    rw [form_eq_sum]
    simp only [mul_apply, Finset.sum_mul, transpose_apply, conjTranspose_apply, star_def, mulVec,
      dotProduct]
    rw [Finset.sum_comm]
  simp only [h2]
  change ((M * e)ᵀ * H * eᴴᵀ).trace = _
  rw [transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc,
    h1, Matrix.mul_one, trace_transpose]

/- English proof (translation)
Establish `h0 : B * e = 0`. Use extensionality with `a i`. Conclude with `congrFun (hB i) a`. Establish `h1 : e * (H * eᴴᵀ)ᵀ = 1`. Use `gram_eq_one h` as an intermediate fact.

Rewrite `this` using `[Matrix.mul_assoc]`. Use `congrArg transpose (mul_eq_one_comm.1 this)` as an intermediate fact. Rewrite `this` using `[transpose_mul, transpose_transpose, transpose_one]`. Then use the resulting hypothesis. Rewrite using `[← Matrix.mul_one B, ← h1, ← Matrix.mul_assoc, h0, Matrix.zero_mul]`.
-/
theorem eq_zero_of_cols {n m : ℕ} {H e : Matrix (Fin n) (Fin n) ℂ}
    (h : ∀ k l, form H (fun a => e a k) (fun a => e a l) = if k = l then 1 else 0)
    {B : Matrix (Fin m) (Fin n) ℂ} (hB : ∀ i, (B *ᵥ fun a => e a i) = 0) : B = 0 := by
  have h0 : B * e = 0 := by
    ext a i
    exact congrFun (hB i) a
  have h1 : e * (H * eᴴᵀ)ᵀ = 1 := by
    have := gram_eq_one h
    rw [Matrix.mul_assoc] at this
    have := congrArg transpose (mul_eq_one_comm.1 this)
    rwa [transpose_mul, transpose_transpose, transpose_one] at this
  rw [← Matrix.mul_one B, ← h1, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

/- English proof (translation)
Establish `key : (∑ j, y j) * (∑ i, l i * x i - ∑ j, m j * y j) = ∑ i, ∑ j, (l i - m j) * (x i * y j)`. Rewrite using `[mul_sub]`. Use `nth_rewrite 2 [← hs]`. Rewrite using `[mul_comm, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← Finset.sum_sub_distrib]`. Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Establish `hterm : ∀ i j, 0 ≤ (l i - m j) * (x i * y j)` using `fun i j => mul_nonneg (sub_nonneg.2 (hl i j)) (mul_nonneg (hx i) (hy j))`. Establish `hS : 0 ≤ ∑ j, y j` using `Finset.sum_nonneg fun j _ => hy j`. Prove the components needed by the constructor for the conclusion.

Break down `hS.eq_or_lt with h0 | h0` into its components or cases. Establish `hy0 : ∀ j, y j = 0` using `fun j => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hy j).1 h0.symm j (Finset.mem_univ _)`. Establish `hx0 : ∀ i, x i = 0` using `fun i => (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx j).1 (hs.trans h0.symm) i (Finset.mem_univ _)`. Simplify using `[hx0, hy0]`. Use `le_of_mul_le_mul_left ?_ h0` and prove the remaining obligations.

Rewrite using `[mul_zero, key]`. Conclude with `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j`. Introduce and unpack `hlt ⟨j, hj⟩`. Establish `hj' : 0 < y j` using `(hy j).lt_of_ne' hj`. Establish `h0 : 0 < ∑ j, y j` using `Finset.sum_pos' (fun j _ => hy j) ⟨j, Finset.mem_univ _, hj'⟩`.

Take `⟨i, -, hi⟩` from `Finset.exists_ne_zero_of_sum_ne_zero (hs.trans_gt h0).ne'`. Establish `hi' : 0 < x i` using `(hx i).lt_of_ne' hi`. Use `(mul_pos_iff_of_pos_left h0).1 ?_` and prove the remaining obligations. Rewrite using `[key]`. Use `Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hterm i j) ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ => hterm i j) ⟨j, Finset.mem_univ _, ?_⟩⟩` and prove the remaining obligations.

Conclude with `mul_pos (sub_pos.2 (hlt i j)) (mul_pos hi' hj')`.
-/
theorem weighted_sub {p q : ℕ} (x l : Fin p → ℝ) (y m : Fin q → ℝ) (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ j, 0 ≤ y j) (hs : ∑ i, x i = ∑ j, y j) (hl : ∀ i j, m j ≤ l i) :
    0 ≤ ∑ i, l i * x i - ∑ j, m j * y j ∧
      ((∀ i j, m j < l i) → (∃ j, y j ≠ 0) → 0 < ∑ i, l i * x i - ∑ j, m j * y j) := by
  have key : (∑ j, y j) * (∑ i, l i * x i - ∑ j, m j * y j) =
      ∑ i, ∑ j, (l i - m j) * (x i * y j) := by
    rw [mul_sub]
    nth_rewrite 2 [← hs]
    rw [mul_comm, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hterm : ∀ i j, 0 ≤ (l i - m j) * (x i * y j) := fun i j =>
    mul_nonneg (sub_nonneg.2 (hl i j)) (mul_nonneg (hx i) (hy j))
  have hS : 0 ≤ ∑ j, y j := Finset.sum_nonneg fun j _ => hy j
  constructor
  · rcases hS.eq_or_lt with h0 | h0
    · have hy0 : ∀ j, y j = 0 := fun j =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hy j).1 h0.symm j (Finset.mem_univ _)
      have hx0 : ∀ i, x i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hx j).1 (hs.trans h0.symm) i
          (Finset.mem_univ _)
      simp [hx0, hy0]
    · refine le_of_mul_le_mul_left ?_ h0
      rw [mul_zero, key]
      exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm i j
  · rintro hlt ⟨j, hj⟩
    have hj' : 0 < y j := (hy j).lt_of_ne' hj
    have h0 : 0 < ∑ j, y j := Finset.sum_pos' (fun j _ => hy j) ⟨j, Finset.mem_univ _, hj'⟩
    obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hs.trans_gt h0).ne'
    have hi' : 0 < x i := (hx i).lt_of_ne' hi
    refine (mul_pos_iff_of_pos_left h0).1 ?_
    rw [key]
    refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ => hterm i j)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun j _ => hterm i j) ⟨j, Finset.mem_univ _, ?_⟩⟩
    exact mul_pos (sub_pos.2 (hlt i j)) (mul_pos hi' hj')

/- English proof (translation)
Establish `: -I * horizForm H π e lam y ξ ξ = ((-((2 * Real.pi)⁻¹ * ∑ i, lam i * x i) : ℝ) : ℂ)`. Simplify using `only [horizForm, hx, kappa]`. Use `push_cast`. Take the linear combination `((2 * (Real.pi : ℂ))⁻¹ * ∑ i, (lam i : ℂ) * x i) * I_mul_I`. Rewrite using `[diagVal, this, ofReal_re]`.
-/
theorem diagVal_horizForm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {ι : Type}
    [Fintype ι] {n : ℕ} (H : (ι → ℂ) → Matrix (Fin n) (Fin n) ℂ) (π : E → ι → ℂ)
    (e : E → Matrix (Fin n) (Fin n) ℂ) (lam : Fin n → ℝ) (y ξ : E) (x : Fin n → ℝ)
    (hx : ∀ i, curvDiag H π e i y ξ ξ = x i) :
    diagVal (horizForm H π e lam y) ξ = -((2 * Real.pi)⁻¹ * ∑ i, lam i * x i) := by
  have : -I * horizForm H π e lam y ξ ξ =
      ((-((2 * Real.pi)⁻¹ * ∑ i, lam i * x i) : ℝ) : ℂ) := by
    simp only [horizForm, hx, kappa]
    push_cast
    linear_combination ((2 * (Real.pi : ℂ))⁻¹ * ∑ i, (lam i : ℂ) * x i) * I_mul_I
  rw [diagVal, this, ofReal_re]

/- English proof (translation)
Introduce `hSQ E _ _ _ _ _ ι _ p q U ψ a b Y π AW eW Aω eω hψ ha hb hF _ hW hω y hy lam hlam ξ`. Establish `hz : π y ∈ U` using `hF.mapsTo hy`. Establish `hu : ∀ z ∈ U, IsUnit (subGram (ψ z)).det` using `fun z hz => by`. Use `(isUnit_iff_isUnit_det _).1 (hψ.neg_sub z hz).isUnit` as an intermediate fact. Rewrite `this` using `[det_neg]`.

Conclude with `isUnit_of_mul_isUnit_right this`. Take `⟨hS, hQ, hat⟩` from `(hSQ (ι → ℂ) (Fin q) (Fin p) U ψ).1 hψ.isHermFrame hu`. Take `⟨-, -, hadj, -, hcS, hcQ⟩` from `hat _ hz`. Use `set v := fderiv ℂ π y ξ with hv`. Use `set B := secondForm ψ (π y) v with hB`.

Use `set B' := secondFormAdj ψ (π y) v with hB'`. Establish `hh` using `hψ.isHermFrame.herm _ hz`. Establish `cW : curv (fun x => (a : ℂ) • quotGram (ψ x)) (π y) v v = B * B'`. Use `curv_smul (f := fun _ => a) contDiffAt_const ha.ne' (hQ.two hz) (hQ.isUnit _ hz) v v` as an intermediate fact. Rewrite `this` using `[hcQ, hψ.flat _ hz]`.

Use `this.trans ?_` and prove the remaining obligations. Simplify using `[blockQQ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.wedgeHolAnti, hB, hB']`. Establish `cω : curv (fun x => (b : ℂ) • -subGram (ψ x)) (π y) v v = -(B' * B)`. Use `curv_smul (f := fun _ => -b) contDiffAt_const (neg_ne_zero.2 hb.ne') (hS.two hz) (hS.isUnit _ hz) v v` as an intermediate fact. Rewrite `this` using `[hcS, hψ.flat _ hz]`.

Establish `e : (fun x => (b : ℂ) • -subGram (ψ x)) = fun x => ((-b : ℝ) : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS ψ x`. Use function extensionality and compare the values at `x`. Simplify using `[GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS]`. Rewrite using `[e]`. Use `this.trans ?_` and prove the remaining obligations.

Simplify using `[blockSS, GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.wedgeAntiHol, hB, hB']`. Establish `pS` using `hψ.neg_sub _ hz`. Establish `pQ` using `hψ.pos_quot _ hz`. Establish `fneg : ∀ s t, form (-subGram (ψ (π y))) s t = -form (subGram (ψ (π y))) s t` using `fun s t => by`. Simplify using `[form, neg_mulVec]`.

Use `set x : Fin p → ℝ := fun i => a * gnorm (-subGram (ψ (π y))) (B' *ᵥ fun c => eW y c i) ^ 2 with hxd`. Use `set w : Fin q → ℝ := fun j => b * gnorm (quotGram (ψ (π y))) (B *ᵥ fun c => eω y c j) ^ 2 with hwd`. Establish `hX : ∀ i, curvDiag (fun x => (a : ℂ) • quotGram (ψ x)) π eW i y ξ ξ = ((-x i : ℝ) : ℂ)`. Introduce `i`. Rewrite using `[curvDiag, ← hv, cW, form_smul, ← mulVec_mulVec, hB, form_secondForm hh (hu _ hz), ← hB', hxd, ofReal_neg, ofReal_mul, ← form_self pS.posSemidef, fneg]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hY : ∀ j, curvDiag (fun x => (b : ℂ) • -subGram (ψ x)) π eω j y ξ ξ = (w j : ℂ)`. Introduce `j`. Rewrite using `[curvDiag, ← hv, cω, form_smul, fneg, hB, hB', form_secondFormAdj_mul hh (hu _ hz), ← hB, hwd, ofReal_mul, ← form_self pQ.posSemidef, neg_neg]`. Establish `hsum : ∑ i, x i = ∑ j, w j`.

Establish `h1` using `sum_form_eq_trace (hW.unitary y hy) (B * B')`. Establish `h2` using `sum_form_eq_trace (hω.unitary y hy) (-(B' * B))`. Rewrite `h1` using `[← cW]`. Rewrite `h2` using `[← cω]`. Establish `h1' : ∑ i, ((-x i : ℝ) : ℂ) = (B * B').trace`.

Rewrite using `[← cW, ← h1]`. Conclude with `Finset.sum_congr rfl fun i _ => (hX i).symm`. Establish `h2' : ∑ j, (w j : ℂ) = (-(B' * B)).trace`. Rewrite using `[← cω, ← h2]`. Conclude with `Finset.sum_congr rfl fun i _ => (hY i).symm`.

Rewrite `h2'` using `[trace_neg, trace_mul_comm, ← h1']`. Establish `: ((∑ j, w j : ℝ) : ℂ) = ((∑ i, x i : ℝ) : ℂ)`. Move the coercions through the operations in `at h2' ⊢`. Rewrite using `[h2', Finset.sum_neg_distrib, neg_neg]`. Conclude with `(ofReal_injective this).symm`.

Establish `hlt : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i < Fin.natAdd p j` using `fun i j => by`. Rewrite using `[Fin.lt_def]`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Take `⟨r1, r2⟩` from `weighted_sub x (fun i => lam (Fin.castAdd q i)) w (fun j => lam (Fin.natAdd p j)) (fun i => by positivity) (fun j => by positivity) hsum fun i j => hlam (hlt i j).le`.

Establish `hval : diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW (fun i => lam (Fin.castAdd q i)) y) ξ + diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω (fun i => lam (Fin.natAdd p i)) y) ξ = (2 * Real.pi)⁻¹ * (∑ i, lam (Fin.castAdd q i) * x i - ∑ j, lam (Fin.natAdd …`. Rewrite using `[diagVal_horizForm _ _ _ _ _ _ _ hX, diagVal_horizForm _ _ _ _ _ _ _ hY]`. Simplify using `only [mul_neg, Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree. Establish `hπ : 0 < (2 * Real.pi)⁻¹` using `by positivity`.

Rewrite using `[hval]`. Use `⟨mul_nonneg hπ.le r1, fun hst hB0 => mul_pos hπ (r2 (fun i j => hst (hlt i j)) ?_)⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Use `hB0 (eq_zero_of_cols (hω.unitary y hy) fun j => ?_)` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Use `gnorm_pos pQ hne` as an intermediate fact. Establish `h3 : 0 < w j` using `by positivity`. Conclude with `h3.ne' (hc j)`.
-/
theorem hodge_horiz : GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.SubQuotCurvature →
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [FiniteDimensional ℂ E] (ι : Type) [Fintype ι] (p q : ℕ) (U : Set (ι → ℂ))
    (ψ : (ι → ℂ) → Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ) (a b : ℝ) (Y : Set E) (π : E → ι → ℂ)
    (AW eW : E → Matrix (Fin p) (Fin p) ℂ) (Aω eω : E → Matrix (Fin q) (Fin q) ℂ),
    IsHodgeFrame U ψ → 0 < a → 0 < b → IsFlagFamily Y U π AW → IsFlagFamily Y U π Aω →
    IsUnitaryFlagFrame Y (fun x => (a : ℂ) • quotGram (ψ x)) π AW eW →
    IsUnitaryFlagFrame Y (fun x => (b : ℂ) • -subGram (ψ x)) π Aω eω →
    ∀ y ∈ Y, ∀ lam : Fin (p + q) → ℝ, Antitone lam → ∀ ξ,
      0 ≤ diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW
            (fun i => lam (Fin.castAdd q i)) y) ξ +
          diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω
            (fun i => lam (Fin.natAdd p i)) y) ξ ∧
      (StrictAnti lam → secondForm ψ (π y) (fderiv ℂ π y ξ) ≠ 0 →
        0 < diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW
            (fun i => lam (Fin.castAdd q i)) y) ξ +
          diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω
            (fun i => lam (Fin.natAdd p i)) y) ξ) := by
  intro hSQ E _ _ _ _ _ ι _ p q U ψ a b Y π AW eW Aω eω hψ ha hb hF _ hW hω y hy lam hlam ξ
  have hz : π y ∈ U := hF.mapsTo hy
  have hu : ∀ z ∈ U, IsUnit (subGram (ψ z)).det := fun z hz => by
    have := (isUnit_iff_isUnit_det _).1 (hψ.neg_sub z hz).isUnit
    rw [det_neg] at this
    exact isUnit_of_mul_isUnit_right this
  obtain ⟨hS, hQ, hat⟩ := (hSQ (ι → ℂ) (Fin q) (Fin p) U ψ).1 hψ.isHermFrame hu
  obtain ⟨-, -, hadj, -, hcS, hcQ⟩ := hat _ hz
  set v := fderiv ℂ π y ξ with hv
  set B := secondForm ψ (π y) v with hB
  set B' := secondFormAdj ψ (π y) v with hB'
  have hh := hψ.isHermFrame.herm _ hz
  have cW : curv (fun x => (a : ℂ) • quotGram (ψ x)) (π y) v v = B * B' := by
    have := curv_smul (f := fun _ => a) contDiffAt_const ha.ne' (hQ.two hz) (hQ.isUnit _ hz) v v
    rw [hcQ, hψ.flat _ hz] at this
    refine this.trans ?_
    simp [blockQQ, GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.wedgeHolAnti, hB, hB']
  have cω : curv (fun x => (b : ℂ) • -subGram (ψ x)) (π y) v v = -(B' * B) := by
    have := curv_smul (f := fun _ => -b) contDiffAt_const (neg_ne_zero.2 hb.ne') (hS.two hz)
      (hS.isUnit _ hz) v v
    rw [hcS, hψ.flat _ hz] at this
    have e : (fun x => (b : ℂ) • -subGram (ψ x)) =
        fun x => ((-b : ℝ) : ℂ) • GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS ψ x := by
      funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.gramS]
    rw [e]
    refine this.trans ?_
    simp [blockSS, GlobalTheory.IndefiniteRowSideFullHecke.HermitianCurvatureForms.wedgeAntiHol, hB, hB']
  have pS := hψ.neg_sub _ hz
  have pQ := hψ.pos_quot _ hz
  have fneg : ∀ s t, form (-subGram (ψ (π y))) s t = -form (subGram (ψ (π y))) s t := fun s t => by
    simp [form, neg_mulVec]
  set x : Fin p → ℝ := fun i => a * gnorm (-subGram (ψ (π y))) (B' *ᵥ fun c => eW y c i) ^ 2
    with hxd
  set w : Fin q → ℝ := fun j => b * gnorm (quotGram (ψ (π y))) (B *ᵥ fun c => eω y c j) ^ 2
    with hwd
  have hX : ∀ i, curvDiag (fun x => (a : ℂ) • quotGram (ψ x)) π eW i y ξ ξ = ((-x i : ℝ) : ℂ) := by
    intro i
    rw [curvDiag, ← hv, cW, form_smul, ← mulVec_mulVec, hB, form_secondForm hh (hu _ hz), ← hB',
      hxd, ofReal_neg, ofReal_mul, ← form_self pS.posSemidef, fneg]
    ring
  have hY : ∀ j, curvDiag (fun x => (b : ℂ) • -subGram (ψ x)) π eω j y ξ ξ = (w j : ℂ) := by
    intro j
    rw [curvDiag, ← hv, cω, form_smul, fneg, hB, hB', form_secondFormAdj_mul hh (hu _ hz), ← hB,
      hwd, ofReal_mul, ← form_self pQ.posSemidef, neg_neg]
  have hsum : ∑ i, x i = ∑ j, w j := by
    have h1 := sum_form_eq_trace (hW.unitary y hy) (B * B')
    have h2 := sum_form_eq_trace (hω.unitary y hy) (-(B' * B))
    rw [← cW] at h1
    rw [← cω] at h2
    have h1' : ∑ i, ((-x i : ℝ) : ℂ) = (B * B').trace := by
      rw [← cW, ← h1]; exact Finset.sum_congr rfl fun i _ => (hX i).symm
    have h2' : ∑ j, (w j : ℂ) = (-(B' * B)).trace := by
      rw [← cω, ← h2]; exact Finset.sum_congr rfl fun i _ => (hY i).symm
    rw [trace_neg, trace_mul_comm, ← h1'] at h2'
    have : ((∑ j, w j : ℝ) : ℂ) = ((∑ i, x i : ℝ) : ℂ) := by
      push_cast at h2' ⊢
      rw [h2', Finset.sum_neg_distrib, neg_neg]
    exact (ofReal_injective this).symm
  have hlt : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i < Fin.natAdd p j := fun i j => by
    rw [Fin.lt_def]; simp; omega
  obtain ⟨r1, r2⟩ := weighted_sub x (fun i => lam (Fin.castAdd q i)) w
    (fun j => lam (Fin.natAdd p j)) (fun i => by positivity) (fun j => by positivity) hsum
    fun i j => hlam (hlt i j).le
  have hval : diagVal (horizForm (fun x => (a : ℂ) • quotGram (ψ x)) π eW
            (fun i => lam (Fin.castAdd q i)) y) ξ +
          diagVal (horizForm (fun x => (b : ℂ) • -subGram (ψ x)) π eω
            (fun i => lam (Fin.natAdd p i)) y) ξ = (2 * Real.pi)⁻¹ *
          (∑ i, lam (Fin.castAdd q i) * x i - ∑ j, lam (Fin.natAdd p j) * w j) := by
    rw [diagVal_horizForm _ _ _ _ _ _ _ hX, diagVal_horizForm _ _ _ _ _ _ _ hY]
    simp only [mul_neg, Finset.sum_neg_distrib]
    ring
  have hπ : 0 < (2 * Real.pi)⁻¹ := by positivity
  rw [hval]
  refine ⟨mul_nonneg hπ.le r1, fun hst hB0 => mul_pos hπ (r2 (fun i j => hst (hlt i j)) ?_)⟩
  by_contra hc
  push Not at hc
  refine hB0 (eq_zero_of_cols (hω.unitary y hy) fun j => ?_)
  by_contra hne
  have := gnorm_pos pQ hne
  have h3 : 0 < w j := by positivity
  exact h3.ne' (hc j)

end GlobalTheory.HodgeHoriz
