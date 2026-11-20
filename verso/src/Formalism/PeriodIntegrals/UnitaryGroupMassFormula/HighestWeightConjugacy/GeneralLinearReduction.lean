import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GlueStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightConjugacy.GLDense

noncomputable section

open Matrix Filter Topology

namespace PI.UnitaryGroupMassFormula.HwConjInf

def mPt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : Bool × Fin n × Fin n → ℂ := fun p =>
  if p.1 then M p.2.1 p.2.2 else (M⁻¹) p.2.2 p.2.1

/- English proof (translation)
Use function extensionality and compare the values at `p`. Unfold `gPt mPt`. Rewrite using `[Matrix.coe_units_inv]`.
-/
theorem gPt_eq {n : ℕ} (g : GL (Fin n) ℂ) : gPt g = mPt g.val := by
  funext p
  unfold gPt mPt
  rw [Matrix.coe_units_inv]

/- English proof (translation)
Rewrite using `[continuousAt_pi]`. Introduce and unpack `⟨b, i, j⟩`. Consider the cases of `b`. Simplify using `only [mPt, Bool.false_eq_true, if_false]`. Establish `h1 : ContinuousAt (fun N : Matrix (Fin n) (Fin n) ℂ => N⁻¹) M` using `continuousAt_matrix_inv M (by simpa [isUnit_iff_ne_zero] using hM)`.

Conclude with `(continuous_apply_apply j i).continuousAt.comp h1`. Simplify using `only [mPt, if_true]`. Conclude with `(continuous_apply_apply i j).continuousAt`.
-/
theorem mPt_continuousAt {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt mPt M := by
  rw [continuousAt_pi]
  rintro ⟨b, i, j⟩
  cases b
  · simp only [mPt, Bool.false_eq_true, if_false]
    have h1 : ContinuousAt (fun N : Matrix (Fin n) (Fin n) ℂ => N⁻¹) M :=
      continuousAt_matrix_inv M (by simpa [isUnit_iff_ne_zero] using hM)
    exact (continuous_apply_apply j i).continuousAt.comp h1
  · simp only [mPt, if_true]
    exact (continuous_apply_apply i j).continuousAt

def Rm {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ) (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix ι ι ℂ := fun i j => MvPolynomial.eval (mPt M) (Q i j)

/- English proof (translation)
Use `continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_` and prove the remaining obligations. Conclude with `((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp (mPt_continuousAt M hM)`.
-/
theorem Rm_continuousAt {n : ℕ} {ι : Type} (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (M : Matrix (Fin n) (Fin n) ℂ) (hM : M.det ≠ 0) : ContinuousAt (Rm Q) M := by
  refine continuousAt_pi.mpr fun i => continuousAt_pi.mpr fun j => ?_
  exact ((MvPolynomial.continuous_eval (Q i j)).continuousAt).comp (mPt_continuousAt M hM)

def dd {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : GL (Fin n) ℂ :=
  ⟨Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t), Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)),
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add],
    by rw [Matrix.diagonal_mul_diagonal]; simp [← Complex.exp_add]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dd_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    (dd c t).val = Matrix.diagonal fun i => Complex.exp ((c i : ℂ) * t) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dd_inv_val {n : ℕ} (c : Fin n → ℤ) (t : ℝ) :
    ((dd c t)⁻¹).val = Matrix.diagonal fun i => Complex.exp (-((c i : ℂ) * t)) := rfl

/- English proof (translation)
Rewrite using `[dd_val]`. Conclude with `Matrix.blockTriangular_diagonal _`.
-/
theorem dd_tri {n : ℕ} (c : Fin n → ℤ) (t : ℝ) : (dd c t).val.BlockTriangular id := by
  rw [dd_val]
  exact Matrix.blockTriangular_diagonal _

def phi {n : ℕ} (c lam : Fin n → ℤ) : ℤ := ∑ i, c i * lam i

/- English proof (translation)
Rewrite using `[dd_val]`. Simplify using `only [Matrix.diagonal_apply_eq]`. Rewrite using `[show (phi c lam : ℂ) * t = ∑ i, (lam i : ℂ) * ((c i : ℂ) * t) by`. Unfold `phi`. Use `push_cast`.

Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring]`. Rewrite using `[Complex.exp_sum]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Conclude with `(Complex.exp_int_mul ((c i : ℂ) * t) (lam i)).symm`.
-/
theorem char_dd {n : ℕ} (c lam : Fin n → ℤ) (t : ℝ) :
    ∏ i, (dd c t).val i i ^ lam i = Complex.exp ((phi c lam : ℂ) * t) := by
  rw [dd_val]
  simp only [Matrix.diagonal_apply_eq]
  rw [show (phi c lam : ℂ) * t = ∑ i, (lam i : ℂ) * ((c i : ℂ) * t) by
    unfold phi
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring]
  rw [Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (Complex.exp_int_mul ((c i : ℂ) * t) (lam i)).symm

/- English proof (translation)
Rewrite using `[tendsto_zero_iff_norm_tendsto_zero]`. Establish `h : (fun t : ℝ => ‖Complex.exp ((k : ℂ) * t)‖) = fun t => Real.exp ((k : ℝ) * t)`. Use function extensionality and compare the values at `t`. Rewrite using `[Complex.norm_exp]`. Use `congr 1`.

Simplify using the standard rewrite rules. Rewrite using `[h]`. Apply `Real.tendsto_exp_atBot.comp` to reduce the goal to its premises. Conclude with `Filter.tendsto_id.const_mul_atTop_of_neg (by exact_mod_cast hk)`.
-/
theorem tendsto_exp_neg {k : ℤ} (hk : k < 0) :
    Tendsto (fun t : ℝ => Complex.exp ((k : ℂ) * t)) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h : (fun t : ℝ => ‖Complex.exp ((k : ℂ) * t)‖) = fun t => Real.exp ((k : ℝ) * t) := by
    funext t
    rw [Complex.norm_exp]
    congr 1
    simp
  rw [h]
  apply Real.tendsto_exp_atBot.comp
  exact Filter.tendsto_id.const_mul_atTop_of_neg (by exact_mod_cast hk)

/- English proof (translation)
Establish `hR : ∀ g : GL (Fin n) ℂ, R g = Rm Q g.val`. Introduce `g`. Use extensionality with `i j`. Rewrite using `[hRQ, Rm, gPt_eq]`. Use `set f : (ι → ℂ) → ℝ → (ι → ℂ) := fun w t => Complex.exp (-((phi c lam : ℂ) * t)) • (R (dd c t) *ᵥ w) with hf`.

Set `P : Submodule ℂ (ι → ℂ)` to `{ carrier := {w | ∃ y, Tendsto (f w) atTop (𝓝 y)} add_mem' := by`. Introduce and unpack `a b ⟨ya, ha⟩ ⟨yb, hb⟩`. Use `⟨ya + yb, ?_⟩` and prove the remaining obligations. Establish `e : f (a + b) = fun t => f a t + f b t` using `by funext t; simp [hf, Matrix.mulVec_add, smul_add]`. Rewrite using `[e]`.

Conclude with `ha.add hb`. Use the proof step `zero_mem' := ⟨0, by`. Establish `e : f 0 = fun _ => 0` using `by funext t; simp [hf]`. Rewrite using `[e]`. Conclude with `tendsto_const_nhds⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `r a ⟨ya, ha⟩`. Use `⟨r • ya, ?_⟩` and prove the remaining obligations. Establish `e : f (r • a) = fun t => r • f a t` using `by funext t; simp [hf, Matrix.mulVec_smul, smul_comm r]`. Rewrite using `[e]`.

Conclude with `ha.const_smul r }`. Establish `hgenL : ∀ s ∈ S, ∀ large₂ : GL (Fin n) ℂ, LowUni large₂.val → s *ᵥ (R large₂ *ᵥ v) ∈ P`. Introduce `s hs large₂ hL`. Establish `comm : ∀ g y, R g *ᵥ (s *ᵥ y) = s *ᵥ (R g *ᵥ y)`. Introduce `g y`.

Rewrite using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS s hs]`. Establish `key : ∀ t, f (s *ᵥ (R large₂ *ᵥ v)) t = s *ᵥ (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v)`. Introduce `t`. Establish `e2 : dd c t * large₂ = (dd c t * large₂ * (dd c t)⁻¹) * dd c t` using `by group`. Establish `inner : R (dd c t) *ᵥ (R large₂ *ᵥ v) = Complex.exp ((phi c lam : ℂ) * t) • (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v)`.

Rewrite using `[Matrix.mulVec_mulVec, ← hmul, show R (dd c t * large₂) = R (dd c t * large₂ * (dd c t)⁻¹) * R (dd c t) by`. Rewrite using `[← hmul, ← e2], ← Matrix.mulVec_mulVec, hv (dd c t) (dd_tri c t),`. Use the proof step `char_dd, Matrix.mulVec_smul, hR]`. Simplify using `only [hf]`. Rewrite using `[comm, inner, Matrix.mulVec_smul, smul_smul, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_smul]`.

Establish `hM : Tendsto (fun t => (dd c t * large₂ * (dd c t)⁻¹).val) atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ))`. Use `tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_` and prove the remaining obligations. Apply the tactic sequence `have hentry : ∀ t, (dd c t * large₂ * (dd c t)⁻¹).val i j = Complex.exp (((c i - c j : ℤ) : ℂ) * t) * large₂.val i j := by`. Introduce `t`. Rewrite using `[Units.val_mul, Units.val_mul, dd_val, dd_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Rewrite using `[mul_comm (Complex.exp _) (large₂.val i j), mul_assoc, ← Complex.exp_add, mul_comm]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [hentry]`.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. Rewrite using `[hL.1 i j h, Matrix.one_apply_ne h.ne]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality. Simplify using `[hL.2]`.

Rewrite using `[Matrix.one_apply_ne h.ne']`. Simplify using `using (tendsto_exp_neg (sub_neg.2 (hc j i h))).mul_const (large₂.val i j)`. Establish `hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v)` using `continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)`. Use `⟨s *ᵥ (Rm Q 1 *ᵥ v), ?_⟩` and prove the remaining obligations. Rewrite using `[show f (s *ᵥ (R large₂ *ᵥ v)) = _ from funext key]`.

Conclude with `(hcs.tendsto _).comp ((Rm_continuousAt Q 1 (by simp)).tendsto.comp hM)`. Establish `hgen : ∀ s ∈ S, ∀ g : GL (Fin n) ℂ, s *ᵥ (R g *ᵥ v) ∈ P`. Introduce `s hs g`. Establish `hclosed : IsClosed (P : Set (ι → ℂ))` using `Submodule.closed_of_finiteDimensional P`. Establish `hdet : g.val.det ≠ 0` using `(Matrix.isUnits_det_units g).ne_zero`.

Establish `hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v)` using `continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)`. Establish `hlim : Tendsto (fun x : ℂ => s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v)) (𝓝[≠] 0) (𝓝 (s *ᵥ (R g *ᵥ v)))`. Rewrite using `[hR]`. Conclude with `(hcs.tendsto _).comp ((Rm_continuousAt Q g.val hdet).tendsto.comp (tendsto_add_smul g.val))`. Apply `hclosed.mem_of_tendsto hlim` to reduce the goal to its premises.

Use `filter_upwards [dense_LU g.val] with x hx`. Take `⟨hdx, L, U, hL, hU, hLU⟩` from `hx`. Establish `hdL : L.det ≠ 0` using `by rw [det_lowUni hL]; exact one_ne_zero`. Establish `hdU : U.det ≠ 0` using `by intro h; apply hdx; rw [hLU, Matrix.det_mul, h, mul_zero]`. Use `set large₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdL`.

Use `set Ug := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdU`. Establish `e : g.val + x • 1 = (large₂ * Ug).val` using `by rw [hLU]; rfl`. Establish `hUg : Ug.val.BlockTriangular id` using `fun i j h => hU i j h`. Use `show s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v) ∈ P`. Rewrite using `[e, ← hR, hmul, ← Matrix.mulVec_mulVec, hv Ug hUg, Matrix.mulVec_smul, Matrix.mulVec_smul]`.

Conclude with `P.smul_mem _ (hgenL s hs large₂ hL)`. Establish `huP : u ∈ P`. Use `Submodule.span_le.2 ?_ hmem` and prove the remaining obligations. Introduce and unpack `w ⟨s, hs, g, rfl⟩`. Conclude with `hgen s hs g`.

Take `⟨y, hy⟩` from `huP`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`. Establish `hfu : ∀ t, f u t = Complex.exp (((phi c mu - phi c lam : ℤ) : ℂ) * t) • u`. Introduce `t`.

Simplify using `only [hf]`. Rewrite using `[hu (dd c t) (dd_tri c t), char_dd, smul_smul, ← Complex.exp_add]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `hnorm : Tendsto (fun t => ‖f u t‖) atTop atTop`. Establish `e : (fun t => ‖f u t‖) = fun t => Real.exp (((phi c mu - phi c lam : ℤ) : ℝ) * t) * ‖u‖`. Use function extensionality and compare the values at `t`. Rewrite using `[hfu, norm_smul, Complex.norm_exp]`. Simplify using the standard rewrite rules.

Rewrite using `[e]`. Conclude with `(Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by exact_mod_cast sub_pos.2 hlt))).atTop_mul_const (norm_pos_iff.2 hu0)`. Conclude with `not_tendsto_atTop_of_tendsto_nhds hy.norm hnorm`.
-/
theorem wt_le {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : GL (Fin n) ℂ → Matrix ι ι ℂ) (Q : ι → ι → MvPolynomial (Bool × Fin n × Fin n) ℂ)
    (hRQ : ∀ g i j, R g i j = MvPolynomial.eval (gPt g) (Q i j))
    (hmul : ∀ g h, R (g * h) = R g * R h)
    (S : Set (Matrix ι ι ℂ)) (hS : ∀ s ∈ S, ∀ g, s * R g = R g * s)
    (v u : ι → ℂ) (lam mu : Fin n → ℤ)
    (hv : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) v = (∏ i, B.val i i ^ lam i) • v)
    (hu : ∀ B : GL (Fin n) ℂ, B.val.BlockTriangular id → Matrix.mulVec (R B) u = (∏ i, B.val i i ^ mu i) • u)
    (hmem : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)})
    (hu0 : u ≠ 0) (c : Fin n → ℤ) (hc : ∀ i j, i < j → c j < c i) :
    phi c mu ≤ phi c lam := by
  have hR : ∀ g : GL (Fin n) ℂ, R g = Rm Q g.val := by
    intro g; ext i j; rw [hRQ, Rm, gPt_eq]
  set f : (ι → ℂ) → ℝ → (ι → ℂ) := fun w t => Complex.exp (-((phi c lam : ℂ) * t)) • (R (dd c t) *ᵥ w) with hf
  let P : Submodule ℂ (ι → ℂ) :=
    { carrier := {w | ∃ y, Tendsto (f w) atTop (𝓝 y)}
      add_mem' := by
        rintro a b ⟨ya, ha⟩ ⟨yb, hb⟩
        refine ⟨ya + yb, ?_⟩
        have e : f (a + b) = fun t => f a t + f b t := by funext t; simp [hf, Matrix.mulVec_add, smul_add]
        rw [e]; exact ha.add hb
      zero_mem' := ⟨0, by
        have e : f 0 = fun _ => 0 := by funext t; simp [hf]
        rw [e]; exact tendsto_const_nhds⟩
      smul_mem' := by
        rintro r a ⟨ya, ha⟩
        refine ⟨r • ya, ?_⟩
        have e : f (r • a) = fun t => r • f a t := by funext t; simp [hf, Matrix.mulVec_smul, smul_comm r]
        rw [e]; exact ha.const_smul r }

  have hgenL : ∀ s ∈ S, ∀ large₂ : GL (Fin n) ℂ, LowUni large₂.val → s *ᵥ (R large₂ *ᵥ v) ∈ P := by
    intro s hs large₂ hL
    have comm : ∀ g y, R g *ᵥ (s *ᵥ y) = s *ᵥ (R g *ᵥ y) := by
      intro g y; rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hS s hs]
    have key : ∀ t, f (s *ᵥ (R large₂ *ᵥ v)) t = s *ᵥ (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
      intro t
      have e2 : dd c t * large₂ = (dd c t * large₂ * (dd c t)⁻¹) * dd c t := by group
      have inner : R (dd c t) *ᵥ (R large₂ *ᵥ v) =
          Complex.exp ((phi c lam : ℂ) * t) • (Rm Q (dd c t * large₂ * (dd c t)⁻¹).val *ᵥ v) := by
        rw [Matrix.mulVec_mulVec, ← hmul, show R (dd c t * large₂) = R (dd c t * large₂ * (dd c t)⁻¹) * R (dd c t) by
          rw [← hmul, ← e2], ← Matrix.mulVec_mulVec, hv (dd c t) (dd_tri c t),
          char_dd, Matrix.mulVec_smul, hR]
      simp only [hf]
      rw [comm, inner, Matrix.mulVec_smul, smul_smul, ← Complex.exp_add, neg_add_cancel,
        Complex.exp_zero, one_smul]
    have hM : Tendsto (fun t => (dd c t * large₂ * (dd c t)⁻¹).val) atTop (𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)) := by
      refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
      have hentry : ∀ t, (dd c t * large₂ * (dd c t)⁻¹).val i j =
          Complex.exp (((c i - c j : ℤ) : ℂ) * t) * large₂.val i j := by
        intro t
        rw [Units.val_mul, Units.val_mul, dd_val, dd_inv_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
        rw [mul_comm (Complex.exp _) (large₂.val i j), mul_assoc, ← Complex.exp_add, mul_comm]
        congr 2; push_cast; ring
      simp only [hentry]
      rcases lt_trichotomy i j with h | h | h
      · rw [hL.1 i j h, Matrix.one_apply_ne h.ne]; simp
      · subst h; simp [hL.2]
      · rw [Matrix.one_apply_ne h.ne']
        simpa using (tendsto_exp_neg (sub_neg.2 (hc j i h))).mul_const (large₂.val i j)
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    refine ⟨s *ᵥ (Rm Q 1 *ᵥ v), ?_⟩
    rw [show f (s *ᵥ (R large₂ *ᵥ v)) = _ from funext key]
    exact (hcs.tendsto _).comp ((Rm_continuousAt Q 1 (by simp)).tendsto.comp hM)

  have hgen : ∀ s ∈ S, ∀ g : GL (Fin n) ℂ, s *ᵥ (R g *ᵥ v) ∈ P := by
    intro s hs g
    have hclosed : IsClosed (P : Set (ι → ℂ)) := Submodule.closed_of_finiteDimensional P
    have hdet : g.val.det ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    have hcs : Continuous fun N : Matrix ι ι ℂ => s *ᵥ (N *ᵥ v) :=
      continuous_const.matrix_mulVec (continuous_id.matrix_mulVec continuous_const)
    have hlim : Tendsto (fun x : ℂ => s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v)) (𝓝[≠] 0) (𝓝 (s *ᵥ (R g *ᵥ v))) := by
      rw [hR]
      exact (hcs.tendsto _).comp ((Rm_continuousAt Q g.val hdet).tendsto.comp (tendsto_add_smul g.val))
    apply hclosed.mem_of_tendsto hlim
    filter_upwards [dense_LU g.val] with x hx
    obtain ⟨hdx, L, U, hL, hU, hLU⟩ := hx
    have hdL : L.det ≠ 0 := by rw [det_lowUni hL]; exact one_ne_zero
    have hdU : U.det ≠ 0 := by intro h; apply hdx; rw [hLU, Matrix.det_mul, h, mul_zero]
    set large₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero L hdL
    set Ug := Matrix.GeneralLinearGroup.mkOfDetNeZero U hdU
    have e : g.val + x • 1 = (large₂ * Ug).val := by rw [hLU]; rfl
    have hUg : Ug.val.BlockTriangular id := fun i j h => hU i j h
    show s *ᵥ (Rm Q (g.val + x • 1) *ᵥ v) ∈ P
    rw [e, ← hR, hmul, ← Matrix.mulVec_mulVec, hv Ug hUg, Matrix.mulVec_smul, Matrix.mulVec_smul]
    exact P.smul_mem _ (hgenL s hs large₂ hL)
  have huP : u ∈ P := by
    refine Submodule.span_le.2 ?_ hmem
    rintro w ⟨s, hs, g, rfl⟩
    exact hgen s hs g
  obtain ⟨y, hy⟩ := huP
  by_contra hlt
  push Not at hlt
  have hfu : ∀ t, f u t = Complex.exp (((phi c mu - phi c lam : ℤ) : ℂ) * t) • u := by
    intro t
    simp only [hf]
    rw [hu (dd c t) (dd_tri c t), char_dd, smul_smul, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hnorm : Tendsto (fun t => ‖f u t‖) atTop atTop := by
    have e : (fun t => ‖f u t‖) = fun t => Real.exp (((phi c mu - phi c lam : ℤ) : ℝ) * t) * ‖u‖ := by
      funext t; rw [hfu, norm_smul, Complex.norm_exp]; simp
    rw [e]
    exact (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by exact_mod_cast sub_pos.2 hlt))).atTop_mul_const
      (norm_pos_iff.2 hu0)
  exact not_tendsto_atTop_of_tendsto_nhds hy.norm hnorm

/- English proof (translation)
Introduce `n ι _ _ R Q hRQ hmul S hS v u lam mu hv hu hspv hspu hv0 hu0`. Establish `memu : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)}`. Rewrite using `[hspv]`. Conclude with `Submodule.mem_top`. Establish `memv : v ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)}`.

Rewrite using `[hspu]`. Conclude with `Submodule.mem_top`. Establish `key : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j < c i) → phi c mu = phi c lam` using `fun c hc => le_antisymm (wt_le R Q hRQ hmul S hS v u lam mu hv hu memu hu0 c hc) (wt_le R Q hRQ hmul S hS u v mu lam hu hv memv hv0 c hc)`. Use function extensionality and compare the values at `k`. Set `c0 : Fin n → ℤ` to `fun i => -2 * ((i : ℕ) : ℤ)`.

Set `ck : Fin n → ℤ` to `fun i => -2 * ((i : ℕ) : ℤ) + if i = k then 1 else 0`. Establish `h0` using `key c0 (by`. Introduce `i j h`. Establish `: (i : ℕ) < j` using `h`. Simplify using `only [c0]`.

Use the proof step `omega)`. Establish `h1` using `key ck (by`. Introduce `i j h`. Establish `: (i : ℕ) < j` using `h`. Apply the tactic sequence `simp only [ck]; split_ifs <;> omega)`.

Establish `hk : ∀ x : Fin n → ℤ, phi ck x = phi c0 x + x k`. Introduce `x`. Simplify using `[phi, ck, c0, add_mul, Finset.sum_add_distrib]`. Rewrite `h1` using `[hk, hk]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem general_linear_reduction : GLStep := by
  intro n ι _ _ R Q hRQ hmul S hS v u lam mu hv hu hspv hspu hv0 hu0
  have memu : u ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) v)} := by
    rw [hspv]; exact Submodule.mem_top
  have memv : v ∈ Submodule.span ℂ {w | ∃ s ∈ S, ∃ g, w = Matrix.mulVec s (Matrix.mulVec (R g) u)} := by
    rw [hspu]; exact Submodule.mem_top
  have key : ∀ c : Fin n → ℤ, (∀ i j, i < j → c j < c i) → phi c mu = phi c lam := fun c hc =>
    le_antisymm (wt_le R Q hRQ hmul S hS v u lam mu hv hu memu hu0 c hc)
      (wt_le R Q hRQ hmul S hS u v mu lam hu hv memv hv0 c hc)
  funext k
  let c0 : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ)
  let ck : Fin n → ℤ := fun i => -2 * ((i : ℕ) : ℤ) + if i = k then 1 else 0
  have h0 := key c0 (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [c0]; omega)
  have h1 := key ck (by
    intro i j h
    have : (i : ℕ) < j := h
    simp only [ck]; split_ifs <;> omega)
  have hk : ∀ x : Fin n → ℤ, phi ck x = phi c0 x + x k := by
    intro x
    simp [phi, ck, c0, add_mul, Finset.sum_add_distrib]
  rw [hk, hk] at h1
  linarith

end PI.UnitaryGroupMassFormula.HwConjInf
