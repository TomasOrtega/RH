import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import ReciprocityTheory.AnalyticForms.LeviForms.HomDensB

namespace ReciprocityTheory.AnForm.P

open MeasureTheory

noncomputable section

def CellMatZeroStatement : Prop := ∀ N : ℕ, cellMat N 0 = 1

/- English proof (translation)
Introduce `N`. Establish `hz : zMat N 0 = 0`. Use extensionality with `i j`. Rewrite using `[zMat_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.

Rewrite using `[cellMat_eq, hz]`. Break down `N with _ | n` into its components or cases. Conclude with `Subsingleton.elim _ _`. Rewrite using `[Finset.sum_range_succ']`. Simplify using the standard rewrite rules.
-/
theorem cellMat_zero : CellMatZeroStatement := by
  intro N
  have hz : zMat N 0 = 0 := by
    ext i j
    rw [zMat_apply]
    split_ifs <;> rfl
  rw [cellMat_eq, hz]
  rcases N with _ | n
  · exact Subsingleton.elim _ _
  · rw [Finset.sum_range_succ']
    simp

def LeviHalfLogAbsStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (f : (ι → ℂ) → ℝ) (z : ι → ℂ), ContDiffAt ℝ 2 f z → f z ≠ 0 →
    fderiv ℝ f z = 0 → ∀ w : ι → ℂ,
      levi (fun x => (1 / 2) * Real.log |f x|) z w = levi f z w / (2 * f z)

/- English proof (translation)
Introduce `ι _ f z hf hz hd w`. Conclude with `leviForm_half_log_abs_of_fderiv_eq_zero f z hf hz hd w`.
-/
theorem leviHalfLogAbs : LeviHalfLogAbsStatement := by
  intro ι _ f z hf hz hd w
  exact leviForm_half_log_abs_of_fderiv_eq_zero f z hf hz hd w

def detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) : ℝ :=
  ((Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
      cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det).re

section HomDensHelp

open Matrix Polynomial

/- English proof (translation)
Establish `h1 : cellMat N (s • v) = ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • zMat N v ^ k`. Rewrite using `[cellMat_eq, zMat_real_smul]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[_root_.smul_pow, smul_smul, mul_comm]`. Establish `h2 : (cellMat N (s • v))ᴴ = ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • (zMat N v)ᴴ ^ k`.

Rewrite using `[h1, conjTranspose_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[conjTranspose_smul, conjTranspose_pow]`. Use `congr 1`. Simplify using `[Complex.conj_ofReal]`.

Establish `hG : (gP N hd v).map (eval (s : ℂ)) = (cellMat N (s • v))ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N (s • v)`. Rewrite using `[gP, ← coe_evalRingHom, Matrix.map_mul, Matrix.map_mul, coe_evalRingHom, eval_cpP, eval_cpP, h2, h1, Matrix.mul_assoc]`. Use `congr 2`. Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [diagonal_apply, h]`.

Unfold `detGram`. Rewrite using `[← hG]`. Use `congr 1`. Rewrite using `[← coe_evalRingHom, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem detGram_line (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (s : ℝ) :
    detGram N hd m hm (s • v) = ((Gm N hd m hm v).det.eval (s : ℂ)).re := by
  have h1 : cellMat N (s • v) =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • zMat N v ^ k := by
    rw [cellMat_eq, zMat_real_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [_root_.smul_pow, smul_smul, mul_comm]
  have h2 : (cellMat N (s • v))ᴴ =
      ∑ k ∈ Finset.range N, ((s : ℂ) ^ k * ((k.factorial : ℂ)⁻¹)) • (zMat N v)ᴴ ^ k := by
    rw [h1, conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [conjTranspose_smul, conjTranspose_pow]
    congr 1
    simp [Complex.conj_ofReal]
  have hG : (gP N hd v).map (eval (s : ℂ)) =
      (cellMat N (s • v))ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N (s • v) := by
    rw [gP, ← coe_evalRingHom, Matrix.map_mul, Matrix.map_mul, coe_evalRingHom, eval_cpP,
      eval_cpP, h2, h1, Matrix.mul_assoc]
    congr 2
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h]
  unfold detGram
  rw [← hG]
  congr 1
  rw [← coe_evalRingHom, RingHom.map_det]
  rfl

/- English proof (translation)
Establish `hZ : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => zMat N z a b)`. Introduce `a b`. Distinguish the cases in `h : b < a`. Simplify using `only [zMat_apply, dif_pos h]`. Conclude with `contDiff_apply ℝ ℂ _`.

Simplify using `only [zMat_apply, dif_neg h]`. Conclude with `contDiff_const`. Establish `hP : ∀ k a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => (zMat N z ^ k) a b)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero => intro a b`. Simplify using `only [pow_zero]`. Conclude with `contDiff_const`. Consider the case `succ k ih`. Introduce `a b`.

Simplify using `only [pow_succ, Matrix.mul_apply]`. Conclude with `ContDiff.sum fun l _ => (ih a l).mul (hZ l b)`. Establish `hA : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => cellMat N z a b)`. Introduce `a b`. Simplify using `only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]`.

Conclude with `ContDiff.sum fun k _ => contDiff_const.mul (hP k a b)`. Establish `hS : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => star (cellMat N z a b))` using `fun a b => by`. Establish `h` using `Complex.conjCLE.contDiff.comp (hA a b)`. Conclude with `h`. Establish `hM : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b)`.

Introduce `a b`. Establish `e : (fun z : Pairs N → ℂ => ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) = fun z => ∑ l, star (cellMat N z l a) * (hd l : ℂ) * cellMat N z l b`. Use function extensionality and compare the values at `z`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]`.

Rewrite using `[e]`. Conclude with `ContDiff.sum fun l _ => ((hS l a).mul contDiff_const).mul (hA l b)`. Establish `hdet : ContDiff ℝ 2 (fun z : Pairs N → ℂ => (Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det)`. Simplify using `only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]`. Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)`.

Establish `h2 : ContDiff ℝ 2 (fun z : Pairs N → ℂ => Complex.reCLM (Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det)` using `Complex.reCLM.contDiff.comp hdet`. Unfold `detGram`. Simplify `h2` using `only [Complex.reCLM_apply]`.
-/
theorem contDiff_detGram (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) :
    ContDiff ℝ 2 (detGram N hd m hm) := by
  have hZ : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => zMat N z a b) := by
    intro a b
    by_cases h : b < a
    · simp only [zMat_apply, dif_pos h]; exact contDiff_apply ℝ ℂ _
    · simp only [zMat_apply, dif_neg h]; exact contDiff_const
  have hP : ∀ k a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => (zMat N z ^ k) a b) := by
    intro k
    induction k with
    | zero => intro a b; simp only [pow_zero]; exact contDiff_const
    | succ k ih =>
      intro a b
      simp only [pow_succ, Matrix.mul_apply]
      exact ContDiff.sum fun l _ => (ih a l).mul (hZ l b)
  have hA : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => cellMat N z a b) := by
    intro a b
    simp only [cellMat_eq, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact ContDiff.sum fun k _ => contDiff_const.mul (hP k a b)
  have hS : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ => star (cellMat N z a b)) := fun a b => by
    have h := Complex.conjCLE.contDiff.comp (hA a b)
    exact h
  have hM : ∀ a b, ContDiff ℝ 2 (fun z : Pairs N → ℂ =>
      ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) := by
    intro a b
    have e : (fun z : Pairs N → ℂ =>
        ((cellMat N z)ᴴ * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) a b) =
        fun z => ∑ l, star (cellMat N z l a) * (hd l : ℂ) * cellMat N z l b := by
      funext z
      rw [Matrix.mul_apply]
      simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]
    rw [e]
    exact ContDiff.sum fun l _ => ((hS l a).mul contDiff_const).mul (hA l b)
  have hdet : ContDiff ℝ 2 (fun z : Pairs N → ℂ => (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det) := by
    simp only [Matrix.det_apply, Matrix.submatrix_apply, Units.smul_def, zsmul_eq_mul]
    exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM _ _)
  have h2 : ContDiff ℝ 2 (fun z : Pairs N → ℂ => Complex.reCLM (Matrix.submatrix
      ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z)
      (Fin.castLE hm) (Fin.castLE hm)).det) := Complex.reCLM.contDiff.comp hdet
  unfold detGram
  simpa only [Complex.reCLM_apply] using h2

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Conclude with `Finset.sum_bij (fun b _ => Fin.castLE hm b) (fun b _ => by simp) (fun b1 _ b2 _ h => Fin.castLE_injective hm h) (fun k hk => ⟨⟨k.val, (Finset.mem_filter.1 hk).2⟩, Finset.mem_univ _, Fin.ext rfl⟩) (fun b _ => rfl)`.
-/
theorem sum_castLE (N m : ℕ) (hm : m ≤ N) (f : Fin N → ℝ) :
    ∑ b : Fin m, f (Fin.castLE hm b) = ∑ k : Fin N, if k.val < m then f k else 0 := by
  rw [← Finset.sum_filter]
  exact Finset.sum_bij (fun b _ => Fin.castLE hm b) (fun b _ => by simp)
    (fun b1 _ b2 _ h => Fin.castLE_injective hm h)
    (fun k hk => ⟨⟨k.val, (Finset.mem_filter.1 hk).2⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    (fun b _ => rfl)

def sW (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (v : Pairs N → ℂ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin N,
    if i.val < m ∧ m ≤ k.val then hd k / hd i * ‖zMat N v k i‖ ^ 2 else 0

/- English proof (translation)
Rewrite using `[Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]`. Express the relevant statement in the definitionally equal form `(starRingEnd ℂ) z * _ = _`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem star_mul_mul (h : ℝ) (z : ℂ) : star z * ((h : ℂ) * z) = ((h * ‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, ← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  change (starRingEnd ℂ) z * _ = _
  ring

/- English proof (translation)
Establish `hin : ∀ i : Fin N, (∑ k, hd k * ‖zMat N v k i‖ ^ 2) - ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) i‖ ^ 2 = ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0`. Introduce `i`. Rewrite using `[sum_castLE N m hm (fun b => hd b * ‖zMat N v b i‖ ^ 2), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : k.val < m`.

Simplify using `[h, not_le.2 h]`. Simplify using `[h, not_lt.1 h]`. Establish `hR : ∑ a : Fin m, (hd (Fin.castLE hm a))⁻¹ * ((∑ k, hd k * ‖zMat N v k (Fin.castLE hm a)‖ ^ 2) - ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) (Fin.castLE hm a)‖ ^ 2) = sW N hd m v`. Simplify using `only [hin]`. Rewrite using `[sum_castLE N m hm (fun i => (hd i)⁻¹ * ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0), sW]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i.val < m`. Rewrite using `[if_pos hi, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : m ≤ k.val`.

Simplify using `only [hi, hk, and_self, if_true]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[hk]`. Simplify using `[hi]`. Establish `hC` using `congrArg (fun x : ℝ => (x : ℂ)) hR`.

Simplify using `only [star_mul_mul]`. Move the coercions through the operations in `at hC ⊢`. Conclude with `hC`.
-/
theorem bracket_eq (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) :
    ∑ a : Fin m, ((hd (Fin.castLE hm a) : ℂ))⁻¹ *
        (∑ k, star (zMat N v k (Fin.castLE hm a)) * ((hd k : ℂ) * zMat N v k (Fin.castLE hm a)) -
        ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
          ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a))) =
      (sW N hd m v : ℂ) := by
  have hin : ∀ i : Fin N, (∑ k, hd k * ‖zMat N v k i‖ ^ 2) -
      ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) i‖ ^ 2 =
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0 := by
    intro i
    rw [sum_castLE N m hm (fun b => hd b * ‖zMat N v b i‖ ^ 2), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k.val < m
    · simp [h, not_le.2 h]
    · simp [h, not_lt.1 h]
  have hR : ∑ a : Fin m, (hd (Fin.castLE hm a))⁻¹ *
      ((∑ k, hd k * ‖zMat N v k (Fin.castLE hm a)‖ ^ 2) -
        ∑ b : Fin m, hd (Fin.castLE hm b) * ‖zMat N v (Fin.castLE hm b) (Fin.castLE hm a)‖ ^ 2) =
      sW N hd m v := by
    simp only [hin]
    rw [sum_castLE N m hm (fun i => (hd i)⁻¹ *
      ∑ k : Fin N, if m ≤ k.val then hd k * ‖zMat N v k i‖ ^ 2 else 0), sW]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.val < m
    · rw [if_pos hi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hk : m ≤ k.val
      · simp only [hi, hk, and_self, if_true]; ring
      · simp [hk]
    · simp [hi]
  have hC := congrArg (fun x : ℝ => (x : ℂ)) hR
  simp only [star_mul_mul]
  push_cast at hC ⊢
  exact hC

/- English proof (translation)
Simplify using `[sW, zMat_smul, norm_mul]`.
-/
theorem sW_I (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m (Complex.I • w) = sW N hd m w := by
  simp [sW, zMat_smul, norm_mul]

/- English proof (translation)
Set `F : Fin N × Fin N → ℝ` to `fun q => if q.1.val < m ∧ m ≤ q.2.val then hd q.2 / hd q.1 * ‖zMat N w q.2 q.1‖ ^ 2 else 0`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.sum_filter_of_ne fun q _ hq => ?_).symm` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Apply `hq` to reduce the goal to its premises.

Simplify using `only [F]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `hlt (Fin.lt_iff_val_lt_val.2 (by omega))`. Use `_ = ∑ p : Pairs N, F p.1 := Finset.sum_subtype _ (by simp) F`.

Use `_ = _ := by`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Simplify using `only [F, zMat_apply, dif_pos p.2]`.
-/
theorem sW_pairs (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (w : Pairs N → ℂ) :
    sW N hd m w = ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
      hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0 := by
  let F : Fin N × Fin N → ℝ := fun q =>
    if q.1.val < m ∧ m ≤ q.2.val then hd q.2 / hd q.1 * ‖zMat N w q.2 q.1‖ ^ 2 else 0
  calc sW N hd m w = ∑ q, F q := (Fintype.sum_prod_type' (fun i k => F (i, k))).symm
    _ = ∑ q ∈ Finset.univ.filter (fun q : Fin N × Fin N => q.1 < q.2), F q := by
      refine (Finset.sum_filter_of_ne fun q _ hq => ?_).symm
      by_contra hlt
      apply hq
      simp only [F]
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hlt (Fin.lt_iff_val_lt_val.2 (by omega))
    _ = ∑ p : Pairs N, F p.1 := Finset.sum_subtype _ (by simp) F
    _ = _ := by
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [F, zMat_apply, dif_pos p.2]

end HomDensHelp

def LogDetFlagEqStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    logDetFlag N hd m hm = fun z => (1 / 2) * Real.log |detGram N hd m hm z|

/- English proof (translation)
Introduce `N hd m hm`. Use function extensionality and compare the values at `z`. Establish `hs : star (fun k => (hd k : ℂ)) = fun k => (hd k : ℂ)`. Use function extensionality and compare the values at `fun k => Complex.conj_ofReal _`. Establish `hH : (Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).conjTranspose = Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.ca …`.

Rewrite using `[Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]`. Establish `him : (Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det.im = 0`. Rewrite using `[← Complex.conj_eq_iff_im]`. Express the relevant statement in the definitionally equal form `star _ = _`. Rewrite using `[← Matrix.det_conjTranspose, hH]`.

Unfold `logDetFlag detGram`. Rewrite using `[(Complex.abs_re_eq_norm.2 him).symm]`.
-/
theorem logDetFlag_eq : LogDetFlagEqStatement := by
  intro N hd m hm
  funext z
  have hs : star (fun k => (hd k : ℂ)) = fun k => (hd k : ℂ) :=
    funext fun k => Complex.conj_ofReal _
  have hH : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).conjTranspose =
      Matrix.submatrix ((cellMat N z).conjTranspose * Matrix.diagonal (fun k => (hd k : ℂ)) *
        cellMat N z) (Fin.castLE hm) (Fin.castLE hm) := by
    rw [Matrix.conjTranspose_submatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.diagonal_conjTranspose, hs, Matrix.mul_assoc]
  have him : (Matrix.submatrix ((cellMat N z).conjTranspose *
      Matrix.diagonal (fun k => (hd k : ℂ)) * cellMat N z) (Fin.castLE hm) (Fin.castLE hm)).det.im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    change star _ = _
    rw [← Matrix.det_conjTranspose, hH]
  unfold logDetFlag detGram
  rw [(Complex.abs_re_eq_norm.2 him).symm]

def DetGramDerivStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N),
    ContDiff ℝ 2 (detGram N hd m hm) ∧
      detGram N hd m hm 0 = ∏ a : Fin m, hd (Fin.castLE hm a) ∧ fderiv ℝ (detGram N hd m hm) 0 = 0

/- English proof (translation)
Introduce `N hd m hm`. Establish `hC` using `contDiff_detGram N hd m hm`. Establish `hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) = fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re` using `fun v => funext (detGram_line N hd m hm v)`. Use `⟨hC, ?_, ?_⟩` and prove the remaining obligations. Establish `h` using `detGram_line N hd m hm 0 0`.

Rewrite `h` using `[smul_zero]`. Rewrite using `[h, Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, (det_gramPolyMinor_coeff_zero_one N hd m hm 0).1, Complex.ofReal_re]`. Use `ContinuousLinearMap.ext fun v => ?_` and prove the remaining obligations. Rewrite using `[fderiv_line_zero (hC.differentiable (by norm_num) 0) v, hl v, deriv_re_eval_zero, (det_gramPolyMinor_coeff_zero_one N hd m hm v).2]`. Simplify using the standard rewrite rules.
-/
theorem detGram_deriv : DetGramDerivStatement := by
  intro N hd m hm
  have hC := contDiff_detGram N hd m hm
  have hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) =
      fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re := fun v => funext (detGram_line N hd m hm v)
  refine ⟨hC, ?_, ?_⟩
  · have h := detGram_line N hd m hm 0 0
    rw [smul_zero] at h
    rw [h, Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, (det_gramPolyMinor_coeff_zero_one N hd m hm 0).1,
      Complex.ofReal_re]
  · refine ContinuousLinearMap.ext fun v => ?_
    rw [fderiv_line_zero (hC.differentiable (by norm_num) 0) v, hl v, deriv_re_eval_zero,
      (det_gramPolyMinor_coeff_zero_one N hd m hm v).2]
    simp

def DetGramLeviStatement : Prop :=
  ∀ (N : ℕ) (hd : Fin N → ℝ), (∀ k, hd k ≠ 0) → ∀ (m : ℕ) (hm : m ≤ N) (w : Pairs N → ℂ),
    levi (detGram N hd m hm) 0 w = (∏ a : Fin m, hd (Fin.castLE hm a)) *
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then hd p.1.2 / hd p.1.1 * ‖w p‖ ^ 2 else 0

/- English proof (translation)
Introduce `N hd hd0 m hm w`. Establish `hC` using `contDiff_detGram N hd m hm`. Establish `hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) = fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re` using `fun v => funext (detGram_line N hd m hm v)`. Rewrite using `[levi_eq_lines hC, hl, hl, deriv2_re_eval_zero, deriv2_re_eval_zero, coeff2_Gm N hd hd0 m hm, coeff2_Gm N hd hd0 m hm, bracket_eq, bracket_eq, sW_I, ← sW_pairs, ← Complex.ofReal_prod, ← Complex.ofReal_mul, Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detGram_levi : DetGramLeviStatement := by
  intro N hd hd0 m hm w
  have hC := contDiff_detGram N hd m hm
  have hl : ∀ v, (fun s : ℝ => detGram N hd m hm (s • v)) =
      fun s : ℝ => ((Gm N hd m hm v).det.eval (s : ℂ)).re := fun v => funext (detGram_line N hd m hm v)
  rw [levi_eq_lines hC, hl, hl, deriv2_re_eval_zero, deriv2_re_eval_zero, coeff2_Gm N hd hd0 m hm,
    coeff2_Gm N hd hd0 m hm, bracket_eq, bracket_eq, sW_I, ← sW_pairs, ← Complex.ofReal_prod,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/- English proof (translation)
Introduce `N hd hd0 m hm w`. Establish `hC` using `contDiff_detGram N hd m hm`. Take `⟨_, h0, h1⟩` from `detGram_deriv N hd m hm`. Establish `hP : (∏ a : Fin m, hd (Fin.castLE hm a)) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hd0 _`. Rewrite using `[logDetFlag_eq N hd m hm, leviHalfLogAbs (detGram N hd m hm) 0 hC.contDiffAt (by rw [h0]; exact hP) h1 w, detGram_levi N hd hd0 m hm w, h0, Finset.mul_sum, Finset.sum_div]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[mul_comm (2 : ℝ), mul_div_mul_left _ _ hP]`. Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules.
-/
theorem homDensity : HomDensityStatement := by
  intro N hd hd0 m hm w
  have hC := contDiff_detGram N hd m hm
  obtain ⟨_, h0, h1⟩ := detGram_deriv N hd m hm
  have hP : (∏ a : Fin m, hd (Fin.castLE hm a)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hd0 _
  rw [logDetFlag_eq N hd m hm, leviHalfLogAbs (detGram N hd m hm) 0 hC.contDiffAt
    (by rw [h0]; exact hP) h1 w, detGram_levi N hd hd0 m hm w, h0, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs
  · rw [mul_comm (2 : ℝ), mul_div_mul_left _ _ hP]
    ring
  · simp

end

end ReciprocityTheory.AnForm.P
