import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustStatementPfA

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

open Matrix Topology Filter
open scoped ComplexOrder Matrix
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB

variable {f p q N' : ℕ}

/- English proof (translation)
Take `⟨⟨k, ab⟩, rfl⟩` from `finProdFinEquiv.surjective j`. Take `⟨⟨a, b⟩, rfl⟩` from `finProdFinEquiv.surjective ab`. Establish `h` using `(hw k).diag_pos (i := a)`. Rewrite `h` using `[Complex.lt_def]`. Establish `h1` using `h.1`.

Simplify using `only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re, Complex.re_sum, Complex.zero_re, Complex.star_def, Complex.mul_conj, Complex.ofReal_re] at h1`. Establish `h2 : Complex.normSq (Zof w k a b) ≤ ∑ c, Complex.normSq (Zof w k a c)` using `Finset.single_le_sum (f := fun c => Complex.normSq (Zof w k a c)) (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ b)`. Establish `h3 : ‖Zof w k a b‖ ^ 2 ≤ 1`. Rewrite using `[← Complex.normSq_eq_norm_sq]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h4 : ‖Zof w k a b‖ ≤ 1` using `by nlinarith [norm_nonneg (Zof w k a b)]`. Conclude with `h4`.
-/
theorem coord_le_one {w : V (nD f p q)} (hw : w ∈ Dset f p q) (j : Fin (nD f p q)) :
    ‖w j‖ ≤ 1 := by
  obtain ⟨⟨k, ab⟩, rfl⟩ := finProdFinEquiv.surjective j
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective ab
  have h := (hw k).diag_pos (i := a)
  rw [Complex.lt_def] at h
  have h1 := h.1
  simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply, Matrix.one_apply_eq,
    Complex.sub_re, Complex.one_re, Complex.re_sum, Complex.zero_re, Complex.star_def,
    Complex.mul_conj, Complex.ofReal_re] at h1
  have h2 : Complex.normSq (Zof w k a b) ≤ ∑ c, Complex.normSq (Zof w k a c) :=
    Finset.single_le_sum (f := fun c => Complex.normSq (Zof w k a c))
      (fun c _ => Complex.normSq_nonneg _) (Finset.mem_univ b)
  have h3 : ‖Zof w k a b‖ ^ 2 ≤ 1 := by
    rw [← Complex.normSq_eq_norm_sq]; linarith
  have h4 : ‖Zof w k a b‖ ≤ 1 := by nlinarith [norm_nonneg (Zof w k a b)]
  exact h4

/- English proof (translation)
Unfold `rh`. Rewrite using `[neg_nonneg]`. Conclude with `Finset.sum_nonpos fun k _ => Real.log_nonpos (det_re_pos_im (hw k)).1.le (det_re_le_one (hw k))`.
-/
theorem rh_nonneg {w : V (nD f p q)} (hw : w ∈ Dset f p q) : 0 ≤ rh w := by
  unfold rh
  rw [neg_nonneg]
  exact Finset.sum_nonpos fun k _ => Real.log_nonpos (det_re_pos_im (hw k)).1.le (det_re_le_one (hw k))

def dk (w : V (nD f p q)) (k : Fin f) : ℝ := (1 - Zof w k * (Zof w k)ᴴ).det.re

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_sq_eq]`. Simplify using `only [tPart_apply]`.
-/
theorem normSq_tPart (v : V (nD f p q + N')) :
    ‖tPart v‖ ^ 2 = ∑ j, ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp only [tPart_apply]

/- English proof (translation)
Use extensionality with `v`. Simplify using `only [Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, he⟩`. Establish `hpos : ∀ k, 0 < dk (zPart v) k` using `fun k => (det_re_pos_im (hv k)).1`.

Establish `hG : 0 < ∏ k, dk (zPart v) k` using `Finset.prod_pos fun k _ => hpos k`. Establish `hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k)`. Rewrite using `[Real.log_prod (fun k _ => (hpos k).ne')]`. Both sides reduce to the same expression. Use `⟨fun k => (hv k).posSemidef, ?_⟩` and prove the remaining obligations.

Unfold `eOm at he`. Rewrite `he` using `[hr]`. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨hpsd, hle⟩`. Establish `hG : 0 < ∏ k, dk (zPart v) k` using `(Real.exp_pos _).trans_le hle`.

Establish `hne : ∀ k, dk (zPart v) k ≠ 0`. Introduce `k hk`. Use `Finset.prod_eq_zero (Finset.mem_univ k) hk` as an intermediate fact. Rewrite `hG` using `[this]`. Conclude with `lt_irrefl _ hG`.

Establish `hv : v ∈ OmSet f p q N'`. Introduce `k`. Use `(hpsd k).posDef_iff_det_ne_zero.2 fun h => hne k ?_` and prove the remaining obligations. Simplify using `[dk, h]`. Establish `hpos : ∀ k, 0 < dk (zPart v) k` using `fun k => (det_re_pos_im (hv k)).1`.

Establish `hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k)`. Rewrite using `[Real.log_prod (fun k _ => (hpos k).ne')]`. Both sides reduce to the same expression. Use `⟨hv, ?_⟩` and prove the remaining obligations. Unfold `eOm`.

Rewrite using `[hr]`. Use `Real.log_le_log (Real.exp_pos _) hle` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sub_eq (a : ℝ) :
    {v : V (nD f p q + N') | v ∈ OmSet f p q N' ∧ eOm v ≤ a} =
      {v | (∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖tPart v‖ ^ 2) - a) ≤ ∏ k, dk (zPart v) k} := by
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hv, he⟩
    have hpos : ∀ k, 0 < dk (zPart v) k := fun k => (det_re_pos_im (hv k)).1
    have hG : 0 < ∏ k, dk (zPart v) k := Finset.prod_pos fun k _ => hpos k
    have hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k) := by
      rw [Real.log_prod (fun k _ => (hpos k).ne')]; rfl
    refine ⟨fun k => (hv k).posSemidef, ?_⟩
    unfold eOm at he
    rw [hr] at he
    calc Real.exp (Real.log (1 + ‖tPart v‖ ^ 2) - a) ≤ Real.exp (Real.log (∏ k, dk (zPart v) k)) :=
          Real.exp_le_exp.2 (by linarith)
      _ = _ := Real.exp_log hG
  · rintro ⟨hpsd, hle⟩
    have hG : 0 < ∏ k, dk (zPart v) k := (Real.exp_pos _).trans_le hle
    have hne : ∀ k, dk (zPart v) k ≠ 0 := by
      intro k hk
      have := Finset.prod_eq_zero (Finset.mem_univ k) hk
      rw [this] at hG; exact lt_irrefl _ hG
    have hv : v ∈ OmSet f p q N' := by
      intro k
      refine (hpsd k).posDef_iff_det_ne_zero.2 fun h => hne k ?_
      simp [dk, h]
    have hpos : ∀ k, 0 < dk (zPart v) k := fun k => (det_re_pos_im (hv k)).1
    have hr : rh (zPart v) = -Real.log (∏ k, dk (zPart v) k) := by
      rw [Real.log_prod (fun k _ => (hpos k).ne')]; rfl
    refine ⟨hv, ?_⟩
    unfold eOm
    rw [hr]
    have := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at this
    linarith

/- English proof (translation)
Establish `e : {v : V (nD f p q + N') | ∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef} = ⋂ k, ⋂ x : Fin p → ℂ, {v | 0 ≤ star x ⬝ᵥ ((1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ) *ᵥ x)}`. Use extensionality with `v`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iInter]`. Conclude with `forall_congr' fun k => ⟨fun h => h.dotProduct_mulVec_nonneg, fun h => PosSemidef.of_dotProduct_mulVec_nonneg (herm_one_sub _) h⟩`. Rewrite using `[e]`.

Use `isClosed_iInter fun k => isClosed_iInter fun x => isClosed_le continuous_const ?_` and prove the remaining obligations. Apply the tactic sequence `have hc := cont_entry (fun v : V (nD f p q + N') => zPart v) (fun i => by simp only [zPart_apply]; exact cont_coord _) k`. Simplify using `only [dotProduct, mulVec]`. Conclude with `continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_finsetSum _ fun j _ => (hc i j).mul continuous_const)`.
-/
theorem isClosed_psd :
    IsClosed {v : V (nD f p q + N') | ∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef} := by
  have e : {v : V (nD f p q + N') | ∀ k, (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).PosSemidef} =
      ⋂ k, ⋂ x : Fin p → ℂ, {v | 0 ≤ star x ⬝ᵥ ((1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ) *ᵥ x)} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    exact forall_congr' fun k => ⟨fun h => h.dotProduct_mulVec_nonneg,
      fun h => PosSemidef.of_dotProduct_mulVec_nonneg (herm_one_sub _) h⟩
  rw [e]
  refine isClosed_iInter fun k => isClosed_iInter fun x => isClosed_le continuous_const ?_
  have hc := cont_entry (fun v : V (nD f p q + N') => zPart v)
    (fun i => by simp only [zPart_apply]; exact cont_coord _) k
  simp only [dotProduct, mulVec]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul
    (continuous_finsetSum _ fun j _ => (hc i j).mul continuous_const)

/- English proof (translation)
Simplify using `only [normSq_tPart]`. Use `Continuous.log (continuous_const.add (continuous_finsetSum _ fun j _ => ((cont_coord _).norm).pow 2)) fun v => ?_` and prove the remaining obligations. Check the signs of the components of the expression.
-/
theorem continuous_torusCharacter : Continuous fun v : V (nD f p q + N') => Real.log (1 + ‖tPart v‖ ^ 2) := by
  simp only [normSq_tPart]
  refine Continuous.log (continuous_const.add (continuous_finsetSum _ fun j _ =>
    ((cont_coord _).norm).pow 2)) fun v => ?_
  positivity

/- English proof (translation)
Use `continuous_finsetProd _ fun k _ => Complex.continuous_re.comp ?_` and prove the remaining obligations. Apply the tactic sequence `have hc := cont_entry (fun v : V (nD f p q + N') => zPart v) (fun i => by simp only [zPart_apply]; exact cont_coord _) k`. Conclude with `(continuous_pi fun a => continuous_pi fun b => hc a b).matrix_det`.
-/
theorem cont_G : Continuous fun v : V (nD f p q + N') => ∏ k, dk (zPart v) k := by
  refine continuous_finsetProd _ fun k _ => Complex.continuous_re.comp ?_
  have hc := cont_entry (fun v : V (nD f p q + N') => zPart v)
    (fun i => by simp only [zPart_apply]; exact cont_coord _) k
  exact (continuous_pi fun a => continuous_pi fun b => hc a b).matrix_det

/- English proof (translation)
Use `Metric.isCompact_of_isClosed_isBounded ?_ ?_` and prove the remaining obligations. Rewrite using `[sub_eq]`. Conclude with `isClosed_psd.inter (isClosed_le (Real.continuous_exp.comp (continuous_torusCharacter.sub continuous_const)) cont_G)`. Use `isBounded_iff_forall_norm_le.2 ⟨(nD f p q + N') * (1 + Real.exp a) + 1, ?_⟩` and prove the remaining obligations. Introduce and unpack `v ⟨hv, he⟩`.

Establish `hT : Real.log (1 + ‖tPart v‖ ^ 2) ≤ a`. Use `rh_nonneg hv` as an intermediate fact. Unfold `eOm at he`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT2 : ‖tPart v‖ ^ 2 ≤ Real.exp a`.

Establish `h` using `Real.exp_le_exp.2 hT`. Rewrite using `[Real.exp_log (by positivity)] at h; linarith`. Establish `hco : ∀ i, ‖v i‖ ^ 2 ≤ 1 + Real.exp a`. Introduce `i`. Use `Fin.addCases (fun j => ?_) (fun j => ?_) i` and prove the remaining obligations.

Establish `h` using `coord_le_one hv j`. Rewrite `h` using `[zPart_apply]`. Establish `: ‖v (Fin.castAdd N' j)‖ ^ 2 ≤ 1` using `by nlinarith [norm_nonneg (v (Fin.castAdd N' j))]`. Combine the linear relations using `[Real.exp_pos a]`. Establish `h` using `normSq_tPart v`.

Establish `h2 : ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2 ≤ ‖tPart v‖ ^ 2`. Rewrite using `[h]`. Conclude with `Finset.single_le_sum (f := fun j => ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hn : ‖v‖ ^ 2 ≤ (nD f p q + N') * (1 + Real.exp a)`.

Rewrite using `[EuclideanSpace.norm_sq_eq]`. Combine the equalities or inequalities in the displayed calculation. Establish `h0 : 0 ≤ ((nD f p q + N' : ℕ) : ℝ) * (1 + Real.exp a)` using `by positivity`. Move the coercions through the operations in `at h0`. Use polynomial arithmetic with `[norm_nonneg v]`.
-/
theorem isCompact_sub (a : ℝ) :
    IsCompact {v : V (nD f p q + N') | v ∈ OmSet f p q N' ∧ eOm v ≤ a} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · rw [sub_eq]
    exact isClosed_psd.inter (isClosed_le (Real.continuous_exp.comp (continuous_torusCharacter.sub continuous_const)) cont_G)
  · refine isBounded_iff_forall_norm_le.2 ⟨(nD f p q + N') * (1 + Real.exp a) + 1, ?_⟩
    rintro v ⟨hv, he⟩
    have hT : Real.log (1 + ‖tPart v‖ ^ 2) ≤ a := by
      have := rh_nonneg hv; unfold eOm at he; linarith
    have hT2 : ‖tPart v‖ ^ 2 ≤ Real.exp a := by
      have h := Real.exp_le_exp.2 hT
      rw [Real.exp_log (by positivity)] at h; linarith
    have hco : ∀ i, ‖v i‖ ^ 2 ≤ 1 + Real.exp a := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · have h := coord_le_one hv j
        rw [zPart_apply] at h
        have : ‖v (Fin.castAdd N' j)‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (v (Fin.castAdd N' j))]
        linarith [Real.exp_pos a]
      · have h := normSq_tPart v
        have h2 : ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2 ≤ ‖tPart v‖ ^ 2 := by
          rw [h]
          exact Finset.single_le_sum (f := fun j => ‖v (Fin.natAdd (nD f p q) j)‖ ^ 2)
            (fun _ _ => by positivity) (Finset.mem_univ j)
        linarith
    have hn : ‖v‖ ^ 2 ≤ (nD f p q + N') * (1 + Real.exp a) := by
      rw [EuclideanSpace.norm_sq_eq]
      calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin (nD f p q + N'), (1 + Real.exp a) :=
            Finset.sum_le_sum fun i _ => hco i
        _ = _ := by simp; ring
    have h0 : 0 ≤ ((nD f p q + N' : ℕ) : ℝ) * (1 + Real.exp a) := by positivity
    push_cast at h0
    nlinarith [norm_nonneg v]

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD

open Matrix Topology Filter
open scoped ComplexOrder Matrix ContDiff
open ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC

variable {f p q N' : ℕ}

/- English proof (translation)
Establish `e : (fun x => (M x).det) = fun x => ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.det_apply']`. Rewrite using `[e]`. Conclude with `ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)`.
-/
theorem contDiff_det_of {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 ℂ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] {m : ℕ} {M : E → Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ i j, ContDiff 𝕜 ∞ fun x => M x i j) : ContDiff 𝕜 ∞ fun x => (M x).det := by
  have e : (fun x => (M x).det) = fun x =>
      ∑ σ : Equiv.Perm (Fin m), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, M x (σ j) j := by
    funext x; rw [Matrix.det_apply']
  rw [e]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun j _ => h _ _)

/- English proof (translation)
Establish `h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ)`. Use function extensionality and compare the values at `v`. Simplify using the standard rewrite rules. Rewrite using `[h]`. Conclude with `ContinuousLinearMap.contDiff _`.
-/
theorem cd_coord {n : ℕ} (i : Fin n) : ContDiff ℂ ∞ fun v : V n => v i := by
  have h : (fun v : V n => v i) = ⇑(EuclideanSpace.proj i : V n →L[ℂ] ℂ) := by
    funext v; simp
  rw [h]; exact ContinuousLinearMap.contDiff _

def dkC (k : Fin f) (v : V (nD f p q + N')) : ℂ :=
  (1 - Zof (zPart v) k * (Zof (zPart v) k)ᴴ).det

def Hh (W : V (nD f p q)) (v : V (nD f p q + N')) : ℂ :=
  ∏ k, (1 - Zof (zPart v) k * (Zof W k)ᴴ).det

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD
