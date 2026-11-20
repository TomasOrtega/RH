import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.CompactDerivativesBounded

open MeasureTheory Matrix Filter Topology
open scoped InnerProductSpace

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.SG.Pf.admitted

open Formalism.MainNotions.S Formalism.REAL Formalism.MainNotions.BridgeCPX

namespace CoordinateExpansion

/- English proof (translation)
Use `letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing`. Use `letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra`. Establish `hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ) ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0`. Conclude with `hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)`. Conclude with `⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, fun Z _ => rfl⟩`.
-/
theorem exp_localHomeo (n : ℕ) :
    ∃ e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ),
      (0 : Matrix (Fin n) (Fin n) ℂ) ∈ e.source ∧ ∀ Z ∈ e.source, e Z = NormedSpace.exp Z := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  have hf : HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix (Fin n) (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ →L[ℂ] Matrix (Fin n) (Fin n) ℂ)) 0 := by
    exact hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix (Fin n) (Fin n) ℂ)
  exact ⟨hf.toOpenPartialHomeomorph _, hf.mem_toOpenPartialHomeomorph_source, fun Z _ => rfl⟩

variable {n : ℕ}

def coord (Z : Matrix (Fin n) (Fin n) ℂ) (p : Fin n × Fin n) : ℝ :=
  if p.1 = p.2 then (Z p.1 p.1).im else if p.1 < p.2 then (Z p.1 p.2).re else (Z p.2 p.1).im

/- English proof (translation)
Unfold `coord`. Use `split_ifs`. Conclude with `Complex.continuous_im.comp (continuous_id.matrix_elem _ _)`. Conclude with `Complex.continuous_re.comp (continuous_id.matrix_elem _ _)`. Conclude with `Complex.continuous_im.comp (continuous_id.matrix_elem _ _)`.
-/
theorem continuous_coord (p : Fin n × Fin n) : Continuous fun Z : Matrix (Fin n) (Fin n) ℂ => coord Z p := by
  unfold coord
  split_ifs
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_re.comp (continuous_id.matrix_elem _ _)
  · exact Complex.continuous_im.comp (continuous_id.matrix_elem _ _)

/- English proof (translation)
Establish `h` using `congrFun (congrFun hZ a) b`. Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Jm, Matrix.conjTranspose_apply, Matrix.zero_apply] at h`. Simplify using `only [sg]`. Apply the tactic sequence `cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h ⊢ <;> first | linear_combination h | linear_combination -h`.
-/
theorem entry_of_inG {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) (a b : Fin n) :
    Z a b = -((sg ε (a, b) : ℝ) : ℂ) * star (Z b a) := by
  have h := congrFun (congrFun hZ a) b
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Jm, Matrix.conjTranspose_apply,
    Matrix.zero_apply] at h
  simp only [sg]
  cases ha : ε a <;> cases hb : ε b <;> simp [ha, hb] at h ⊢ <;>
    first | linear_combination h | linear_combination -h

/- English proof (translation)
Simplify using `only [sg]`. Distinguish the cases in `h : ε a = ε b`. Rewrite using `[if_pos h.symm, if_pos h]`. Rewrite using `[if_neg (fun h' => h h'.symm), if_neg h]`.
-/
theorem sg_swap (ε : Fin n → Bool) (a b : Fin n) : sg ε (b, a) = sg ε (a, b) := by
  simp only [sg]
  by_cases h : ε a = ε b
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (fun h' => h h'.symm), if_neg h]

/- English proof (translation)
Take `⟨p1, p2⟩` from `p`. Simplify using `only [ne_eq, Prod.mk.injEq] at h1 h2`. Unfold `gen`. Apply the tactic sequence `split_ifs <;> simp [Matrix.single_apply] <;> aesop`.
-/
theorem gen_apply_zero (ε : Fin n → Bool) (p : Fin n × Fin n) (i j : Fin n) (h1 : p ≠ (i, j)) (h2 : p ≠ (j, i)) :
    gen ε p i j = 0 := by
  obtain ⟨p1, p2⟩ := p
  simp only [ne_eq, Prod.mk.injEq] at h1 h2
  unfold gen
  split_ifs <;> simp [Matrix.single_apply] <;> aesop

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.sum_apply]`. Simplify using `only [Matrix.smul_apply, smul_eq_mul]`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne]) (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]`.

Simplify using `[coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply]`. Rewrite using `[Fintype.sum_eq_single (i, i) (fun q hq => by rw [gen_apply_zero ε q i i hq hq, mul_zero])]`. Establish `he` using `entry_of_inG hZ i i`. Simplify using `only [sg, if_true] at he`. Establish `hre : (Z i i).re = 0`.

Establish `h2` using `congrArg Complex.re he`. Simplify using `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Simplify using `[coord, gen, Matrix.single_apply]`. Apply the tactic sequence `try (apply Complex.ext <;> simp [hre])`.

Rewrite using `[Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne']) (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]`. Rewrite using `[entry_of_inG hZ i j]`. Simplify using `[coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply, sg_swap]`. Apply the tactic sequence `try (apply Complex.ext <;> simp <;> ring)`.
-/
theorem eq_sum_gen {ε : Fin n → Bool} {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : inG ε Z) :
    Z = ∑ p, ((coord Z p : ℝ) : ℂ) • gen ε p := by
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rcases lt_trichotomy i j with h | rfl | h
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply]
  · rw [Fintype.sum_eq_single (i, i) (fun q hq => by rw [gen_apply_zero ε q i i hq hq, mul_zero])]
    have he := entry_of_inG hZ i i
    simp only [sg, if_true] at he
    have hre : (Z i i).re = 0 := by
      have h2 := congrArg Complex.re he
      simp at h2
      linarith
    simp [coord, gen, Matrix.single_apply]
    try (apply Complex.ext <;> simp [hre])
  · rw [Fintype.sum_eq_add (i, j) (j, i) (by simp [h.ne'])
      (fun q hq => by rw [gen_apply_zero ε q i j hq.1 hq.2, mul_zero])]
    rw [entry_of_inG hZ i j]
    simp [coord, gen, h, h.ne, h.ne', not_lt.mpr h.le, Matrix.single_apply, sg_swap]
    try (apply Complex.ext <;> simp <;> ring)

/- English proof (translation)
Establish `hJJ : Jm ε * Jm ε = 1`. Rewrite using `[Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs <;> norm_num`.

Establish `hJi : (Jm ε)⁻¹ = Jm ε` using `Matrix.inv_eq_left_inv hJJ`. Establish `hJu : IsUnit (Jm ε)` using `(Matrix.isUnit_iff_isUnit_det _).mpr (Matrix.isUnit_det_of_left_inverse hJJ)`. Establish `hJh : (Jm ε)ᴴ = Jm ε`. Rewrite using `[Jm, Matrix.diagonal_conjTranspose]`. Use `congr 1`.

Use function extensionality and compare the values at `a`. Apply the tactic sequence `split_ifs with ha <;> simp [ha]`. Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `hg`. Establish `hgl : (Jm ε * gᴴ * Jm ε) * g = 1`. Rewrite using `[Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ]`.

Establish `hgi : g⁻¹ = Jm ε * gᴴ * Jm ε` using `Matrix.inv_eq_left_inv hgl`. Establish `key : NormedSpace.exp (-(Jm ε * Zᴴ * Jm ε)) = g`. Establish `h1 : -(Jm ε * Zᴴ * Jm ε) = Jm ε * (-Z)ᴴ * (Jm ε)⁻¹`. Rewrite using `[hJi, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]`. Rewrite using `[h1, Matrix.exp_conj _ _ hJu, Matrix.exp_conjTranspose, Matrix.exp_neg, hZg, hgi, hJi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh]`.

Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hJJ, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]`. Establish `hτ : -(Jm ε * Zᴴ * Jm ε) = Z` using `e.injOn hτZ hZ (by rw [hee _ hτZ, hee _ hZ, key, hZg])`. Use `show Zᴴ * Jm ε + Jm ε * Z = 0`. Establish `hJZ : Jm ε * Z = -(Zᴴ * Jm ε)`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]`. Rewrite using `[hJZ, add_neg_cancel]`.
-/
theorem inG_of_log {ε : Fin n → Bool} (e : OpenPartialHomeomorph (Matrix (Fin n) (Fin n) ℂ) (Matrix (Fin n) (Fin n) ℂ))
    (hee : ∀ Z ∈ e.source, e Z = NormedSpace.exp Z) {Z g : Matrix (Fin n) (Fin n) ℂ} (hZ : Z ∈ e.source)
    (hτZ : -(Jm ε * Zᴴ * Jm ε) ∈ e.source) (hg : inUJ ε g) (hZg : NormedSpace.exp Z = g) : inG ε Z := by

  have hJJ : Jm ε * Jm ε = 1 := by
    rw [Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  have hJi : (Jm ε)⁻¹ = Jm ε := Matrix.inv_eq_left_inv hJJ
  have hJu : IsUnit (Jm ε) := (Matrix.isUnit_iff_isUnit_det _).mpr
    (Matrix.isUnit_det_of_left_inverse hJJ)
  have hJh : (Jm ε)ᴴ = Jm ε := by
    rw [Jm, Matrix.diagonal_conjTranspose]
    congr 1
    funext a
    split_ifs with ha <;> simp [ha]
  have hg' : gᴴ * Jm ε * g = Jm ε := hg

  have hgl : (Jm ε * gᴴ * Jm ε) * g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, hg', hJJ]
  have hgi : g⁻¹ = Jm ε * gᴴ * Jm ε := Matrix.inv_eq_left_inv hgl
  have key : NormedSpace.exp (-(Jm ε * Zᴴ * Jm ε)) = g := by
    have h1 : -(Jm ε * Zᴴ * Jm ε) = Jm ε * (-Z)ᴴ * (Jm ε)⁻¹ := by
      rw [hJi, Matrix.conjTranspose_neg, Matrix.mul_neg, Matrix.neg_mul]
    rw [h1, Matrix.exp_conj _ _ hJu, Matrix.exp_conjTranspose, Matrix.exp_neg, hZg, hgi, hJi,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hJh]
    simp only [← Matrix.mul_assoc]
    rw [hJJ, Matrix.one_mul, Matrix.mul_assoc, hJJ, Matrix.mul_one]
  have hτ : -(Jm ε * Zᴴ * Jm ε) = Z := e.injOn hτZ hZ (by rw [hee _ hτZ, hee _ hZ, key, hZg])
  show Zᴴ * Jm ε + Jm ε * Z = 0
  have hJZ : Jm ε * Z = -(Zᴴ * Jm ε) := by
    calc Jm ε * Z = Jm ε * (-(Jm ε * Zᴴ * Jm ε)) := by rw [hτ]
      _ = -(Zᴴ * Jm ε) := by
        rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  rw [hJZ, add_neg_cancel]

end CoordinateExpansion

/- English proof (translation)
Introduce `n ε H _ _ _ σ D hD W C' hC' hdense`. Take `⟨e, he0, hee⟩` from `CoordinateExpansion.exp_localHomeo n`. Use `set M := max C' 0 with hM`. Set `τ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ` to `fun Z => -(Jm ε * Zᴴ * Jm ε)`. Establish `hτ : Continuous τ` using `((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg`.

Set `V : Set (Matrix (Fin n) (Fin n) ℂ)` to `e.source ∩ τ ⁻¹' e.source ∩ {Z | (∑ p, |CoordinateExpansion.coord Z p|) * M < 1 / 2}`. Establish `hVo : IsOpen V`. Use `(e.open_source.inter (e.open_source.preimage hτ)).inter (isOpen_lt ?_ continuous_const)` and prove the remaining obligations. Conclude with `(continuous_finsetSum _ fun p _ => (CoordinateExpansion.continuous_coord p).abs).mul continuous_const`. Establish `hV0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ V`.

Use `⟨⟨he0, ?_⟩, ?_⟩` and prove the remaining obligations. Simplify `he0` using `[τ]`. Simplify using `[CoordinateExpansion.coord]`. Establish `himg : IsOpen (e '' V)` using `e.isOpen_image_of_subset_source hVo (fun Z h => h.1.1)`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ e '' V` using `⟨0, hV0, by rw [hee 0 he0, NormedSpace.exp_zero]⟩`.

Use `⟨(fun g : UJ ε => umat g) ⁻¹' (e '' V), ?_, ?_⟩` and prove the remaining obligations. Conclude with `continuous_umat.continuousAt.preimage_mem_nhds (himg.mem_nhds (by exact h1))`. Introduce and unpack `g ⟨Z, hZV, hZg⟩ v hv`. Establish `hZg' : NormedSpace.exp Z = umat g` using `by rw [← hee Z hZV.1.1]; exact hZg`. Establish `hG : inG ε Z` using `CoordinateExpansion.inG_of_log e hee hZV.1.1 hZV.1.2 (umat_mem g) hZg'`.

Establish `key : ((D ⊓ W : Submodule ℂ H) : Set H) ⊆ {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2}`. Introduce `u hu`. Establish `huD : u ∈ D` using `hu.1`. Establish `huW : u ∈ W` using `hu.2`. Use `show ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2`.

Rewrite using `[← hZg']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hD.lin _ u huD, ← CoordinateExpansion.eq_sum_gen hG]`. Use `_ ≤ ∑ p, |CoordinateExpansion.coord Z p| * (M * ‖u‖) := by`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, Complex.norm_real, Real.norm_eq_abs]`. Use `mul_le_mul_of_nonneg_left ((hC' p u huD huW).trans ?_) (abs_nonneg _)` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)`. Use `_ = ((∑ p, |CoordinateExpansion.coord Z p|) * M) * ‖u‖ := by`. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`.

Conclude with `Finset.sum_congr rfl fun p _ => by ring`. Use `_ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hZV.2.le (norm_nonneg _)`. Use `_ = ‖u‖ / 2 := by ring`. Establish `hcl : IsClosed {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2}` using `isClosed_le (((σ (umat g)).continuous.sub continuous_id).norm) (continuous_norm.div_const _)`. Conclude with `closure_minimal key hcl (hdense v hv)`.
-/
theorem c6 : SmallMotionNeighbourhood := by
  intro n ε H _ _ _ σ D hD W C' hC' hdense
  obtain ⟨e, he0, hee⟩ := CoordinateExpansion.exp_localHomeo n
  set M := max C' 0 with hM
  let τ : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ := fun Z => -(Jm ε * Zᴴ * Jm ε)
  have hτ : Continuous τ :=
    ((continuous_const.matrix_mul continuous_id.matrix_conjTranspose).matrix_mul continuous_const).neg
  let V : Set (Matrix (Fin n) (Fin n) ℂ) :=
    e.source ∩ τ ⁻¹' e.source ∩ {Z | (∑ p, |CoordinateExpansion.coord Z p|) * M < 1 / 2}
  have hVo : IsOpen V := by
    refine (e.open_source.inter (e.open_source.preimage hτ)).inter (isOpen_lt ?_ continuous_const)
    exact (continuous_finsetSum _ fun p _ => (CoordinateExpansion.continuous_coord p).abs).mul continuous_const
  have hV0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ V := by
    refine ⟨⟨he0, ?_⟩, ?_⟩
    · simpa [τ] using he0
    · simp [CoordinateExpansion.coord]
  have himg : IsOpen (e '' V) := e.isOpen_image_of_subset_source hVo (fun Z h => h.1.1)
  have h1 : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ e '' V := ⟨0, hV0, by rw [hee 0 he0, NormedSpace.exp_zero]⟩
  refine ⟨(fun g : UJ ε => umat g) ⁻¹' (e '' V), ?_, ?_⟩
  · exact continuous_umat.continuousAt.preimage_mem_nhds (himg.mem_nhds (by exact h1))
  · rintro g ⟨Z, hZV, hZg⟩ v hv
    have hZg' : NormedSpace.exp Z = umat g := by rw [← hee Z hZV.1.1]; exact hZg
    have hG : inG ε Z := CoordinateExpansion.inG_of_log e hee hZV.1.1 hZV.1.2 (umat_mem g) hZg'
    have key : ((D ⊓ W : Submodule ℂ H) : Set H) ⊆ {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} := by
      intro u hu
      have huD : u ∈ D := hu.1
      have huW : u ∈ W := hu.2
      show ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2
      rw [← hZg']
      calc ‖σ (NormedSpace.exp Z) u - u‖ ≤ ‖dS σ Z u‖ := hD.mv Z hG u huD
        _ = ‖∑ p, ((CoordinateExpansion.coord Z p : ℝ) : ℂ) • dS σ (gen ε p) u‖ := by
          rw [← hD.lin _ u huD, ← CoordinateExpansion.eq_sum_gen hG]
        _ ≤ ∑ p, |CoordinateExpansion.coord Z p| * (M * ‖u‖) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          refine mul_le_mul_of_nonneg_left ((hC' p u huD huW).trans ?_) (abs_nonneg _)
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ = ((∑ p, |CoordinateExpansion.coord Z p|) * M) * ‖u‖ := by
          rw [Finset.sum_mul, Finset.sum_mul]
          exact Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (1 / 2) * ‖u‖ := mul_le_mul_of_nonneg_right hZV.2.le (norm_nonneg _)
        _ = ‖u‖ / 2 := by ring
    have hcl : IsClosed {u : H | ‖σ (umat g) u - u‖ ≤ ‖u‖ / 2} :=
      isClosed_le (((σ (umat g)).continuous.sub continuous_id).norm) (continuous_norm.div_const _)
    exact closure_minimal key hcl (hdense v hv)

end Formalism.L2.SG.Pf.admitted
