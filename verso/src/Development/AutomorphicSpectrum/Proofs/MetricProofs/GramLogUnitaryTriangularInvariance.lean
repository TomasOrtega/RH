import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsOpenFlagDomainNondegenerateMinorsStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open Matrix Topology
open scoped ComplexOrder

/- English proof (translation)
Use `set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef`. Establish `hK : IsCompact K` using `isCompact_sphere 0 1`. Establish `hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re`. Simplify using `only [dotProduct, mulVec]`. Use `Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)` and prove the remaining obligations.

Conclude with `(continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul (continuous_finsetSum _ fun j _ => ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))`. Establish `hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y), 0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re`. Introduce `y hy`. Establish `hy0 : y ≠ 0` using `by rintro rfl; simp [hKdef] at hy`. Establish `h` using `h0.dotProduct_mulVec_pos hy0`.

Rewrite `h` using `[Complex.lt_def]`. Conclude with `(hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)`. Use `filter_upwards [hK.eventually_forall_of_forall_eventually (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx`. Use `PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_` and prove the remaining obligations. Establish `hn : 0 < ‖y‖` using `norm_pos_iff.2 hy`.

Establish `hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K`. Simplify using `[hKdef, norm_smul, hn.ne']`. Establish `h1` using `hx _ hyK`. Establish `e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) = ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y))`. Rewrite using `[star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]`.

Simplify using `only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[e, Complex.re_ofReal_mul]`. Establish `him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0`.

Rewrite using `[← Complex.conj_eq_iff_im]`. Simplify using `only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def, Complex.conj_conj, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h` using `(hH x).apply i j`.

Rewrite `h` using `[Complex.star_def]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Complex.lt_def]`. Use `⟨?_, by simpa using him.symm⟩` and prove the remaining obligations.

Use `pos_of_mul_pos_right h1 (by positivity)` as an intermediate fact. Simplify using `using this`.
-/
theorem posDef_eventually_of_continuous {X n : Type*} [TopologicalSpace X] [Fintype n] [DecidableEq n]
    (A : X → Matrix n n ℂ) (hc : ∀ i j, Continuous fun x => A x i j)
    (hH : ∀ x, (A x).IsHermitian) (x0 : X) (h0 : (A x0).PosDef) :
    ∀ᶠ x in 𝓝 x0, (A x).PosDef := by
  set K : Set (n → ℂ) := Metric.sphere 0 1 with hKdef
  have hK : IsCompact K := isCompact_sphere 0 1
  have hQ : Continuous fun z : X × (n → ℂ) => (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    simp only [dotProduct, mulVec]
    refine Complex.continuous_re.comp (continuous_finsetSum _ fun i _ => ?_)
    exact (continuous_star.comp ((continuous_apply i).comp continuous_snd)).mul
      (continuous_finsetSum _ fun j _ =>
        ((hc i j).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd))
  have hP : ∀ y ∈ K, ∀ᶠ z : X × (n → ℂ) in 𝓝 (x0, y),
      0 < (star z.2 ⬝ᵥ (A z.1 *ᵥ z.2)).re := by
    intro y hy
    have hy0 : y ≠ 0 := by rintro rfl; simp [hKdef] at hy
    have h := h0.dotProduct_mulVec_pos hy0
    rw [Complex.lt_def] at h
    exact (hQ.tendsto (x0, y)).eventually_const_lt (by simpa using h.1)
  filter_upwards [hK.eventually_forall_of_forall_eventually
    (P := fun x y => 0 < (star y ⬝ᵥ (A x *ᵥ y)).re) hP] with x hx
  refine PosDef.of_dotProduct_mulVec_pos (hH x) fun y hy => ?_
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hyK : ((‖y‖⁻¹ : ℝ) : ℂ) • y ∈ K := by
    simp [hKdef, norm_smul, hn.ne']
  have h1 := hx _ hyK
  have e : star (((‖y‖⁻¹ : ℝ) : ℂ) • y) ⬝ᵥ (A x *ᵥ (((‖y‖⁻¹ : ℝ) : ℂ) • y)) =
      ((‖y‖⁻¹ ^ 2 : ℝ) : ℂ) * (star y ⬝ᵥ (A x *ᵥ y)) := by
    rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul, Complex.star_def, Complex.conj_ofReal]
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have him : (star y ⬝ᵥ (A x *ᵥ y)).im = 0 := by
    rw [← Complex.conj_eq_iff_im]
    simp only [dotProduct, mulVec, map_sum, map_mul, Pi.star_apply, Complex.star_def,
      Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := (hH x).apply i j
    rw [Complex.star_def] at h
    rw [h]; ring
  rw [Complex.lt_def]
  refine ⟨?_, by simpa using him.symm⟩
  have := pos_of_mul_pos_right h1 (by positivity)
  simpa using this

/- English proof (translation)
Unfold `gramOf`. Use `isHermitian_conjTranspose_mul_mul g ?_` and prove the remaining obligations. Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[diagonal_apply, h, Ne.symm h]`.
-/
theorem gramOf_isHermitian {N : ℕ} (hd : Fin N → ℝ) (g : Matrix (Fin N) (Fin N) ℂ) :
    (gramOf hd g).IsHermitian := by
  unfold gramOf
  refine isHermitian_conjTranspose_mul_mul g ?_
  ext i j
  by_cases h : i = j
  · subst h; simp
  · simp [diagonal_apply, h, Ne.symm h]

/- English proof (translation)
Unfold `gramHead gramOf`. Conclude with `(((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul continuous_id).matrix_submatrix _ _`.
-/
theorem continuous_gramHead {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) :
    Continuous fun g : Matrix (Fin N) (Fin N) ℂ => gramHead hd k g := by
  unfold gramHead gramOf
  exact (((continuous_id.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul
    continuous_id).matrix_submatrix _ _

/- English proof (translation)
Establish `h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det}`. Simplify using `only [isUnit_iff_ne_zero]`. Conclude with `isOpen_ne_fun (continuous_id.matrix_det) continuous_const`. Establish `h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef}`. Use `isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_` and prove the remaining obligations.

Use `posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_) (fun g => ?_) g0 hg0` and prove the remaining obligations. Conclude with `((continuous_gramHead _ _).neg).matrix_elem a b`. Conclude with `((gramOf_isHermitian _ g).submatrix _).neg`. Conclude with `h1.inter h2`.
-/
theorem isOpen_inFlagDomain (N j : ℕ) :
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} := by
  have h1 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | IsUnit g.det} := by
    simp only [isUnit_iff_ne_zero]
    exact isOpen_ne_fun (continuous_id.matrix_det) continuous_const
  have h2 : IsOpen {g : Matrix (Fin N) (Fin N) ℂ | (-gramHead (sigForm N j) (N - j) g).PosDef} := by
    refine isOpen_iff_mem_nhds.2 fun g0 hg0 => ?_
    refine posDef_eventually_of_continuous (fun g => -gramHead (sigForm N j) (N - j) g) (fun a b => ?_)
      (fun g => ?_) g0 hg0
    · exact ((continuous_gramHead _ _).neg).matrix_elem a b
    · exact ((gramOf_isHermitian _ g).submatrix _).neg
  exact h1.inter h2

/- English proof (translation)
Unfold `gramOf at hu ⊢`. Rewrite using `[conjTranspose_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hu]`.
-/
theorem gramOf_mul_of_preserves {N : ℕ} (hd : Fin N → ℝ) (u g : Matrix (Fin N) (Fin N) ℂ)
    (hu : gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ))) :
    gramOf hd (u * g) = gramOf hd g := by
  unfold gramOf at hu ⊢
  rw [conjTranspose_mul]
  calc gᴴ * uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * (u * g)
      = gᴴ * (uᴴ * diagonal (fun i => ((hd i : ℝ) : ℂ)) * u) * g := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [hu]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [gramHead, gramOf, submatrix_apply]`. Rewrite using `[mul_apply, mul_apply]`. Simplify using `only [mul_diagonal, conjTranspose_apply, submatrix_apply]`. Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp) (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]`.

Rewrite using `[Finset.sum_filter_of_ne]`. Introduce `l _ hl`. Assume the negation of the conclusion as `hlk`. Apply `hl` to reduce the goal to its premises. Establish `: b l i.1 = 0` using `hb (by show i.1 < l`.

Use `i.2` as an intermediate fact. Conclude with `Fin.lt_def.2 (by omega))`. Simplify using `[this]`.
-/
theorem gramHead_of_triangular {N : ℕ} (hd : Fin N → ℝ) (k : ℕ) (b : Matrix (Fin N) (Fin N) ℂ)
    (hb : b.BlockTriangular id) :
    gramHead hd k b = (b.submatrix Subtype.val Subtype.val)ᴴ *
      diagonal (fun a : {a : Fin N // (a : ℕ) < k} => ((hd a : ℝ) : ℂ)) *
      b.submatrix Subtype.val Subtype.val := by
  ext i j
  simp only [gramHead, gramOf, submatrix_apply]
  rw [mul_apply, mul_apply]
  simp only [mul_diagonal, conjTranspose_apply, submatrix_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun a : Fin N => (a : ℕ) < k) (by simp)
    (fun l => star (b l i.1) * ((hd l : ℝ) : ℂ) * b l j.1)]
  rw [Finset.sum_filter_of_ne]
  intro l _ hl
  by_contra hlk
  apply hl
  have : b l i.1 = 0 := hb (by
    show i.1 < l
    have := i.2
    exact Fin.lt_def.2 (by omega))
  simp [this]

/- English proof (translation)
Apply the tactic sequence `unfold sigForm; split_ifs <;> norm_num`.
-/
theorem sigForm_apply_ne_zero (N j : ℕ) (a : Fin N) : sigForm N j a ≠ 0 := by
  unfold sigForm; split_ifs <;> norm_num

/- English proof (translation)
Establish `hbd : ∀ i, b i i ≠ 0`. Establish `h` using `(isUnit_iff_ne_zero.1 hu)`. Rewrite `h` using `[det_of_upperTriangular hb]`. Conclude with `fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)`. Establish `hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0`.

Establish `ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id` using `fun i j hij => hb hij`. Rewrite using `[det_of_upperTriangular ht]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1`. Rewrite using `[gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]`. Use `mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs` and prove the remaining obligations.

Conclude with `Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)`.
-/
theorem gramHead_det_ne_zero_of_triangular {N : ℕ} (hd : Fin N → ℝ) (hd0 : ∀ a, hd a ≠ 0) (k : ℕ)
    (b : Matrix (Fin N) (Fin N) ℂ) (hb : b.BlockTriangular id) (hu : IsUnit b.det) :
    (gramHead hd k b).det ≠ 0 := by
  have hbd : ∀ i, b i i ≠ 0 := by
    have h := (isUnit_iff_ne_zero.1 hu)
    rw [det_of_upperTriangular hb] at h
    exact fun i => (Finset.prod_ne_zero_iff.1 h) i (Finset.mem_univ i)
  have hs : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).det ≠ 0 := by
    have ht : (b.submatrix (Subtype.val : {a : Fin N // (a : ℕ) < k} → Fin N) Subtype.val).BlockTriangular id :=
      fun i j hij => hb hij
    rw [det_of_upperTriangular ht]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hbd i.1
  rw [gramHead_of_triangular hd k b hb, det_mul, det_mul, det_conjTranspose, det_diagonal]
  refine mul_ne_zero (mul_ne_zero (star_ne_zero.2 hs) ?_) hs
  exact Finset.prod_ne_zero_iff.2 fun a _ => Complex.ofReal_ne_zero.2 (hd0 a)

/- English proof (translation)
Take `⟨u, b, hu, hb, hbu, hug⟩` from `GlobalTheory.T.flag_domain_unitary_triangular N j hj g hg`. Establish `e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b`. Unfold `gramHead`. Rewrite using `[← hug, gramOf_mul_of_preserves _ _ _ hu]`. Rewrite using `[e]`.

Conclude with `gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu`.
-/
theorem gramHead_det_ne_zero (N j : ℕ) (hj : j ≤ N) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : InFlagDomain N j g) (k : ℕ) : (gramHead (sigForm N j) k g).det ≠ 0 := by
  obtain ⟨u, b, hu, hb, hbu, hug⟩ := GlobalTheory.T.flag_domain_unitary_triangular N j hj g hg
  have e : gramHead (sigForm N j) k g = gramHead (sigForm N j) k b := by
    unfold gramHead
    rw [← hug, gramOf_mul_of_preserves _ _ _ hu]
  rw [e]
  exact gramHead_det_ne_zero_of_triangular _ (sigForm_apply_ne_zero N j) k b hb hbu

/- English proof (translation)
Introduce `N j hj` and use `⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩`.
-/
theorem flagDomain_open_and_minors : ∀ (N j : ℕ), j ≤ N →
    IsOpen {g : Matrix (Fin N) (Fin N) ℂ | InFlagDomain N j g} ∧
      ∀ g : Matrix (Fin N) (Fin N) ℂ, InFlagDomain N j g → ∀ k,
        (gramHead (sigForm N j) k g).det ≠ 0 :=
  fun N j hj => ⟨isOpen_inFlagDomain N j, fun g hg k => gramHead_det_ne_zero N j hj g hg k⟩

end GlobalTheory.CompanionTheory.Ar.PB
