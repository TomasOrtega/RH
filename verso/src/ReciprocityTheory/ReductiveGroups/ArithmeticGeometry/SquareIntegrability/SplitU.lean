import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SplitC
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceMinima

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

section lin

variable {dim : (E →+* ℂ) → ℕ}

/- English proof (translation)
Use `⟨add_mem hu.1 hv.1, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hH : Hf (x + y) a = Hf x a + Hf y a`. Simplify using `[Hf, add_mul, Finset.sum_add_distrib]`. Rewrite using `[inner_add_left, hu.2 a ha, hv.2 a ha, hH, Complex.add_im]`.
-/
theorem IsU.add' {I : Submodule ℤ (Vsp dim)} {x y u v : Vsp dim} (hu : IsU I x u)
    (hv : IsU I y v) : IsU I (x + y) (u + v) := by
  refine ⟨add_mem hu.1 hv.1, fun a ha => ?_⟩
  have hH : Hf (x + y) a = Hf x a + Hf y a := by
    simp [Hf, add_mul, Finset.sum_add_distrib]
  rw [inner_add_left, hu.2 a ha, hv.2 a ha, hH, Complex.add_im]

/- English proof (translation)
Conclude with `⟨zero_mem _, fun a _ => by simp [Hf]⟩`.
-/
theorem IsU.zero' (I : Submodule ℤ (Vsp dim)) : IsU I 0 0 := by
  exact ⟨zero_mem _, fun a _ => by simp [Hf]⟩

/- English proof (translation)
Use `⟨zsmul_mem hu.1 k, fun a ha => ?_⟩` and prove the remaining obligations. Establish `hH : Hf (k • x) a = (k : ℂ) * Hf x a`. Simplify using `only [Hf]`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `[mul_assoc]`. Rewrite using `[← Int.cast_smul_eq_zsmul ℝ k u, real_inner_smul_left, hu.2 a ha, hH]`. Simplify using the standard rewrite rules.
-/
theorem IsU.zsmul' {I : Submodule ℤ (Vsp dim)} {x u : Vsp dim} (k : ℤ) (hu : IsU I x u) :
    IsU I (k • x) (k • u) := by
  refine ⟨zsmul_mem hu.1 k, fun a ha => ?_⟩
  have hH : Hf (k • x) a = (k : ℂ) * Hf x a := by
    simp only [Hf]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [mul_assoc]
  rw [← Int.cast_smul_eq_zsmul ℝ k u, real_inner_smul_left, hu.2 a ha, hH]
  simp

end lin

/- English proof (translation)
Establish `hH : ∀ y, Hf y a = inner ℂ a y` using `fun y => by`. Simplify using `[Hf, PiLp.inner_apply, mul_comm]`. Establish `hf : (Complex.imLm.comp ((innerₛₗ ℂ a).restrictScalars ℝ) : Vsp X.dim →ₗ[ℝ] ℝ) = 0` using `X.b.ext fun i => by`. Simplify `h (X.b i) (Submodule.subset_span ⟨i, rfl⟩)` using `[← hH]`. Establish `h0 : (inner ℂ a ((Complex.I : ℂ) • a)).im = 0`.

Use `LinearMap.congr_fun hf ((Complex.I : ℂ) • a)` as an intermediate fact. Use `first`. Consider the case `exact this`. Consider the case `(simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, innerₛₗ_apply, LinearMap.zero_apply] at this`. Conclude with `this)`.

Rewrite `h0` using `[inner_smul_right, inner_self_eq_norm_sq_to_K]`. Establish `h2 : ‖a‖ ^ 2 = 0`. Establish `h3 : (Complex.I * ((‖a‖ : ℂ) ^ 2)).im = ‖a‖ ^ 2`. Rewrite using `[← Complex.ofReal_pow, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← h3]`. Conclude with `h0`. Simplify using `using h2`.
-/
theorem eq_zero_of_im_L (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, (Hf y a).im = 0) : a = 0 := by
  have hH : ∀ y, Hf y a = inner ℂ a y := fun y => by
    simp [Hf, PiLp.inner_apply, mul_comm]
  have hf : (Complex.imLm.comp ((innerₛₗ ℂ a).restrictScalars ℝ) : Vsp X.dim →ₗ[ℝ] ℝ) = 0 :=
    X.b.ext fun i => by
      simpa [← hH] using h (X.b i) (Submodule.subset_span ⟨i, rfl⟩)
  have h0 : (inner ℂ a ((Complex.I : ℂ) • a)).im = 0 := by
    have := LinearMap.congr_fun hf ((Complex.I : ℂ) • a)
    first
      | exact this
      | (simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, innerₛₗ_apply,
          LinearMap.zero_apply] at this
         exact this)
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
  have h2 : ‖a‖ ^ 2 = 0 := by
    have h3 : (Complex.I * ((‖a‖ : ℂ) ^ 2)).im = ‖a‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [← h3]
    exact h0
  simpa using h2

/- English proof (translation)
Establish `hadd : ∀ y y' : Vsp X.dim, (Hf (y + y') a).im = (Hf y a).im + (Hf y' a).im` using `fun y y' => by simp [Hf, add_mul, Finset.sum_add_distrib]`. Set `φ : X.L →+ ℤ` to `{ toFun := fun y => (h (y : Vsp X.dim) y.2).choose map_zero' := by`. Establish `e` using `(h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose_spec`. Establish `e' : (((h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose : ℤ) : ℝ) = 0`. Rewrite using `[← e]`.

Simplify using `[Hf]`. Conclude with `e'` after adjusting the coercions. Use the proof step `map_add' := fun y y' => by`. Establish `e1` using `(h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose_spec`. Establish `e2` using `(h (y : Vsp X.dim) y.2).choose_spec`.

Establish `e3` using `(h (y' : Vsp X.dim) y'.2).choose_spec`. Establish `e' : (((h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose : ℤ) : ℝ) = (h (y : Vsp X.dim) y.2).choose + (h (y' : Vsp X.dim) y'.2).choose`. Rewrite using `[← e1, ← e2, ← e3, Submodule.coe_add, hadd]`. Conclude with `e' }` after adjusting the coercions. Take `⟨x, hx, hxy⟩` from `X.perfect φ`.

Establish `key : a + x = 0`. Apply `eq_zero_of_im_L X` to reduce the goal to its premises. Introduce `y hy`. Establish `h1 : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf x y).im` using `hxy ⟨y, hy⟩`. Establish `hφ : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf y a).im` using `(h y hy).choose_spec.symm`.

Establish `hc : (Hf y x).im = -(Hf x y).im`. Establish `hcj : Hf y x = starRingEnd ℂ (Hf x y)` using `by simp [Hf, map_sum, mul_comm]`. Rewrite using `[hcj, Complex.conj_im]`. Establish `hr : Hf y (a + x) = Hf y a + Hf y x` using `by simp [Hf, mul_add, Finset.sum_add_distrib]`. Rewrite using `[hr, Complex.add_im, hc, ← h1, hφ]`.

Expand and normalize the polynomial expressions, which then agree. Establish `ha : a = -x` using `eq_neg_of_add_eq_zero_left key`. Rewrite using `[ha]`. Conclude with `neg_mem hx`.
-/
theorem mem_L_of_int (X : PT E) {a : Vsp X.dim} (h : ∀ y ∈ X.L, ∃ k : ℤ, (Hf y a).im = k) :
    a ∈ X.L := by
  have hadd : ∀ y y' : Vsp X.dim, (Hf (y + y') a).im = (Hf y a).im + (Hf y' a).im :=
    fun y y' => by simp [Hf, add_mul, Finset.sum_add_distrib]
  let φ : X.L →+ ℤ :=
    { toFun := fun y => (h (y : Vsp X.dim) y.2).choose
      map_zero' := by
        have e := (h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose_spec
        have e' : (((h ((0 : X.L) : Vsp X.dim) (0 : X.L).2).choose : ℤ) : ℝ) = 0 := by
          rw [← e]
          simp [Hf]
        exact_mod_cast e'
      map_add' := fun y y' => by
        have e1 := (h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose_spec
        have e2 := (h (y : Vsp X.dim) y.2).choose_spec
        have e3 := (h (y' : Vsp X.dim) y'.2).choose_spec
        have e' : (((h ((y + y' : X.L) : Vsp X.dim) (y + y').2).choose : ℤ) : ℝ) =
            (h (y : Vsp X.dim) y.2).choose + (h (y' : Vsp X.dim) y'.2).choose := by
          rw [← e1, ← e2, ← e3, Submodule.coe_add, hadd]
        exact_mod_cast e' }
  obtain ⟨x, hx, hxy⟩ := X.perfect φ
  have key : a + x = 0 := by
    apply eq_zero_of_im_L X
    intro y hy
    have h1 : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf x y).im := hxy ⟨y, hy⟩
    have hφ : ((φ ⟨y, hy⟩ : ℤ) : ℝ) = (Hf y a).im := (h y hy).choose_spec.symm
    have hc : (Hf y x).im = -(Hf x y).im := by
      have hcj : Hf y x = starRingEnd ℂ (Hf x y) := by simp [Hf, map_sum, mul_comm]
      rw [hcj, Complex.conj_im]
    have hr : Hf y (a + x) = Hf y a + Hf y x := by simp [Hf, mul_add, Finset.sum_add_distrib]
    rw [hr, Complex.add_im, hc, ← h1, hφ]
    ring
  have ha : a = -x := eq_neg_of_add_eq_zero_left key
  rw [ha]
  exact neg_mem hx

/- English proof (translation)
Use `set K := IR I with hK`. Use `set N := Module.finrank ℝ K with hNdef`. Set `e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N)` to `(stdOrthonormalBasis ℝ K).repr`. Set `M : Submodule ℤ (EuclideanSpace ℝ (Fin N))` to `{ carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)} add_mem' := by`. Introduce and unpack `z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩`.

Conclude with `⟨y + y', X.L.add_mem hy hy', by simpa using hu.add' hu'⟩`. Use the proof step `zero_mem' := ⟨0, X.L.zero_mem, by simpa using IsU.zero' I⟩`. Use the proof step `smul_mem' := by`. Introduce and unpack `k z ⟨y, hy, hu⟩`. Conclude with `⟨k • y, X.L.smul_mem k hy, by simpa using hu.zsmul' k⟩ }`.

Establish `hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u` using `fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩`. Establish `hinner : ∀ z z' : EuclideanSpace ℝ (Fin N), ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ`. Introduce `z z'`. Rewrite using `[← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]`. Establish `hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖`.

Introduce `z`. Rewrite using `[← e.symm.norm_map z]`. Both sides reduce to the same expression. Establish `hdual : ∀ z ∈ PI.dualZ M, ((e.symm z : K) : Vsp X.dim) ∈ I`. Introduce `z hz`.

Apply `hsat _ ?_ (e.symm z).2` to reduce the goal to its premises. Apply `mem_L_of_int X` to reduce the goal to its premises. Introduce `y hy`. Take `⟨u, hu⟩` from `exists_isU I y`. Take `⟨z', hz'M, hz'⟩` from `hmemM y hy u hu`.

Take `⟨k, hk⟩` from `hz z' hz'M`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]`. Break down `Nat.eq_zero_or_pos N with hN0 | hNpos` into its components or cases. Establish `: IsEmpty (Fin N)` using `by rw [hN0]; infer_instance`.

Conclude with `⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type, fun j => isEmptyElim j⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a0, ha0I, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hK0 : K = ⊥`.

Rewrite using `[eq_bot_iff, hK]`. Conclude with `Submodule.span_le.2 (fun a ha => by simp [hcon a ha])`. Establish `: N = 0` using `by rw [hNdef, hK0]; exact finrank_bot ℝ _`. Use linear arithmetic over natural numbers and integers. Establish `hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤`.

Rewrite using `[← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]`. Introduce `z hz`. Establish `h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0` using `fun z' hz' => (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')`. Establish `ha : ((e.symm z : K) : Vsp X.dim) = 0`. Apply `eq_zero_of_im_L X` to reduce the goal to its premises.

Introduce `y hy`. Take `⟨u, hu⟩` from `exists_isU I y`. Take `⟨z', hz'M, hz'⟩` from `hmemM y hy u hu`. Rewrite using `[← hu.2 _ (e.symm z).2, ← hz', ← hinner]`. Conclude with `h0 z' hz'M`.

Establish `: e.symm z = 0` using `Subtype.ext ha`. Simplify using `using congrArg e this`. Take `⟨s, hsI, hsspan, hsli⟩` from `exists_linearIndependent ℝ (I : Set (Vsp X.dim))`. Establish `hsfin : s.Finite` using `hsli.setFinite`. Use `set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA`.

Establish `hApos : 0 < A`. Establish `: 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖` using `Finset.sum_nonneg (fun _ _ => norm_nonneg _)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖`. Introduce `z hzM hz0`.

Take `⟨y, hy, hu⟩` from `hzM`. Use `set u := ((e.symm z : K) : Vsp X.dim)`. Establish `hu0 : u ≠ 0`. Introduce `h0`. Apply `hz0` to reduce the goal to its premises.

Establish `: e.symm z = 0` using `Subtype.ext h0`. Simplify using `using congrArg e this`. Choose the witnesses or unpack the hypotheses as in `⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `: ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0`. Introduce `w hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx => exact hcon x hx`. Consider the case `zero => exact inner_zero_right _`.

Consider the case `add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]`. Consider the case `smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]`. Establish `h1` using `this u (by rw [hsspan]; exact hu.1)`. Conclude with `hu0 (inner_self_eq_zero.1 h1)`. Establish `h1 : 1 ≤ |⟪u, a⟫_ℝ|`.

Rewrite using `[hu.2 a (mem_IR (hsI has))]`. Rewrite `ha` using `[hu.2 a (mem_IR (hsI has))]`. Conclude with `one_le_abs_im X hy (hle (hsI has)) ha`. Establish `h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖` using `abs_real_inner_le_norm _ _`. Establish `h3 : ‖a‖ ≤ A`.

Use `Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _) ((Set.Finite.mem_toFinset hsfin).2 has)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hnormE z, div_le_iff₀ hApos]`. Use polynomial arithmetic with `[norm_nonneg u]`. Establish `hdisc : DiscreteTopology M`.

Rewrite using `[discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]`. Use `⟨1 / A, by positivity, fun z hz => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hz0`. Establish `h1` using `hlow z z.2 (fun h => hz0 (Subtype.ext h))`. Rewrite `hz` using `[dist_zero_right]`.

Establish `: ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT` using `transference_successive_minima N M hdisc hspan N hNpos le_rfl`. Rewrite `hT` using `[show N + 1 - N = 1 by omega]`. Establish `hsm0 : 0 ≤ PI.succMin M N` using `Real.sInf_nonneg (fun t ht => ht.1)`.

Establish `hdual1 : X.la1 ≤ PI.succMin (PI.dualZ M) 1`. Apply `le_csInf` to reduce the goal to its premises. Establish `hmem : e ⟨a0, mem_IR ha0I⟩ ∈ PI.dualZ M`. Introduce `z hz`. Take `⟨y, hy, hu⟩` from `hz`.

Take `⟨k, hk⟩` from `X.integral y a0 hy (hle ha0I)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[hinner, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, hu.2 a0 (mem_IR ha0I), hk]`. Use `⟨‖e ⟨a0, mem_IR ha0I⟩‖, norm_nonneg _, fun _ => e ⟨a0, mem_IR ha0I⟩, fun _ => hmem, ?_, fun _ => le_rfl⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_unique_iff]`.

Introduce `h0`. Apply `ha0` to reduce the goal to its premises. Use `congrArg e.symm h0` as an intermediate fact. Simplify using `using congrArg Subtype.val this`. Introduce and unpack `t ⟨-, v, hvM, hvli, hvt⟩`.

Establish `hv0` using `hvli.ne_zero 0`. Establish `ha` using `hdual (v 0) (hvM 0)`. Establish `hne : ((e.symm (v 0) : K) : Vsp X.dim) ≠ 0`. Introduce `h0`. Apply `hv0` to reduce the goal to its premises.

Establish `: e.symm (v 0) = 0` using `Subtype.ext h0`. Simplify using `using congrArg e this`. Combine the equalities or inequalities in the displayed calculation. Establish `hlam : PI.succMin M N ≤ N / X.la1`. Rewrite using `[le_div_iff₀ hla]`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty`. Take `⟨s', hs'M, hs'span, hs'li⟩` from `exists_linearIndependent ℝ (M : Set (EuclideanSpace ℝ (Fin N)))`. Establish `hfin' : s'.Finite` using `hs'li.setFinite`. Establish `: Fintype s'` using `hfin'.fintype`.

Set `bs` to `Module.Basis.mk hs'li (by rw [Subtype.range_coe, hs'span, hspan])`. Establish `hcard : Fintype.card s' = N`. Rewrite using `[← Module.finrank_eq_card_basis bs, finrank_euclideanSpace_fin]`. Set `eq : Fin N ≃ s'` to `(Fintype.equivFinOfCardEq hcard).symm`. Use `⟨∑ j, ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖, Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => (eq j : EuclideanSpace ℝ (Fin N)), fun j => hs'M (eq j).2, hs'li.comp eq eq.injective, fun j => ?_⟩` and prove the remaining obligations.

Conclude with `Finset.single_le_sum (f := fun j => ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)`. Take `⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩` from `exists_lt_of_csInf_lt hne (lt_add_of_pos_right (PI.succMin M N) hε)`. Use `choose y hy hyU using hvM`. Use `⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype K.ker_subtype`.

Introduce `j`. Rewrite using `[hnormE]`. Use `hvt j` as an intermediate fact. Establish `h2 : PI.succMin M N = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N), (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}` using `rfl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_short_vectors_realSpan (X : PT E) (I : Submodule ℤ (Vsp X.dim)) (hle : I ≤ X.L)
    (hsat : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) (hla : 0 < X.la1) {ε : ℝ} (hε : 0 < ε) :
    ∃ x u : Fin (Module.finrank ℝ (IR I)) → Vsp X.dim, (∀ j, x j ∈ X.L ∧ IsU I (x j) (u j)) ∧
      LinearIndependent ℝ u ∧ ∀ j, ‖u j‖ ≤ Module.finrank ℝ (IR I) / X.la1 + ε := by
  set K := IR I with hK
  set N := Module.finrank ℝ K with hNdef
  let e : K ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) := (stdOrthonormalBasis ℝ K).repr
  let M : Submodule ℤ (EuclideanSpace ℝ (Fin N)) :=
    { carrier := {z | ∃ y ∈ X.L, IsU I y ((e.symm z : K) : Vsp X.dim)}
      add_mem' := by
        rintro z z' ⟨y, hy, hu⟩ ⟨y', hy', hu'⟩
        exact ⟨y + y', X.L.add_mem hy hy', by simpa using hu.add' hu'⟩
      zero_mem' := ⟨0, X.L.zero_mem, by simpa using IsU.zero' I⟩
      smul_mem' := by
        rintro k z ⟨y, hy, hu⟩
        exact ⟨k • y, X.L.smul_mem k hy, by simpa using hu.zsmul' k⟩ }
  have hmemM : ∀ y ∈ X.L, ∀ u, IsU I y u → ∃ z ∈ M, ((e.symm z : K) : Vsp X.dim) = u :=
    fun y hy u hu => ⟨e ⟨u, hu.1⟩, ⟨y, hy, by simpa using hu⟩, by simp⟩
  have hinner : ∀ z z' : EuclideanSpace ℝ (Fin N),
      ⟪z, z'⟫_ℝ = ⟪((e.symm z : K) : Vsp X.dim), ((e.symm z' : K) : Vsp X.dim)⟫_ℝ := by
    intro z z'
    rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map]
  have hnormE : ∀ z, ‖((e.symm z : K) : Vsp X.dim)‖ = ‖z‖ := by
    intro z
    rw [← e.symm.norm_map z]
    rfl
  have hdual : ∀ z ∈ PI.dualZ M, ((e.symm z : K) : Vsp X.dim) ∈ I := by
    intro z hz
    apply hsat _ ?_ (e.symm z).2
    apply mem_L_of_int X
    intro y hy
    obtain ⟨u, hu⟩ := exists_isU I y
    obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
    obtain ⟨k, hk⟩ := hz z' hz'M
    refine ⟨k, ?_⟩
    rw [← hu.2 _ (e.symm z).2, ← hk, hinner, hz', real_inner_comm]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have : IsEmpty (Fin N) := by rw [hN0]; infer_instance
    exact ⟨fun _ => 0, fun _ => 0, fun j => isEmptyElim j, linearIndependent_empty_type,
      fun j => isEmptyElim j⟩
  obtain ⟨a0, ha0I, ha0⟩ : ∃ a ∈ I, a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hK0 : K = ⊥ := by
      rw [eq_bot_iff, hK]
      exact Submodule.span_le.2 (fun a ha => by simp [hcon a ha])
    have : N = 0 := by rw [hNdef, hK0]; exact finrank_bot ℝ _
    omega
  have hspan : Submodule.span ℝ (M : Set (EuclideanSpace ℝ (Fin N))) = ⊤ := by
    rw [← Submodule.orthogonal_eq_bot_iff, Submodule.eq_bot_iff]
    intro z hz
    have h0 : ∀ z' ∈ M, ⟪z', z⟫_ℝ = 0 := fun z' hz' =>
      (Submodule.mem_orthogonal _ _).1 hz z' (Submodule.subset_span hz')
    have ha : ((e.symm z : K) : Vsp X.dim) = 0 := by
      apply eq_zero_of_im_L X
      intro y hy
      obtain ⟨u, hu⟩ := exists_isU I y
      obtain ⟨z', hz'M, hz'⟩ := hmemM y hy u hu
      rw [← hu.2 _ (e.symm z).2, ← hz', ← hinner]
      exact h0 z' hz'M
    have : e.symm z = 0 := Subtype.ext ha
    simpa using congrArg e this

  obtain ⟨s, hsI, hsspan, hsli⟩ := exists_linearIndependent ℝ (I : Set (Vsp X.dim))
  have hsfin : s.Finite := hsli.setFinite
  set A := ∑ a ∈ hsfin.toFinset, ‖a‖ + 1 with hA
  have hApos : 0 < A := by
    have : 0 ≤ ∑ a ∈ hsfin.toFinset, ‖a‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
    linarith
  have hlow : ∀ z ∈ M, z ≠ 0 → 1 / A ≤ ‖z‖ := by
    intro z hzM hz0
    obtain ⟨y, hy, hu⟩ := hzM
    set u := ((e.symm z : K) : Vsp X.dim)
    have hu0 : u ≠ 0 := by
      intro h0
      apply hz0
      have : e.symm z = 0 := Subtype.ext h0
      simpa using congrArg e this
    obtain ⟨a, has, ha⟩ : ∃ a ∈ s, ⟪u, a⟫_ℝ ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have : ∀ w ∈ Submodule.span ℝ s, ⟪u, w⟫_ℝ = 0 := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem x hx => exact hcon x hx
        | zero => exact inner_zero_right _
        | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
        | smul r x _ hx => rw [real_inner_smul_right, hx, mul_zero]
      have h1 := this u (by rw [hsspan]; exact hu.1)
      exact hu0 (inner_self_eq_zero.1 h1)
    have h1 : 1 ≤ |⟪u, a⟫_ℝ| := by
      rw [hu.2 a (mem_IR (hsI has))]
      rw [hu.2 a (mem_IR (hsI has))] at ha
      exact one_le_abs_im X hy (hle (hsI has)) ha
    have h2 : |⟪u, a⟫_ℝ| ≤ ‖u‖ * ‖a‖ := abs_real_inner_le_norm _ _
    have h3 : ‖a‖ ≤ A := by
      have := Finset.single_le_sum (f := fun a => ‖a‖) (fun _ _ => norm_nonneg _)
        ((Set.Finite.mem_toFinset hsfin).2 has)
      linarith
    rw [← hnormE z, div_le_iff₀ hApos]
    nlinarith [norm_nonneg u]
  have hdisc : DiscreteTopology M := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    refine ⟨1 / A, by positivity, fun z hz => ?_⟩
    by_contra hz0
    have h1 := hlow z z.2 (fun h => hz0 (Subtype.ext h))
    rw [dist_zero_right] at hz
    have : ‖(z : EuclideanSpace ℝ (Fin N))‖ = ‖z‖ := rfl
    linarith
  have hT := transference_successive_minima N M hdisc hspan N hNpos le_rfl
  rw [show N + 1 - N = 1 by omega] at hT
  have hsm0 : 0 ≤ PI.succMin M N := Real.sInf_nonneg (fun t ht => ht.1)
  have hdual1 : X.la1 ≤ PI.succMin (PI.dualZ M) 1 := by
    apply le_csInf
    · have hmem : e ⟨a0, mem_IR ha0I⟩ ∈ PI.dualZ M := by
        intro z hz
        obtain ⟨y, hy, hu⟩ := hz
        obtain ⟨k, hk⟩ := X.integral y a0 hy (hle ha0I)
        refine ⟨k, ?_⟩
        rw [hinner, LinearIsometryEquiv.symm_apply_apply, real_inner_comm, hu.2 a0 (mem_IR ha0I), hk]
      refine ⟨‖e ⟨a0, mem_IR ha0I⟩‖, norm_nonneg _, fun _ => e ⟨a0, mem_IR ha0I⟩,
        fun _ => hmem, ?_, fun _ => le_rfl⟩
      rw [linearIndependent_unique_iff]
      intro h0
      apply ha0
      have := congrArg e.symm h0
      simpa using congrArg Subtype.val this
    · rintro t ⟨-, v, hvM, hvli, hvt⟩
      have hv0 := hvli.ne_zero 0
      have ha := hdual (v 0) (hvM 0)
      have hne : ((e.symm (v 0) : K) : Vsp X.dim) ≠ 0 := by
        intro h0
        apply hv0
        have : e.symm (v 0) = 0 := Subtype.ext h0
        simpa using congrArg e this
      calc X.la1 ≤ ‖((e.symm (v 0) : K) : Vsp X.dim)‖ := sq_le_Qy_of_le_firstMinimum X (hle ha) hne
        _ = ‖v 0‖ := hnormE _
        _ ≤ t := hvt 0
  have hlam : PI.succMin M N ≤ N / X.la1 := by
    rw [le_div_iff₀ hla]
    nlinarith

  have hne : {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t}.Nonempty := by
    obtain ⟨s', hs'M, hs'span, hs'li⟩ := exists_linearIndependent ℝ (M : Set (EuclideanSpace ℝ (Fin N)))
    have hfin' : s'.Finite := hs'li.setFinite
    have : Fintype s' := hfin'.fintype
    let bs := Module.Basis.mk hs'li (by rw [Subtype.range_coe, hs'span, hspan])
    have hcard : Fintype.card s' = N := by
      rw [← Module.finrank_eq_card_basis bs, finrank_euclideanSpace_fin]
    let eq : Fin N ≃ s' := (Fintype.equivFinOfCardEq hcard).symm
    refine ⟨∑ j, ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖,
      Finset.sum_nonneg (fun _ _ => norm_nonneg _), fun j => (eq j : EuclideanSpace ℝ (Fin N)),
      fun j => hs'M (eq j).2, hs'li.comp eq eq.injective, fun j => ?_⟩
    exact Finset.single_le_sum (f := fun j => ‖((eq j : s') : EuclideanSpace ℝ (Fin N))‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  obtain ⟨t, ⟨-, v, hvM, hvli, hvt⟩, htlt⟩ :=
    exists_lt_of_csInf_lt hne (lt_add_of_pos_right (PI.succMin M N) hε)
  choose y hy hyU using hvM
  refine ⟨y, fun j => ((e.symm (v j) : K) : Vsp X.dim), fun j => ⟨hy j, hyU j⟩, ?_, ?_⟩
  · exact (hvli.map' e.symm.toLinearEquiv.toLinearMap (LinearEquiv.ker _)).map' K.subtype
      K.ker_subtype
  · intro j
    rw [hnormE]
    have := hvt j
    have h2 : PI.succMin M N = sInf {t : ℝ | 0 ≤ t ∧ ∃ v : Fin N → EuclideanSpace ℝ (Fin N),
      (∀ j, v j ∈ M) ∧ LinearIndependent ℝ v ∧ ∀ j, ‖v j‖ ≤ t} := rfl
    linarith

end

end ReciprocityTheory.ChartRestriction.G.I2
