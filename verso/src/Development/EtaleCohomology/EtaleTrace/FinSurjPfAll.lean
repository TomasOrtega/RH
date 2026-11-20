import Development.EtaleCohomology.EtaleTrace.FinSurjPfDense

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Rewrite using `[eval₂_eq', eval₂_eq', Finset.sum_mul]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hdeg : ∑ j, d j = 1`. Use `hg (mem_support_iff.mp hd)` as an intermediate fact. Rewrite using `[← this]`.

Simplify using `[Finsupp.weight_apply, Finsupp.sum_fintype]`. Repeatedly rewrite using `[mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, pow_one, mul_assoc]`.
-/
theorem eval₂_scale_one {k K : Type} [Field k] [Field K] {n : ℕ} (f : k →+* K) (u : Fin n → K) (t : K)
    (g : MvPolynomial (Fin n) k) (hg : g.IsHomogeneous 1) :
    eval₂ f (fun j => u j * t) g = eval₂ f u g * t := by
  rw [eval₂_eq', eval₂_eq', Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ j, d j = 1 := by
    have := hg (mem_support_iff.mp hd)
    rw [← this]; simp [Finsupp.weight_apply, Finsupp.sum_fintype]
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg, pow_one, mul_assoc]

/- English proof (translation)
Proceed by induction on `g using MvPolynomial.induction_on with`. Consider the case `C a => simpa using hf a`. Consider the case `add a b ha hb => rw [eval₂_add]`. Conclude with `S.add_mem ha hb`. Consider the case `mul_X a j ha => rw [eval₂_mul, eval₂_X]`.

Conclude with `S.mul_mem ha (hu j)`.
-/
theorem eval₂_mem_subring {k K : Type} [Field k] [Field K] {n : ℕ} (f : k →+* K) (S : Subring K)
    (hf : ∀ c, f c ∈ S) (u : Fin n → K) (hu : ∀ j, u j ∈ S) (g : MvPolynomial (Fin n) k) : eval₂ f u g ∈ S := by
  induction g using MvPolynomial.induction_on with
  | C a => simpa using hf a
  | add a b ha hb => rw [eval₂_add]; exact S.add_mem ha hb
  | mul_X a j ha => rw [eval₂_mul, eval₂_X]; exact S.mul_mem ha (hu j)

/- English proof (translation)
Rewrite using `[div_eq_mul_inv, ← eval₂_scale_one _ _ _ _ hg]`. Conclude with `eval₂_mem_subring _ _ (kHom_mem_loc p x) _ (fun j => by simpa [div_eq_mul_inv] using hu j) g`.
-/
theorem eval_linear_form_div_mem_local_ring_of_coordinates_div_mem {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (x : X) {n : ℕ}
    (u : Fin n → X.functionField) (t : X.functionField) (hu : ∀ j, u j / t ∈ loc X x)
    (g : MvPolynomial (Fin n) k) (hg : g.IsHomogeneous 1) : eval₂ (kHom p) u g / t ∈ loc X x := by
  rw [div_eq_mul_inv, ← eval₂_scale_one _ _ _ _ hg]
  exact eval₂_mem_subring _ _ (kHom_mem_loc p x) _ (fun j => by simpa [div_eq_mul_inv] using hu j) g

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Use `⟨∑ j, C (c j) * X j, ?_, by simp [eval₂_sum]⟩` and prove the remaining obligations. Conclude with `IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _`.
-/
theorem linForm {k : Type} [Field k] {K : Type} [Field K] (f : k →+* K) {N : ℕ} (v : Fin (N + 1) → K) (z : K)
    (h : ∃ c : Fin (N + 1) → k, z = ∑ j, f (c j) * v j) :
    ∃ L : MvPolynomial (Fin (N + 1)) k, L.IsHomogeneous 1 ∧ eval₂ f v L = z := by
  obtain ⟨c, rfl⟩ := h
  refine ⟨∑ j, C (c j) * X j, ?_, by simp [eval₂_sum]⟩
  exact IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _

/- English proof (translation)
Establish `htop` using `Proj.iSup_basicOpen_eq_top (homogeneousSubmodule (Fin (d + 1)) k) (fun i : Fin (d + 1) => (X i : MvPolynomial (Fin (d + 1)) k)) ?_`. Establish `: y ∈ (⊤ : (PN k d).Opens)` using `trivial`. Rewrite `this` using `[← htop]`. Conclude with `TopologicalSpace.Opens.mem_iSup.mp this`. Introduce `q hq`.

Rewrite using `[← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]`. Introduce `m hm`. Use `by_contra! hne`. Establish `hm0 : m = 0` using `Finsupp.ext fun i => hne i (Set.mem_univ i)`. Substitute `hm0` using the available equality.

Establish `h0 : GradedRing.proj (homogeneousSubmodule (Fin (d + 1)) k) 0 q = 0` using `hq`. Rewrite `h0` using `[GradedRing.proj_apply]`. Express the relevant statement in the definitionally equal form `((MvPolynomial.decomposition.decompose' q 0 : homogeneousSubmodule (Fin (d + 1)) k 0) : MvPolynomial (Fin (d + 1)) k) = 0 at h0`. Rewrite `h0` using `[MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero]`. Conclude with `(mem_support_iff.mp hm) h0`.
-/
theorem PN_cover (k : Type) [Field k] (d : ℕ) (y : PN k d) :
    ∃ i : Fin (d + 1), y ∈ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (X i) := by
  have htop := Proj.iSup_basicOpen_eq_top (homogeneousSubmodule (Fin (d + 1)) k)
    (fun i : Fin (d + 1) => (X i : MvPolynomial (Fin (d + 1)) k)) ?_
  · have : y ∈ (⊤ : (PN k d).Opens) := trivial
    rw [← htop] at this
    exact TopologicalSpace.Opens.mem_iSup.mp this
  intro q hq
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  by_contra! hne
  have hm0 : m = 0 := Finsupp.ext fun i => hne i (Set.mem_univ i)
  subst hm0
  have h0 : GradedRing.proj (homogeneousSubmodule (Fin (d + 1)) k) 0 q = 0 := hq
  rw [GradedRing.proj_apply] at h0
  change ((MvPolynomial.decomposition.decompose' q 0 : homogeneousSubmodule (Fin (d + 1)) k 0) :
    MvPolynomial (Fin (d + 1)) k) = 0 at h0
  rw [MvPolynomial.decomposition.decompose'_apply, homogeneousComponent_zero, C_eq_zero] at h0
  exact (mem_support_iff.mp hm) h0

/- English proof (translation)
Introduce `k _ X _ p N d ι π v w hι cv cw hlin hx`. Establish `: IsAffineHom ι` using `inferInstance`. Apply `isAffineHom_of_forall_exists_isAffineOpen` to reduce the goal to its premises. Introduce `y`. Take `⟨i, hi⟩` from `PN_cover k d y`.

Take `⟨L, hL, evL⟩` from `linForm (kHom p) v (w i) (hlin i)`. Establish `hXi : (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) k).IsHomogeneous 1` using `isHomogeneous_X _ _`. Establish `heq : π ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (MvPolynomial.X i) = ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) L`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ π ⁻¹ᵁ _ ↔ x ∈ ι ⁻¹ᵁ _`.

Rewrite using `[cw.opens 1 one_pos _ hXi x, cv.opens 1 one_pos L hL x, eval₂_X, evL]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hne, H⟩`. Use `⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x v (w i) (fun j => ?_) g hg⟩` and prove the remaining obligations. Take `⟨i', hi', hv'⟩` from `hx x`.

Establish `h1 : w i' / w i ∈ loc X x` using `by simpa using H (MvPolynomial.X i') (isHomogeneous_X _ _)`. Establish `: v j / w i = v j / w i' * (w i' / w i)` using `by field_simp`. Rewrite using `[this]`. Conclude with `(loc X x).mul_mem (hv' j) h1`. Introduce and unpack `⟨hne, H⟩`.

Use `⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x w (w i) (fun l => ?_) g hg⟩` and prove the remaining obligations. Take `⟨L', hL', evL'⟩` from `linForm (kHom p) v (w l) (hlin l)`. Rewrite using `[← evL']`. Conclude with `H L' hL'`. Use `⟨_, hi, Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hXi) one_pos, ?_⟩` and prove the remaining obligations.

Rewrite using `[heq]`. Conclude with `(Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hL) one_pos).preimage ι`.
-/
theorem FSAffine_pf : FSAffine := by
  intro k _ X _ p N d ι π v w hι cv cw hlin hx
  have : IsAffineHom ι := inferInstance
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  obtain ⟨i, hi⟩ := PN_cover k d y
  obtain ⟨L, hL, evL⟩ := linForm (kHom p) v (w i) (hlin i)
  have hXi : (MvPolynomial.X i : MvPolynomial (Fin (d + 1)) k).IsHomogeneous 1 := isHomogeneous_X _ _
  have heq : π ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (d + 1)) k) (MvPolynomial.X i) =
      ι ⁻¹ᵁ Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) L := by
    ext x
    change x ∈ π ⁻¹ᵁ _ ↔ x ∈ ι ⁻¹ᵁ _
    rw [cw.opens 1 one_pos _ hXi x, cv.opens 1 one_pos L hL x, eval₂_X, evL]
    constructor
    · rintro ⟨hne, H⟩
      refine ⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x v (w i) (fun j => ?_) g hg⟩
      obtain ⟨i', hi', hv'⟩ := hx x
      have h1 : w i' / w i ∈ loc X x := by simpa using H (MvPolynomial.X i') (isHomogeneous_X _ _)
      have : v j / w i = v j / w i' * (w i' / w i) := by field_simp
      rw [this]; exact (loc X x).mul_mem (hv' j) h1
    · rintro ⟨hne, H⟩
      refine ⟨hne, fun g hg => eval_linear_form_div_mem_local_ring_of_coordinates_div_mem p x w (w i) (fun l => ?_) g hg⟩
      obtain ⟨L', hL', evL'⟩ := linForm (kHom p) v (w l) (hlin l)
      rw [← evL']; exact H L' hL'
  refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hXi) one_pos, ?_⟩
  rw [heq]
  exact (Proj.isAffineOpen_basicOpen _ _ ((mem_homogeneousSubmodule 1 _).mpr hL) one_pos).preimage ι

/- English proof (translation)
The claim follows from `FinSurj_of h1 FSAffine_pf FSDense_pf`.
-/
theorem FinSurj_of_full (h1 : PNBasic) : FinSurj := FinSurj_of h1 FSAffine_pf FSDense_pf
