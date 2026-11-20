import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.WeightedHomogeneousComponentMemElimIdeal

open MvPolynomial

noncomputable section

namespace GlobalTheory.Chow

attribute [local instance] MvPolynomial.gradedAlgebra

/- English proof (translation)
Consider the cases of `nonempty_fintype n`. Take `⟨b, hb, hspan, hli⟩` from `exists_linearIndependent Ω ((fun v : n → R => φ ∘ v) '' S)`. Set `B : Module.Basis b Ω (n → Ω)` to `Module.Basis.mk hli (by`. Rewrite using `[Subtype.range_coe, hspan, h])`. Set `e : n ≃ b` to `(Pi.basisFun Ω n).indexEquiv B`.

Use `choose v hv hv' using fun k : n => hb (e k).2`. Set `A : Matrix n n R` to `Matrix.of v`. Establish `hA : IsUnit (φ.mapMatrix A)`. Rewrite using `[← Matrix.linearIndependent_rows_iff_isUnit]`. Establish `: (φ.mapMatrix A).row = Subtype.val ∘ e` using `funext fun k => hv' k`.

Rewrite using `[this]`. Conclude with `hli.comp _ e.injective`. Use `⟨A.det, ?_, fun w => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.map_det]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero`.

Establish `: A.det • w = Matrix.vecMul (Matrix.vecMul w A.adjugate) A`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]`. Rewrite using `[this, Matrix.vecMul_eq_sum]`. Conclude with `S.sum_mem fun k _ => S.smul_mem _ (hv k)`.
-/
theorem exists_smul_mem_of_span_eq_top {R Ω n : Type*} [CommRing R] [Field Ω] [Finite n]
    (φ : R →+* Ω) (S : Submodule R (n → R))
    (h : Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S) = ⊤) :
    ∃ r, φ r ≠ 0 ∧ ∀ w, r • w ∈ S := by
  classical
  cases nonempty_fintype n
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent Ω ((fun v : n → R => φ ∘ v) '' S)
  let B : Module.Basis b Ω (n → Ω) := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, h])
  let e : n ≃ b := (Pi.basisFun Ω n).indexEquiv B
  choose v hv hv' using fun k : n => hb (e k).2
  let A : Matrix n n R := Matrix.of v
  have hA : IsUnit (φ.mapMatrix A) := by
    rw [← Matrix.linearIndependent_rows_iff_isUnit]
    have : (φ.mapMatrix A).row = Subtype.val ∘ e := funext fun k => hv' k
    rw [this]
    exact hli.comp _ e.injective
  refine ⟨A.det, ?_, fun w => ?_⟩
  · rw [RingHom.map_det]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 hA).ne_zero
  · have : A.det • w = Matrix.vecMul (Matrix.vecMul w A.adjugate) A := by
      rw [Matrix.vecMul_vecMul, Matrix.adjugate_mul, Matrix.vecMul_smul, Matrix.vecMul_one]
    rw [this, Matrix.vecMul_eq_sum]
    exact S.sum_mem fun k _ => S.smul_mem _ (hv k)

/- English proof (translation)
Consider the cases of `nonempty_fintype σ`. Establish `hrad : ∀ j, ∃ m : ℕ, (X j : MvPolynomial σ Ω) ^ m ∈ I.map (map φ)`. Introduce `j`. Establish `: (X j : MvPolynomial σ Ω) ∈ (I.map (map φ)).radical`. Rewrite using `[← vanishingIdeal_zeroLocus_eq_radical (K := Ω)]`.

Introduce `x hx`. Rewrite using `[h x fun g hg => hx _ (Ideal.mem_map_of_mem _ hg)]`. Simplify using the standard rewrite rules. Conclude with `this`. Use `choose m hm using hrad`.

Set `d` to `∑ j, m j + 1`. Set `n` to `{a : σ →₀ ℕ // a.degree = d}`. Use `haveI : Finite n := (Finsupp.finite_of_degree_eq d).to_subtype`. Use `letI : Fintype n := Fintype.ofFinite n`. Establish `hmon : ∀ a : n, monomial a.1 (1 : Ω) ∈ I.map (map φ)`.

Introduce `a`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, m j ≤ a.1 j := by`. Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `h1 : ∑ j, a.1 j ≤ ∑ j, m j` using `Finset.sum_le_sum fun j _ => (hc j).le`.

Establish `h2` using `a.2`. Rewrite `h2` using `[Finsupp.degree_eq_sum]`. Use linear arithmetic over natural numbers and integers. Establish `hle : Finsupp.single j (m j) ≤ a.1` using `Finsupp.single_le_iff.2 hj`. Take `⟨c, hc⟩` from `exists_add_of_le hle`.

Rewrite using `[hc, ← mul_one (1 : Ω), ← monomial_mul, ← X_pow_eq_monomial]`. Conclude with `Ideal.mul_mem_right _ _ (hm j)`. Set `L : (n → R) →ₗ[R] MvPolynomial σ R` to `∑ a : n, (monomial a.1).comp (LinearMap.proj a)`. Establish `hL (v) : L v = ∑ a : n, monomial a.1 (v a)` using `by simp [L]`. Set `S : Submodule R (n → R)` to `(I.restrictScalars R).comap L`.

Set `π : MvPolynomial σ Ω →ₗ[Ω] (n → Ω)` to `LinearMap.pi fun a => lcoeff Ω a.1`. Set `T` to `Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S)`. Establish `h1 : ∀ g ∈ I, π (map φ g) ∈ T`. Introduce `g hg`. Use `Submodule.subset_span ⟨fun a => coeff a.1 g, ?_, ?_⟩` and prove the remaining obligations.

Establish `: L (fun a => coeff a.1 g) = homogeneousComponent d g`. Use extensionality with `c`. Rewrite using `[hL, coeff_sum, coeff_homogeneousComponent]`. Use `split_ifs with hc`. Rewrite using `[Finset.sum_eq_single (⟨c, hc⟩ : n)]`.

Simplify using the standard rewrite rules. Introduce `a _ ha`. Rewrite using `[coeff_monomial, if_neg fun h => ha (Subtype.ext h)]`. Simplify using the standard rewrite rules. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[coeff_monomial, if_neg fun h : a.1 = c => hc (h ▸ a.2)]`. Express the relevant statement in the definitionally equal form `L _ ∈ I`. Rewrite using `[this]`. Conclude with `homogeneousComponent_mem_of_mem hI hg d`. Use extensionality with `a`.

Simplify using `[π, coeff_map]`. Establish `h2 : ∀ g ∈ I.map (map φ), ∀ c, π (monomial c 1 * g) ∈ T`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, hg, rfl⟩` from `hx`. Introduce `c`. Use `h1 _ (I.mul_mem_left (monomial c 1) hg)` as an intermediate fact. Rewrite `this` using `[map_mul, map_monomial, map_one]`. Then use the resulting hypothesis. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => intro c`. Rewrite using `[mul_add, map_add]`. Conclude with `T.add_mem (hx c) (hy c)`. Consider the case `smul a x _ hx`. Introduce `c`.

Proceed by induction on `a using MvPolynomial.induction_on' with`. Consider the case `monomial u r`. Establish `: monomial c 1 * monomial u r • x = r • (monomial (c + u) 1 * x)`. Rewrite using `[smul_eq_mul, ← mul_assoc, monomial_mul, ← smul_mul_assoc, smul_monomial]`. Simplify using the standard rewrite rules.

Rewrite using `[this, map_smul]`. Conclude with `T.smul_mem _ (hx _)`. Consider the case `add p q hp hq => rw [add_smul, mul_add, map_add]`. Conclude with `T.add_mem hp hq`. Establish `hT : T = ⊤`.

Rewrite using `[eq_top_iff, ← (Pi.basisFun Ω n).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Use `h2 _ (hmon a) 0` as an intermediate fact. Rewrite `this` using `[monomial_zero', C_1, one_mul]`. Establish `h3 : Pi.basisFun Ω n a = π (monomial a.1 1)`.

Use extensionality with `b`. Distinguish the cases in `hab : a = b`. Simplify using `[π, hab]`. Establish `hab' : a.1 ≠ b.1` using `fun h => hab (Subtype.ext h)`. Simplify using `[π, coeff_monomial, hab', Ne.symm hab]`.

Rewrite using `[h3]` and apply the resulting hypothesis. Take `⟨r, hr, hrS⟩` from `exists_smul_mem_of_span_eq_top φ S hT`. Use `⟨r, hr, d, fun j => ?_⟩` and prove the remaining obligations. Set `a : n` to `⟨Finsupp.single j d, by simp⟩`. Establish `: L (r • Pi.single a 1) ∈ I` using `hrS (Pi.single a 1)`.

Rewrite `this` using `[map_smul, hL, Finset.sum_eq_single a]`. Rewrite `this` using `[Pi.single_eq_same, ← X_pow_eq_monomial, smul_eq_C_mul]`. Then use the resulting hypothesis. Introduce `b _ hb`. Simplify using `[hb]`. Simplify using the standard rewrite rules.
-/
theorem exists_C_mul_X_pow_mem {R Ω σ : Type*} [CommRing R] [Field Ω] [IsAlgClosed Ω] [Finite σ]
    (φ : R →+* Ω) {I : Ideal (MvPolynomial σ R)}
    (hI : I.IsHomogeneous (homogeneousSubmodule σ R))
    (h : ∀ x : σ → Ω, (∀ g ∈ I, eval x (map φ g) = 0) → x = 0) :
    ∃ r, φ r ≠ 0 ∧ ∃ m : ℕ, ∀ j, C r * X j ^ m ∈ I := by
  classical
  cases nonempty_fintype σ
  have hrad : ∀ j, ∃ m : ℕ, (X j : MvPolynomial σ Ω) ^ m ∈ I.map (map φ) := by
    intro j
    have : (X j : MvPolynomial σ Ω) ∈ (I.map (map φ)).radical := by
      rw [← vanishingIdeal_zeroLocus_eq_radical (K := Ω)]
      intro x hx
      rw [h x fun g hg => hx _ (Ideal.mem_map_of_mem _ hg)]
      simp
    exact this
  choose m hm using hrad
  let d := ∑ j, m j + 1
  let n := {a : σ →₀ ℕ // a.degree = d}
  haveI : Finite n := (Finsupp.finite_of_degree_eq d).to_subtype
  letI : Fintype n := Fintype.ofFinite n

  have hmon : ∀ a : n, monomial a.1 (1 : Ω) ∈ I.map (map φ) := by
    intro a
    obtain ⟨j, hj⟩ : ∃ j, m j ≤ a.1 j := by
      by_contra hc
      push Not at hc
      have h1 : ∑ j, a.1 j ≤ ∑ j, m j := Finset.sum_le_sum fun j _ => (hc j).le
      have h2 := a.2
      rw [Finsupp.degree_eq_sum] at h2
      omega
    have hle : Finsupp.single j (m j) ≤ a.1 := Finsupp.single_le_iff.2 hj
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    rw [hc, ← mul_one (1 : Ω), ← monomial_mul, ← X_pow_eq_monomial]
    exact Ideal.mul_mem_right _ _ (hm j)
  let L : (n → R) →ₗ[R] MvPolynomial σ R := ∑ a : n, (monomial a.1).comp (LinearMap.proj a)
  have hL (v) : L v = ∑ a : n, monomial a.1 (v a) := by simp [L]
  let S : Submodule R (n → R) := (I.restrictScalars R).comap L
  let π : MvPolynomial σ Ω →ₗ[Ω] (n → Ω) := LinearMap.pi fun a => lcoeff Ω a.1
  let T := Submodule.span Ω ((fun v : n → R => φ ∘ v) '' S)
  have h1 : ∀ g ∈ I, π (map φ g) ∈ T := by
    intro g hg
    refine Submodule.subset_span ⟨fun a => coeff a.1 g, ?_, ?_⟩
    · have : L (fun a => coeff a.1 g) = homogeneousComponent d g := by
        ext c
        rw [hL, coeff_sum, coeff_homogeneousComponent]
        split_ifs with hc
        · rw [Finset.sum_eq_single (⟨c, hc⟩ : n)]
          · simp
          · intro a _ ha
            rw [coeff_monomial, if_neg fun h => ha (Subtype.ext h)]
          · simp
        · refine Finset.sum_eq_zero fun a _ => ?_
          rw [coeff_monomial, if_neg fun h : a.1 = c => hc (h ▸ a.2)]
      change L _ ∈ I
      rw [this]
      exact homogeneousComponent_mem_of_mem hI hg d
    · ext a
      simp [π, coeff_map]
  have h2 : ∀ g ∈ I.map (map φ), ∀ c, π (monomial c 1 * g) ∈ T := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      intro c
      have := h1 _ (I.mul_mem_left (monomial c 1) hg)
      rwa [map_mul, map_monomial, map_one] at this
    | zero => simp
    | add x y _ _ hx hy => intro c; rw [mul_add, map_add]; exact T.add_mem (hx c) (hy c)
    | smul a x _ hx =>
      intro c
      induction a using MvPolynomial.induction_on' with
      | monomial u r =>
        have : monomial c 1 * monomial u r • x = r • (monomial (c + u) 1 * x) := by
          rw [smul_eq_mul, ← mul_assoc, monomial_mul, ← smul_mul_assoc, smul_monomial]
          simp
        rw [this, map_smul]
        exact T.smul_mem _ (hx _)
      | add p q hp hq => rw [add_smul, mul_add, map_add]; exact T.add_mem hp hq
  have hT : T = ⊤ := by
    rw [eq_top_iff, ← (Pi.basisFun Ω n).span_eq, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have := h2 _ (hmon a) 0
    rw [monomial_zero', C_1, one_mul] at this
    have h3 : Pi.basisFun Ω n a = π (monomial a.1 1) := by
      ext b
      by_cases hab : a = b
      · simp [π, hab]
      · have hab' : a.1 ≠ b.1 := fun h => hab (Subtype.ext h)
        simp [π, coeff_monomial, hab', Ne.symm hab]
    rwa [h3]
  obtain ⟨r, hr, hrS⟩ := exists_smul_mem_of_span_eq_top φ S hT
  refine ⟨r, hr, d, fun j => ?_⟩
  let a : n := ⟨Finsupp.single j d, by simp⟩
  have : L (r • Pi.single a 1) ∈ I := hrS (Pi.single a 1)
  rw [map_smul, hL, Finset.sum_eq_single a] at this
  · rwa [Pi.single_eq_same, ← X_pow_eq_monomial, smul_eq_C_mul] at this
  · intro b _ hb
    simp [hb]
  · simp

variable {K : Type*} [CommRing K] {σ β : Type*}

/- English proof (translation)
Rewrite using `[aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `: ∑ j ∈ d.support, d j = n`. Use `hg (mem_support_iff.1 hd)` as an intermediate fact. Rewrite using `[← this, Finsupp.weight_apply, Finsupp.sum]`.

Simplify using the standard rewrite rules. Simplify using `only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_smul_of_isHomogeneous {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {n : ℕ} (hg : g.IsHomogeneous n) (c : G) (ξ : σ → G) :
    aeval (fun j => c * ξ j) g = c ^ n * aeval ξ g := by
  rw [aeval_def, aeval_def, eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have : ∑ j ∈ d.support, d j = n := by
    have := hg (mem_support_iff.1 hd)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, this]
  ring

/- English proof (translation)
Rewrite using `[← sum_homogeneousComponent g, map_sum]`. Conclude with `Finset.sum_eq_zero fun n _ => h n`.
-/
theorem aeval_eq_zero_of_homogeneousComponent {G : Type*} [CommRing G] [Algebra K G]
    {g : MvPolynomial σ K} {ξ : σ → G} (h : ∀ n, aeval ξ (homogeneousComponent n g) = 0) :
    aeval ξ g = 0 := by
  rw [← sum_homogeneousComponent g, map_sum]
  exact Finset.sum_eq_zero fun n _ => h n

/- English proof (translation)
Introduce `g hg` and use `aeval_eq_zero_of_homogeneousComponent fun n => by rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous n g), hξ _ (homogeneousComponent_mem_of_mem hp hg n), mul_zero]`.
-/
theorem aeval_smul_eq_zero {G : Type*} [CommRing G] [Algebra K G]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    {ξ : σ → G} (hξ : ∀ g ∈ p, aeval ξ g = 0) (c : G) :
    ∀ g ∈ p, aeval (fun j => c * ξ j) g = 0 := fun g hg =>
  aeval_eq_zero_of_homogeneousComponent fun n => by
    rw [aeval_smul_of_isHomogeneous (homogeneousComponent_isHomogeneous n g),
      hξ _ (homogeneousComponent_mem_of_mem hp hg n), mul_zero]

/- English proof (translation)
Use `⟨fun h => ?_, fun ⟨x, hx, hp, ht⟩ f hf => aeval_eq_zero_of_mem_elimIdeal hp hx ht hf⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Set `R` to `MvPolynomial (β × σ) K`. Set `φ : R →+* Ω` to `(aeval t : R →ₐ[K] Ω).toRingHom`. Set `L : β → MvPolynomial σ R` to `fun i => ∑ j, C (X (i, j)) * X j`.

Set `I : Ideal (MvPolynomial σ R)` to `Ideal.span ({h | ∃ g ∈ p, ∃ n, map C (homogeneousComponent n g) = h} ∪ Set.range L)`. Establish `hI : I.IsHomogeneous (homogeneousSubmodule σ R)`. Use `Ideal.homogeneous_span _ _ ?_` and prove the remaining obligations. Introduce and unpack `_ (⟨g, -, n, rfl⟩ | ⟨i, rfl⟩)`. Conclude with `⟨n, (homogeneousComponent_isHomogeneous n g).map _⟩`.

Conclude with `⟨1, IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _⟩`. Take `⟨r, hr, m, hm⟩` from `exists_C_mul_X_pow_mem φ hI (by`. Introduce `x hx`. Assume the negation of the conclusion as `hx0`. Use `hc ⟨x, hx0, fun g hg => aeval_eq_zero_of_homogeneousComponent fun n => ?_, fun i => ?_⟩` and prove the remaining obligations.

Use `hx _ (Ideal.subset_span (Or.inl ⟨g, hg, n, rfl⟩))` as an intermediate fact. Establish `hC : φ.comp C = algebraMap K Ω` using `by ext; simp [φ, R]`. Rewrite `this` using `[map_map, hC, eval_map, ← aeval_def]`. Then use the resulting hypothesis. Use `hx _ (Ideal.subset_span (Or.inr ⟨i, rfl⟩))` as an intermediate fact. Simplify `this)` using `[L, φ, R]`.

Use `hr (h r ⟨m, fun j => ?_⟩)` and prove the remaining obligations. Set `s : MvPolynomial σ R →+* MvPolynomial (β × σ) (MvPolynomial σ K)` to `eval₂Hom (map C) fun j => C (X j)`. Apply the tactic sequence `have hs : s.comp (map C) = C := by ext1 <;> [ext1; skip] <;> simp [s, R]`. Establish `hle : I ≤ (incidenceIdeal β p).comap s`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ (⟨g, hg, n, rfl⟩ | ⟨i, rfl⟩)`. Rewrite using `[SetLike.mem_coe, Ideal.mem_comap, ← RingHom.comp_apply, hs]`. Conclude with `C_mem_incidenceIdeal (homogeneousComponent_mem_of_mem hp hg n)`. Use `genericForm_mem_incidenceIdeal p i` as an intermediate fact. Rewrite `this` using `[genericForm_eq]`.

Simplify `this` using `[s, L, R, mul_comm]`. Use `hle (hm j)` as an intermediate fact. Simplify `this` using `[s, Ideal.mem_comap]`.
-/
theorem forall_aeval_eq_zero_iff [Fintype σ] {Ω : Type*} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    {p : Ideal (MvPolynomial σ K)} (hp : p.IsHomogeneous (homogeneousSubmodule σ K))
    (t : β × σ → Ω) :
    (∀ f ∈ elimIdeal β p, aeval t f = 0) ↔
      ∃ x : σ → Ω, x ≠ 0 ∧ (∀ g ∈ p, aeval x g = 0) ∧ ∀ i, ∑ j, t (i, j) * x j = 0 := by
  refine ⟨fun h => ?_, fun ⟨x, hx, hp, ht⟩ f hf => aeval_eq_zero_of_mem_elimIdeal hp hx ht hf⟩
  by_contra hc
  let R := MvPolynomial (β × σ) K
  let φ : R →+* Ω := (aeval t : R →ₐ[K] Ω).toRingHom
  let L : β → MvPolynomial σ R := fun i => ∑ j, C (X (i, j)) * X j
  let I : Ideal (MvPolynomial σ R) := Ideal.span
    ({h | ∃ g ∈ p, ∃ n, map C (homogeneousComponent n g) = h} ∪ Set.range L)
  have hI : I.IsHomogeneous (homogeneousSubmodule σ R) := by
    refine Ideal.homogeneous_span _ _ ?_
    rintro _ (⟨g, -, n, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨n, (homogeneousComponent_isHomogeneous n g).map _⟩
    · exact ⟨1, IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X _ _⟩
  obtain ⟨r, hr, m, hm⟩ := exists_C_mul_X_pow_mem φ hI (by
    intro x hx
    by_contra hx0
    refine hc ⟨x, hx0, fun g hg => aeval_eq_zero_of_homogeneousComponent fun n => ?_, fun i => ?_⟩
    · have := hx _ (Ideal.subset_span (Or.inl ⟨g, hg, n, rfl⟩))
      have hC : φ.comp C = algebraMap K Ω := by ext; simp [φ, R]
      rwa [map_map, hC, eval_map, ← aeval_def] at this
    · have := hx _ (Ideal.subset_span (Or.inr ⟨i, rfl⟩))
      simpa [L, φ, R] using this)
  refine hr (h r ⟨m, fun j => ?_⟩)
  let s : MvPolynomial σ R →+* MvPolynomial (β × σ) (MvPolynomial σ K) :=
    eval₂Hom (map C) fun j => C (X j)
  have hs : s.comp (map C) = C := by
    ext1 <;> [ext1; skip] <;> simp [s, R]
  have hle : I ≤ (incidenceIdeal β p).comap s := by
    rw [Ideal.span_le]
    rintro _ (⟨g, hg, n, rfl⟩ | ⟨i, rfl⟩)
    · rw [SetLike.mem_coe, Ideal.mem_comap, ← RingHom.comp_apply, hs]
      exact C_mem_incidenceIdeal (homogeneousComponent_mem_of_mem hp hg n)
    · have := genericForm_mem_incidenceIdeal p i
      rw [genericForm_eq] at this
      simpa [s, L, R, mul_comm] using this
  have := hle (hm j)
  simpa [s, Ideal.mem_comap] using this

end GlobalTheory.Chow
