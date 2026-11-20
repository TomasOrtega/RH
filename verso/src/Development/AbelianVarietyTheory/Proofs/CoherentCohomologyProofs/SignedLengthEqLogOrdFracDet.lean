import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective

universe u_1 u_2 u_3 u_4

namespace GlobalTheory.SignedLengthLogDet

open Module

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi, Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]`.
-/
theorem ord_finprod {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} (s : Finset ι)
    (c : ι → R) (hc : ∀ i, c i ≠ 0) :
    Ring.ord R (∏ i ∈ s, c i) = ∑ i ∈ s, Ring.ord R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' R (mem_nonZeroDivisors_of_ne_zero (hc i)), ih]

/- English proof (translation)
Use `set N := LinearMap.range φ with hN`. Set `e : M ≃ₗ[R] N` to `LinearEquiv.ofInjective φ hφ`. Establish `hrk : finrank R N = finrank R M` using `e.symm.finrank_eq`. Set `c` to `Submodule.smithNormalFormCoeffs b hrk`. Set `t` to `Submodule.smithNormalFormTopBasis b hrk`.

Set `s` to `Submodule.smithNormalFormBotBasis b hrk`. Establish `hs : ∀ i, (s i : M) = c i • t i` using `Submodule.smithNormalFormBotBasis_def b hrk`. Establish `hc : ∀ i, c i ≠ 0` using `Submodule.smithNormalFormCoeffs_ne_zero b hrk`. Set `e' : M ≃ₗ[R] N` to `t.equiv s (Equiv.refl _)`. Establish `h1 : Associated (LinearMap.det φ) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)))`.

Establish `: φ = N.subtype ∘ₗ (e : M →ₗ[R] N)` using `by ext x; rfl`. Use `conv_lhs => rw [this]`. Conclude with `LinearMap.associated_det_comp_equiv _ _ _`. Establish `h2 : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, c i`. Rewrite using `[← LinearMap.det_toMatrix t, ← Matrix.det_diagonal]`.

Use `congr 1`. Use extensionality with `i j`. Establish `: (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j`. Simplify using `[e', hs]`. Rewrite using `[LinearMap.toMatrix_apply, this, Matrix.diagonal_apply]`.

Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Finsupp.single_apply, Ne.symm h]`. Rewrite using `[Ring.ord_eq_of_associated h1, h2, ord_finprod _ _ hc, (Submodule.quotientEquivPiSpan N b hrk).length_eq, Module.length_pi_of_fintype]`.

Both sides reduce to the same expression.
-/
theorem length_coker {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {M : Type*} [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (b : Basis ι R M)
    (φ : M →ₗ[R] M) (hφ : Function.Injective φ) :
    Module.length R (M ⧸ LinearMap.range φ) = Ring.ord R (LinearMap.det φ) := by
  classical
  set N := LinearMap.range φ with hN
  let e : M ≃ₗ[R] N := LinearEquiv.ofInjective φ hφ
  have hrk : finrank R N = finrank R M := e.symm.finrank_eq
  let c := Submodule.smithNormalFormCoeffs b hrk
  let t := Submodule.smithNormalFormTopBasis b hrk
  let s := Submodule.smithNormalFormBotBasis b hrk
  have hs : ∀ i, (s i : M) = c i • t i := Submodule.smithNormalFormBotBasis_def b hrk
  have hc : ∀ i, c i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b hrk
  let e' : M ≃ₗ[R] N := t.equiv s (Equiv.refl _)
  have h1 : Associated (LinearMap.det φ) (LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N))) := by
    have : φ = N.subtype ∘ₗ (e : M →ₗ[R] N) := by ext x; rfl
    conv_lhs => rw [this]
    exact LinearMap.associated_det_comp_equiv _ _ _
  have h2 : LinearMap.det (N.subtype ∘ₗ (e' : M →ₗ[R] N)) = ∏ i, c i := by
    rw [← LinearMap.det_toMatrix t, ← Matrix.det_diagonal]
    congr 1
    ext i j
    have : (N.subtype ∘ₗ (e' : M →ₗ[R] N)) (t j) = c j • t j := by
      simp [e', hs]
    rw [LinearMap.toMatrix_apply, this, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h]
  rw [Ring.ord_eq_of_associated h1, h2, ord_finprod _ _ hc,
    (Submodule.quotientEquivPiSpan N b hrk).length_eq, Module.length_pi_of_fintype]
  rfl

/- English proof (translation)
Establish `hle : C.submoduleOf A ≤ D.submoduleOf A` using `Submodule.comap_mono hCD`. Establish `hf : C.submoduleOf D ≤ (C.submoduleOf A).comap (Submodule.inclusion hDA)` using `fun x hx => hx`. Use `Module.length_eq_add_of_exact (Submodule.mapQ (C.submoduleOf D) (C.submoduleOf A) (Submodule.inclusion hDA) hf) (Submodule.factor hle) ?_ (Submodule.factor_surjective hle) ?_` as an intermediate fact. Rewrite using `[relLength_def, this, add_comm]`. Both sides reduce to the same expression.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite `hx` using `[Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`.

Conclude with `hx`. Introduce `y`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ y`. Prove the components needed by the constructor for the conclusion. Introduce `hy`.

Establish `hy' : (Submodule.Quotient.mk y : A ⧸ D.submoduleOf A) = 0` using `hy`. Rewrite `hy'` using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨Submodule.Quotient.mk ⟨y, hy'⟩, rfl⟩`. Introduce and unpack `⟨x, hx⟩`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Rewrite using `[← hx]`. Express the relevant statement in the definitionally equal form `(Submodule.Quotient.mk (Submodule.inclusion hDA x) : A ⧸ D.submoduleOf A) = 0`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `x.2`.
-/
theorem relLength_chain {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
    {A D C : Submodule R V} (hCD : C ≤ D) (hDA : D ≤ A) :
    relLength A C = relLength A D + relLength D C := by
  have hle : C.submoduleOf A ≤ D.submoduleOf A := Submodule.comap_mono hCD
  have hf : C.submoduleOf D ≤ (C.submoduleOf A).comap (Submodule.inclusion hDA) :=
    fun x hx => hx
  have := Module.length_eq_add_of_exact
    (Submodule.mapQ (C.submoduleOf D) (C.submoduleOf A) (Submodule.inclusion hDA) hf)
    (Submodule.factor hle) ?_ (Submodule.factor_surjective hle) ?_
  · rw [relLength_def, this, add_comm]; rfl
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact hx
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have hy' : (Submodule.Quotient.mk y : A ⧸ D.submoduleOf A) = 0 := hy
      rw [Submodule.Quotient.mk_eq_zero] at hy'
      exact ⟨Submodule.Quotient.mk ⟨y, hy'⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      change (Submodule.Quotient.mk (Submodule.inclusion hDA x) : A ⧸ D.submoduleOf A) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact x.2

/- English proof (translation)
Set `φ : A →ₗ[R] A` to `Matrix.toLin a a h`. Establish `hφ : ∀ j, (φ (a j) : V) = v j`. Introduce `j`. Rewrite using `[hv j]`. Simplify using `[φ, Matrix.toLin_self]`.

Establish `hdet : LinearMap.det φ = h.det` using `LinearMap.det_toLin a h`. Establish `hinj : Function.Injective φ`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Establish `h0 : h.mulVec (a.repr x) = 0`.

Rewrite using `[← Matrix.repr_toLin a a h x]`. Express the relevant statement in the definitionally equal form `⇑(a.repr (φ x)) = 0`. Rewrite using `[hx]`. Simplify using the standard rewrite rules. Use `Matrix.eq_zero_of_mulVec_eq_zero hh h0` as an intermediate fact.

Apply `a.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Simplify using `using congrFun this i`. Establish `hmap : (LinearMap.range φ).map A.subtype = Submodule.span R (Set.range v)`. Rewrite using `[← Submodule.map_top, ← a.span_eq, Submodule.map_span, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]`.

Use `congr 2`. Use function extensionality and compare the values at `j`. Conclude with `hφ j`. Use `⟨hmap ▸ Submodule.map_subtype_le _ _, ?_⟩` and prove the remaining obligations. Establish `hsub : (Submodule.span R (Set.range v)).submoduleOf A = LinearMap.range φ`.

Rewrite using `[← hmap]`. Conclude with `Submodule.comap_map_eq_of_injective A.injective_subtype _`. Rewrite using `[relLength_def, hsub, length_coker a φ hinj, hdet]`.
-/
theorem relLength_span_columns {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {V : Type*} [AddCommGroup V] [Module R V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Submodule R V} (a : Basis ι R A) (h : Matrix ι ι R) (hh : h.det ≠ 0) (v : ι → V)
    (hv : ∀ j, v j = ∑ i, h i j • (a i : V)) :
    Submodule.span R (Set.range v) ≤ A ∧
      relLength A (Submodule.span R (Set.range v)) = Ring.ord R h.det := by
  let φ : A →ₗ[R] A := Matrix.toLin a a h
  have hφ : ∀ j, (φ (a j) : V) = v j := by
    intro j
    rw [hv j]
    simp [φ, Matrix.toLin_self]
  have hdet : LinearMap.det φ = h.det := LinearMap.det_toLin a h
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    have h0 : h.mulVec (a.repr x) = 0 := by
      rw [← Matrix.repr_toLin a a h x]
      change ⇑(a.repr (φ x)) = 0
      rw [hx]
      simp
    have := Matrix.eq_zero_of_mulVec_eq_zero hh h0
    apply a.repr.injective
    ext i
    simpa using congrFun this i
  have hmap : (LinearMap.range φ).map A.subtype = Submodule.span R (Set.range v) := by
    rw [← Submodule.map_top, ← a.span_eq, Submodule.map_span, Submodule.map_span,
      ← Set.range_comp, ← Set.range_comp]
    congr 2
    funext j
    exact hφ j
  refine ⟨hmap ▸ Submodule.map_subtype_le _ _, ?_⟩
  have hsub : (Submodule.span R (Set.range v)).submoduleOf A = LinearMap.range φ := by
    rw [← hmap]
    exact Submodule.comap_map_eq_of_injective A.injective_subtype _
  rw [relLength_def, hsub, length_coker a φ hinj, hdet]

/- English proof (translation)
Rewrite using `[Ring.ordFrac_eq_ord R hx, Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hx) hn]`. Both sides reduce to the same expression.
-/
theorem ordFrac_algebraMap_eq_exp {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] {x : R} (hx : x ≠ 0) {n : ℕ}
    (hn : Ring.ord R x = n) :
    Ring.ordFrac R (algebraMap R K x) = WithZero.exp (n : ℤ) := by
  rw [Ring.ordFrac_eq_ord R hx,
    Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hx) hn]
  rfl

/- English proof (translation)
Take `⟨⟨d, hd⟩, hint⟩` from `IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun p : ι × ι => g p.1 p.2)`. Establish `hd0 : d ≠ 0` using `nonZeroDivisors.ne_zero hd`. Use `choose h' hh' using hint`. Set `h : Matrix ι ι R` to `Matrix.of fun i j => h' (i, j)`. Establish `hh : ∀ i j, algebraMap R K (h i j) = algebraMap R K d * g i j`.

Introduce `i j`. Rewrite using `[← Algebra.smul_def]`. Conclude with `hh' (i, j)`. Set `δ : Matrix ι ι R` to `Matrix.diagonal fun _ => d`. Establish `hδ : δ.det ≠ 0`.

Rewrite using `[Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => hd0`. Establish `hinj` using `FaithfulSMul.algebraMap_injective R K`. Establish `hdet : algebraMap R K h.det = algebraMap R K δ.det * g.det`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]`.

Use `congr 1`. Use extensionality with `i j`. Simplify using `[δ, hh, Matrix.diagonal_map, Matrix.diagonal_mul]`. Establish `hh0 : h.det ≠ 0`. Introduce `h0`.

Rewrite `hdet` using `[h0, map_zero]`. Conclude with `mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hδ) hg hdet.symm`. Set `v : ι → V` to `fun j => d • (b j : V)`. Take `⟨hCA, hA⟩` from `relLength_span_columns a h hh0 v (fun j => by`. Simplify using `only [v, hb, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_smul K (h i j), hh, mul_smul, algebraMap_smul])`. Take `⟨hCB, hB⟩` from `relLength_span_columns b δ hδ v (fun j => by`. Simplify using `[v, δ, Matrix.diagonal_apply, ite_smul])`. Use `set C := Submodule.span R (Set.range v)`.

Take `⟨m, hm⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hh0))`. Take `⟨n, hn⟩` from `ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hδ))`. Establish `hC : C ≤ A ⊓ B` using `le_inf hCA hCB`. Rewrite `hA` using `[relLength_chain hC inf_le_left, relLength_inf_right, ← hm]`. Rewrite `hB` using `[relLength_chain hC inf_le_right, relLength_inf_right', ← hn]`.

Establish `hlog : WithZero.log (Ring.ordFrac R g.det) = (m : ℤ) - n`. Use `congrArg (Ring.ordFrac R) hdet` as an intermediate fact. Rewrite `this` using `[map_mul, ordFrac_algebraMap_eq_exp hh0 hm.symm, ordFrac_algebraMap_eq_exp hδ hn.symm]`. Establish `h2 : Ring.ordFrac R g.det = WithZero.exp ((m : ℤ) - n)`. Rewrite using `[WithZero.exp_sub, this, mul_div_cancel_left₀ _ WithZero.exp_ne_zero]`.

Rewrite using `[h2, WithZero.log_exp]`. Rewrite using `[hlog]`. Unfold `LengthCommensurable signedLength`. Generalize the expression as in `relLength A B = x at *`. Generalize the expression as in `relLength B A = y at *`.

Generalize the expression as in `relLength (A ⊓ B) C = z at *`. Proceed by induction on `z using ENat.recTopCoe with`. Consider the case `top => simp at hA`. Consider the case `coe z`. Proceed by induction on `x using ENat.recTopCoe with`.

Consider the case `top => simp at hA`. Consider the case `coe x`. Proceed by induction on `y using ENat.recTopCoe with`. Consider the case `top => simp at hB`. Consider the case `coe y`.

Normalize the coercions in `at hA hB`. Use `⟨⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [ENat.toNat_coe]`. Use linear arithmetic over natural numbers and integers.
-/
theorem signedLength_eq_log_ordFrac_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {K : Type u_2} [Field K] [Algebra R K] [IsFractionRing R K]
    {V : Type u_3} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    {ι : Type u_4} [Fintype ι] [DecidableEq ι] {A B : Submodule R V}
    (a : Module.Basis ι R A) (b : Module.Basis ι R B) (g : Matrix ι ι K) (hg : g.det ≠ 0)
    (hb : ∀ j, (b j : V) = ∑ i, g i j • (a i : V)) :
    LengthCommensurable A B ∧
      signedLength A B = WithZero.log (Ring.ordFrac R g.det) := by
  obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors R) (fun p : ι × ι => g p.1 p.2)
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  choose h' hh' using hint
  let h : Matrix ι ι R := Matrix.of fun i j => h' (i, j)
  have hh : ∀ i j, algebraMap R K (h i j) = algebraMap R K d * g i j := by
    intro i j
    rw [← Algebra.smul_def]
    exact hh' (i, j)
  let δ : Matrix ι ι R := Matrix.diagonal fun _ => d
  have hδ : δ.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => hd0
  have hinj := FaithfulSMul.algebraMap_injective R K
  have hdet : algebraMap R K h.det = algebraMap R K δ.det * g.det := by
    rw [RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
    congr 1
    ext i j
    simp [δ, hh, Matrix.diagonal_map, Matrix.diagonal_mul]
  have hh0 : h.det ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hdet
    exact mul_ne_zero ((map_ne_zero_iff _ hinj).mpr hδ) hg hdet.symm
  let v : ι → V := fun j => d • (b j : V)
  obtain ⟨hCA, hA⟩ := relLength_span_columns a h hh0 v (fun j => by
    simp only [v, hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← algebraMap_smul K (h i j), hh, mul_smul, algebraMap_smul])
  obtain ⟨hCB, hB⟩ := relLength_span_columns b δ hδ v (fun j => by
    simp [v, δ, Matrix.diagonal_apply, ite_smul])
  set C := Submodule.span R (Set.range v)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hh0))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hδ))
  have hC : C ≤ A ⊓ B := le_inf hCA hCB
  rw [relLength_chain hC inf_le_left, relLength_inf_right, ← hm] at hA
  rw [relLength_chain hC inf_le_right, relLength_inf_right', ← hn] at hB
  have hlog : WithZero.log (Ring.ordFrac R g.det) = (m : ℤ) - n := by
    have := congrArg (Ring.ordFrac R) hdet
    rw [map_mul, ordFrac_algebraMap_eq_exp hh0 hm.symm, ordFrac_algebraMap_eq_exp hδ hn.symm] at this
    have h2 : Ring.ordFrac R g.det = WithZero.exp ((m : ℤ) - n) := by
      rw [WithZero.exp_sub, this, mul_div_cancel_left₀ _ WithZero.exp_ne_zero]
    rw [h2, WithZero.log_exp]
  rw [hlog]
  unfold LengthCommensurable signedLength
  generalize relLength A B = x at *
  generalize relLength B A = y at *
  generalize relLength (A ⊓ B) C = z at *
  induction z using ENat.recTopCoe with
  | top => simp at hA
  | coe z =>
    induction x using ENat.recTopCoe with
    | top => simp at hA
    | coe x =>
      induction y using ENat.recTopCoe with
      | top => simp at hB
      | coe y =>
        norm_cast at hA hB
        refine ⟨⟨ENat.coe_ne_top _, ENat.coe_ne_top _⟩, ?_⟩
        simp only [ENat.toNat_coe]
        omega

end GlobalTheory.SignedLengthLogDet
